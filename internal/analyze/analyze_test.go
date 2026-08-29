package analyze

// This file tests template parsing, control flow, function rules, template
// calls, value origins, and diagnostics.

import (
	"strings"
	"testing"
)

func TestUsageMergeIsMonotonic(t *testing.T) {
	left := NewUsage()
	left.Properties["image"] = &Usage{
		Read:       true,
		Properties: map[string]*Usage{"repository": {Read: true}},
	}
	right := NewUsage()
	right.Open = true
	right.Iterated = true
	right.Properties["image"] = &Usage{
		Exact:        true,
		AllowUnknown: true,
		Open:         true,
		Properties:   map[string]*Usage{"tag": {Read: true, Open: true}},
		Additional:   &Usage{Read: true},
		Items:        &Usage{Open: true},
		Elements:     &Usage{Read: true},
	}

	left.Merge(right)

	if !left.Open || !left.Iterated {
		t.Fatalf("root flags = Open %v, Iterated %v", left.Open, left.Iterated)
	}
	image := requireProperty(t, left, "image")
	if !image.Read || !image.Exact || !image.AllowUnknown || !image.Open {
		t.Fatalf("image flags = %#v", image)
	}
	requireProperty(t, image, "repository")
	tag := requireProperty(t, image, "tag")
	if !tag.Read || !tag.Open {
		t.Fatalf("tag flags = Read %v, Open %v", tag.Read, tag.Open)
	}
	if image.Additional == nil || !image.Additional.Read {
		t.Fatal("Additional usage was not merged")
	}
	if image.Items == nil || !image.Items.Open {
		t.Fatal("Items usage was not merged")
	}
	if image.Elements == nil || !image.Elements.Read {
		t.Fatal("Elements usage was not merged")
	}

	left.Merge(NewUsage())
	if !tag.Read || !tag.Open {
		t.Fatal("merging empty usage removed evidence")
	}
}

func TestContextObservationRespectsValuesRoots(t *testing.T) {
	t.Run("unrestricted context includes roots", func(t *testing.T) {
		a := analyzer{usage: NewUsage()}

		a.observe(referenceValue(referenceForScope()), contextValue)

		if !a.usage.AllowUnknown {
			t.Fatal("unrestricted context observation did not open the values root")
		}
	})

	t.Run("selected values below roots", func(t *testing.T) {
		root := referenceForScope()
		dependency := referenceForScope("child")
		context := objectValue(map[string]value{
			"root":               referenceValue(root),
			"rootSettings":       referenceValue(root.append(segment{kind: propertySegment, name: "settings"})),
			"dependency":         referenceValue(dependency),
			"dependencySettings": referenceValue(dependency.append(segment{kind: propertySegment, name: "settings"})),
		})
		a := analyzer{usage: NewUsage()}

		a.observe(context, subtreeContextValue)

		if a.usage.AllowUnknown {
			t.Fatal("context observation opened the selected chart root")
		}
		if !requireProperty(t, a.usage, "settings").AllowUnknown {
			t.Fatal("context observation did not open a selected root subtree")
		}
		child := requireProperty(t, a.usage, "child")
		if child.AllowUnknown {
			t.Fatal("context observation opened the dependency root")
		}
		if !requireProperty(t, child, "settings").AllowUnknown {
			t.Fatal("context observation did not open a dependency subtree")
		}
	})

	t.Run("same path in parent and dependency scopes", func(t *testing.T) {
		context := union(
			referenceValue(referenceForScope("child")),
			referenceValue(referenceForProperties("child")),
		)
		a := analyzer{usage: NewUsage()}

		a.observe(context, subtreeContextValue)

		if !requireProperty(t, a.usage, "child").AllowUnknown {
			t.Fatal("scope boundary was lost when equal paths were combined")
		}
	})
}

func TestDirectFieldsVariablesAndPrefix(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:         "parent/charts/child/templates/deployment.yaml",
		Entry:        true,
		ValuesPrefix: []string{"child"},
		Content: []byte(`
{{- $image := .Values.image -}}
image: {{ $image.repository }}:{{ $image.tag }}
pullPolicy: {{ $.Values.image.pullPolicy }}
`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}

	image := requireProperty(t, requireProperty(t, usage, "child"), "image")
	for _, name := range []string{"repository", "tag", "pullPolicy"} {
		leaf := requireProperty(t, image, name)
		if !leaf.Read || !leaf.Open {
			t.Errorf("%s flags = Read %v, Open %v", name, leaf.Read, leaf.Open)
		}
	}
	if image.Read || image.Open {
		t.Fatalf("structural image node = Read %v, Open %v", image.Read, image.Open)
	}
}

func TestControlFlowScopesAndJoins(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- $selected := .Values.first -}}
{{- if .Values.useSecond -}}
  {{- $selected = .Values.second -}}
{{- end -}}
name: {{ $selected.name }}
{{- with .Values.image }}repo: {{ .repository }}{{ end }}
{{- range $key, $item := .Values.items }}{{ $key }}={{ $item.value }}{{ end }}
{{- if false }}{{ .Values.dead }}{{ end }}
`)

	for _, name := range []string{"first", "second"} {
		leaf := requireProperty(t, requireProperty(t, usage, name), "name")
		if !leaf.Open {
			t.Errorf("%s.name was not consumed", name)
		}
	}
	if !requireProperty(t, usage, "useSecond").Read {
		t.Error("if condition was not read")
	}
	image := requireProperty(t, usage, "image")
	if !image.Read || !requireProperty(t, image, "repository").Open {
		t.Fatal("with scope did not retain the image origin")
	}
	items := requireProperty(t, usage, "items")
	if items.Read || !items.Iterated {
		t.Errorf("range collection flags = Read %v, Iterated %v", items.Read, items.Iterated)
	}
	if items.Elements == nil {
		t.Error("range element was not recorded")
	}
	if !requireProperty(t, items.Elements, "value").Open {
		t.Error("ranged element field was not recorded")
	}
	if _, exists := usage.Properties["dead"]; exists {
		t.Error("literal false branch contributed usage")
	}
}

func TestIterationAndTruthTestRemainSeparateEvidence(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- if .Values.items }}enabled{{ end -}}
{{- range $key, $_ := .Values.items }}{{ $key }}{{ end -}}
`)

	items := requireProperty(t, usage, "items")
	if !items.Read || !items.Iterated {
		t.Fatalf("items flags = Read %v, Iterated %v", items.Read, items.Iterated)
	}
	if items.Elements != nil {
		t.Fatalf("unused range value created element evidence: %#v", items.Elements)
	}
}

func TestStaticallyEmptyRangeSkipsUnreachableBody(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- range (list) }}{{ $.Values.deadBody }}
{{- else }}{{ .Values.liveElse }}{{ end -}}
`)

	if _, exists := usage.Properties["deadBody"]; exists {
		t.Fatal("empty range contributed usage from its body")
	}
	if !requireProperty(t, usage, "liveElse").Open {
		t.Fatal("empty range did not analyze its else branch")
	}
}

func TestNiladicFunctionUsedAsArgument(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- with (default dict .Values.settings) }}{{ .name }}{{ end -}}
`)

	settings := requireProperty(t, usage, "settings")
	if !settings.Read || !requireProperty(t, settings, "name").Open {
		t.Fatalf("default dict usage = %#v", settings)
	}
}

func TestStaticHelpersAndDictionaryContext(t *testing.T) {
	templates := []Template{
		{
			Name: "templates/_helpers.tpl",
			Content: []byte(`
{{- define "example.settings" -}}
name={{ .settings.name }} root={{ .root.Values.rootName }}
{{- end -}}
{{- define "unused" -}}{{ .Values.unused }}{{- end -}}
`),
		},
		{
			Name:     "templates/configmap.yaml",
			Entry:    true,
			BasePath: "templates",
			Content: []byte(`
{{ include (printf "%s.%s" "example" "settings") (dict "settings" .Values.settings "root" $) }}
`),
		},
	}
	usage, diagnostics, err := Templates(templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	if !requireProperty(t, requireProperty(t, usage, "settings"), "name").Open {
		t.Error("helper dictionary field did not map to its source")
	}
	if !requireProperty(t, usage, "rootName").Open {
		t.Error("root dictionary field did not retain the root context")
	}
	if _, exists := usage.Properties["unused"]; exists {
		t.Error("uncalled helper contributed usage")
	}
}

func TestActionOnlyHelperPreservesOutputOrigin(t *testing.T) {
	templates := []Template{
		{
			Name:    "templates/_helpers.tpl",
			Content: []byte(`{{ define "example.value" }}{{ .value }}{{ end }}`),
		},
		{
			Name:    "templates/configmap.yaml",
			Entry:   true,
			Content: []byte(`{{ index (include "example.value" (dict "value" .Values.payload) | fromYaml) "field" }}`),
		},
	}
	usage, diagnostics, err := Templates(templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	payload := requireProperty(t, usage, "payload")
	if payload.Open || !requireProperty(t, payload, "field").Open {
		t.Fatalf("helper output origin = %#v", payload)
	}
}

func TestRenderedHelperOutputDoesNotCreateFalseFieldSelections(t *testing.T) {
	templates := []Template{
		{
			Name: "templates/_helpers.tpl",
			Content: []byte(`{{ define "example.document" }}
apiVersion: {{ .Values.apiVersion }}
spec:
  storageClass: {{ .Values.storageClass }}
{{ end }}`),
		},
		{
			Name:    "templates/job.yaml",
			Entry:   true,
			Content: []byte(`{{ (include "example.document" . | fromYaml).apiVersion }}`),
		},
	}
	usage, diagnostics, err := Templates(templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	for _, name := range []string{"apiVersion", "storageClass"} {
		node := requireProperty(t, usage, name)
		if !node.Open || len(node.Properties) != 0 {
			t.Errorf("rendered field %q = %#v", name, node)
		}
	}
}

func TestUnreachableLiteralDoesNotMakeHelperOutputOpaque(t *testing.T) {
	templates := []Template{
		{
			Name:    "templates/_helpers.tpl",
			Content: []byte(`{{ define "example.value" }}{{ if false }}field: {{ end }}{{ .value }}{{ end }}`),
		},
		{
			Name:    "templates/configmap.yaml",
			Entry:   true,
			Content: []byte(`{{ index (include "example.value" (dict "value" .Values.payload) | fromYaml) "field" }}`),
		},
	}
	usage, diagnostics, err := Templates(templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	payload := requireProperty(t, usage, "payload")
	if payload.Open || !requireProperty(t, payload, "field").Open {
		t.Fatalf("unreachable literal output = %#v", payload)
	}
}

func TestMergeMutationUpdatesCopiedTemplateContext(t *testing.T) {
	templates := []Template{
		{
			Name: "templates/_helpers.tpl",
			Content: []byte(`
{{- define "common.loader" -}}
resources: {{ .Values.resources | toYaml }}
{{- end -}}
`),
		},
		{
			Name:  "templates/deployment.yaml",
			Entry: true,
			Content: []byte(`
{{- $ctx := deepCopy . -}}
{{- $_ := mergeOverwrite $ctx.Values .Values.server -}}
{{- include "common.loader" $ctx -}}
`),
		},
	}
	usage, diagnostics, err := Templates(templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	serverResources := requireProperty(t, requireProperty(t, usage, "server"), "resources")
	if !serverResources.Open {
		t.Fatalf("merged source was not visible through the copied context: %#v", usage)
	}
	if !requireProperty(t, usage, "resources").Open {
		t.Fatalf("merge destination origin was lost: %#v", usage)
	}
}

func TestMergeIntoValuesDoesNotOpenItsSourceObject(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- $values := mustMergeOverwrite .Values.alloy (or .Values.agent dict) -}}
{{- $values.enableReporting -}}
`)
	alloy := requireProperty(t, usage, "alloy")
	if alloy.Open || alloy.Additional != nil || alloy.Elements != nil {
		t.Fatalf("merge into .Values opened its source: %#v", alloy)
	}
	if !requireProperty(t, alloy, "enableReporting").Open {
		t.Fatalf("merge result lost its selected field: %#v", alloy)
	}
}

func TestCalculatedHelperNameUsesImmutableContext(t *testing.T) {
	templates := []Template{
		{
			Name:    "templates/_helpers.tpl",
			Content: []byte(`{{ define "example.settings" }}{{ .Values.used }}{{ end }}`),
		},
		{
			Name:    "templates/configmap.yaml",
			Entry:   true,
			Context: map[string]any{"Chart": map[string]any{"Name": "example"}},
			Content: []byte(`{{ include (printf "%s.settings" .Chart.Name) . }}`),
		},
	}

	usage, diagnostics, err := Templates(templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	if !requireProperty(t, usage, "used").Open {
		t.Fatal("calculated helper was not followed")
	}
}

func TestSubchartScopeMapsValuesToRootPrefix(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:  "templates/configmap.yaml",
		Entry: true,
		Subcharts: map[string]Scope{
			"worker": {ValuesPrefix: []string{"worker"}},
		},
		Content: []byte(`{{ .Subcharts.worker.Values.message }}`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	message := requireProperty(t, requireProperty(t, usage, "worker"), "message")
	if !message.Open {
		t.Fatal("subchart value did not map to the dependency prefix")
	}
}

func TestIndexWithLiteralStringUsesExactProperty(t *testing.T) {
	usage := analyzeTemplate(t, `{{ index .Values.settings "name" }}`)

	settings := requireProperty(t, usage, "settings")
	if !requireProperty(t, settings, "name").Open {
		t.Fatal("literal index property was not recorded")
	}
	if settings.Elements != nil || settings.Additional != nil {
		t.Fatalf("literal index created dynamic evidence: %#v", settings)
	}
}

func TestRootSelectorsKeepStaticAndDynamicEvidenceSeparate(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- if hasKey .Values "known" }}known{{ end -}}
{{ index .Values "not/literal" }}
`)

	if usage.Open || usage.AllowUnknown || usage.Additional != nil || usage.Elements != nil {
		t.Fatalf("literal root selectors opened the root: %#v", usage)
	}
	if !requireProperty(t, usage, "known").Read {
		t.Fatal("root hasKey selector did not record its literal key")
	}
	if !requireProperty(t, usage, "not/literal").Open {
		t.Fatal("root index selector did not preserve its literal slash key")
	}
}

func TestWholeRootConsumerOpensRoot(t *testing.T) {
	usage := analyzeTemplate(t, `{{ toYaml .Values }}`)
	if !usage.Open {
		t.Fatalf("whole root consumer did not open the root: %#v", usage)
	}
}

func TestTemplateActionUsesFreshRoot(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{
		{
			Name:    "templates/_helpers.tpl",
			Content: []byte(`{{ define "show" }}{{ $.name }}{{ end }}`),
		},
		{
			Name:    "templates/output.yaml",
			Entry:   true,
			Content: []byte(`{{ template "show" .Values.object }}`),
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	if !requireProperty(t, requireProperty(t, usage, "object"), "name").Open {
		t.Error("template invocation did not reset $ to its argument")
	}
}

func TestSelectors(t *testing.T) {
	usage := analyzeTemplate(t, `
port: {{ (index .Values.ports .Values.selectedPort).port }}
label: {{ get .Values.labels "app.kubernetes.io/name" }}
dig: {{ dig "parent" "child" "fallback" .Values }}
{{- if hasKey .Values.feature "enabled" }}enabled{{ end }}
`)

	if !requireProperty(t, usage, "selectedPort").Read {
		t.Error("dynamic index key was not read")
	}
	ports := requireProperty(t, usage, "ports")
	if ports.Elements == nil || !requireProperty(t, ports.Elements, "port").Open {
		t.Error("dynamic index item path was not recorded")
	}
	labels := requireProperty(t, usage, "labels")
	if !requireProperty(t, labels, "app.kubernetes.io/name").Open {
		t.Error("literal dotted key was split or omitted")
	}
	if !requireProperty(t, requireProperty(t, usage, "parent"), "child").Open {
		t.Error("dig path was not recorded")
	}
	if !requireProperty(t, requireProperty(t, usage, "feature"), "enabled").Read {
		t.Error("hasKey path was not recorded")
	}
}

func TestCalculatedStringKeyKeepsFixedAlternatives(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- range $ref := (list "configMapKeyRef" "secretKeyRef") -}}
  {{- $key := $ref | trimSuffix "KeyRef" | lower -}}
  {{- get $.Values $key | toYaml -}}
{{- end -}}
`)

	for _, name := range []string{"configmap", "secret"} {
		if !requireProperty(t, usage, name).Open {
			t.Errorf("calculated key %q was not resolved", name)
		}
	}
	if usage.Additional != nil || usage.Elements != nil {
		t.Fatalf("fixed calculated keys reduced root precision: %#v", usage)
	}
}

func TestDefaultAndCoalescePreserveOrigins(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- $image := default .Values.fallback .Values.primary -}}
{{ $image.repository }}
{{- $tag := coalesce .Values.firstTag .Values.secondTag "latest" -}}
{{ $tag }}
`)

	for _, name := range []string{"fallback", "primary"} {
		node := requireProperty(t, usage, name)
		if !node.Read || !requireProperty(t, node, "repository").Open {
			t.Errorf("default origin %s was not retained", name)
		}
	}
	for _, name := range []string{"firstTag", "secondTag"} {
		node := requireProperty(t, usage, name)
		if !node.Read || !node.Open {
			t.Errorf("coalesce origin %s flags = Read %v, Open %v", name, node.Read, node.Open)
		}
	}
}

func TestWholeConsumer(t *testing.T) {
	usage := analyzeTemplate(t, `{{ .Values.annotations | toYaml | nindent 2 }}`)
	annotations := requireProperty(t, usage, "annotations")
	if !annotations.Read || !annotations.Open {
		t.Fatalf("annotations flags = Read %v, Open %v", annotations.Read, annotations.Open)
	}
}

func TestChecksumUsesExactValueWithoutOpeningObject(t *testing.T) {
	usage := analyzeTemplate(t, `checksum: {{ printf "%s" (.Values.service | toJson | quote) | sha256sum }}`)
	service := requireProperty(t, usage, "service")
	if !service.Exact || service.Read || service.Open || service.AllowUnknown {
		t.Fatalf("checksum service usage = %#v", service)
	}
}

func TestInspectionOfSerializedObjectDoesNotValidateUnknownFields(t *testing.T) {
	usage := analyzeTemplate(t, `{{- $serialized := toYaml .Values -}}{{ contains "error" $serialized }}`)
	if !usage.Exact || usage.Open || usage.AllowUnknown {
		t.Fatalf("serialized inspection usage = %#v", usage)
	}
}

func TestWhitespaceTransformKeepsUsageForLaterOutput(t *testing.T) {
	usage := analyzeTemplate(t, `{{ .Values.payload | toYaml | trim }}`)
	if !requireProperty(t, usage, "payload").Open {
		t.Fatalf("whitespace transform lost output usage: %#v", usage)
	}
}

func TestStringReplacementKeepsUsageForLaterOutput(t *testing.T) {
	usage := analyzeTemplate(t, `{{ .Values.payload | toYaml | replace "old" "new" }}`)
	if !requireProperty(t, usage, "payload").Open {
		t.Fatalf("string replacement lost output usage: %#v", usage)
	}
}

func TestCollectionKeyInspectionDoesNotOpenValues(t *testing.T) {
	usage := analyzeTemplate(t, `{{ keys .Values.settings }}{{ len .Values.other }}`)
	for _, name := range []string{"settings", "other"} {
		node := requireProperty(t, usage, name)
		if node.Open || !node.AllowUnknown {
			t.Errorf("key inspection of %q = %#v", name, node)
		}
	}
}

func TestUnusedOriginPreservingTransformDoesNotCreateUsage(t *testing.T) {
	usage := analyzeTemplate(t, `{{- $unused := .Values.internal | toYaml | nindent 2 -}}`)
	if internal := usage.AtPath("internal"); !internal.Empty() {
		t.Fatalf("unused transformed value created usage = %#v", internal)
	}
}

func TestDynamicIncludePermitsOnlyPassedContext(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:    "templates/output.yaml",
		Entry:   true,
		Content: []byte(`{{ include .Values.helperName .Values.component }}`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 || !strings.Contains(diagnostics[0].Message, "dynamic include") {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if !requireProperty(t, usage, "helperName").Open {
		t.Error("dynamic include name was not consumed")
	}
	component := requireProperty(t, usage, "component")
	if component.Open || !component.AllowUnknown {
		t.Error("dynamic include context did not permit direct properties")
	}
	if usage.Open {
		t.Error("dynamic include of a component opened the root")
	}
}

func TestTPLFixedAndDynamic(t *testing.T) {
	t.Run("fixed", func(t *testing.T) {
		usage := analyzeTemplate(t, `{{ tpl "{{ .Values.inner }}" . }}`)
		if !requireProperty(t, usage, "inner").Open {
			t.Error("fixed tpl text was not analyzed")
		}
		if usage.Open {
			t.Error("fixed tpl text opened the root")
		}
	})

	t.Run("dynamic", func(t *testing.T) {
		usage := analyzeDynamicTPL(t, `{{ tpl .Values.text $ }}`)
		if usage.Open || usage.Read || usage.AllowUnknown {
			t.Error("dynamic tpl opened the values root")
		}
		if text := requireProperty(t, usage, "text"); !text.Open {
			t.Error("dynamic tpl did not open its text source")
		}
	})

	t.Run("values root context", func(t *testing.T) {
		usage := analyzeDynamicTPL(t, `{{ tpl .Values.text .Values }}`)
		if usage.AllowUnknown {
			t.Error(".Values context opened the values root")
		}
		if text := requireProperty(t, usage, "text"); !text.Open {
			t.Error("dynamic tpl did not open its text source")
		}
	})

	t.Run("specific context", func(t *testing.T) {
		usage := analyzeDynamicTPL(t, `{{ tpl .Values.text .Values.settings }}`)
		if usage.AllowUnknown {
			t.Error("specific tpl context opened the values root")
		}
		settings := requireProperty(t, usage, "settings")
		if !settings.AllowUnknown || settings.Open {
			t.Error("specific tpl context did not permit direct properties")
		}
	})

	t.Run("ranged text with root context", func(t *testing.T) {
		usage := analyzeDynamicTPL(t, `{{ range .Values.extraObjects }}{{ tpl . $ }}{{ end }}`)
		if usage.AllowUnknown {
			t.Error("ranged tpl opened the values root")
		}
		extraObjects := requireProperty(t, usage, "extraObjects")
		if extraObjects.Elements == nil || !extraObjects.Elements.Open {
			t.Error("ranged tpl did not open its text items")
		}
	})

	t.Run("dependency root context", func(t *testing.T) {
		usage := analyzeDynamicTPL(t, `{{ tpl .Values.text $ }}`, "child")
		child := requireProperty(t, usage, "child")
		if child.AllowUnknown {
			t.Error("dynamic tpl opened the dependency values root")
		}
		if text := requireProperty(t, child, "text"); !text.Open {
			t.Error("dependency tpl did not open its text source")
		}
	})

	t.Run("dependency specific context", func(t *testing.T) {
		usage := analyzeDynamicTPL(t, `{{ tpl .Values.text .Values.settings }}`, "child")
		child := requireProperty(t, usage, "child")
		if child.AllowUnknown {
			t.Error("dynamic tpl opened the dependency values root")
		}
		settings := requireProperty(t, child, "settings")
		if !settings.AllowUnknown || settings.Open {
			t.Error("specific dependency tpl context did not permit direct properties")
		}
	})
}

func TestTPLAnalyzesDeferredTextBelowSerializedObject(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{
		{
			Name:    "templates/configmap.yaml",
			Entry:   true,
			Content: []byte(`{{ tpl (toYaml .Values.configmap.data) . }}`),
		},
		{
			Name:              "values.yaml/configmap/data/config.json",
			Content:           []byte(`{{ .Values.payload | toJson }}`),
			DeferredValuePath: []ValuePathStep{{Property: "configmap"}, {Property: "data"}, {Property: "config.json"}},
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 || !strings.Contains(diagnostics[0].Message, "dynamic tpl") {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if !requireProperty(t, usage, "payload").Open {
		t.Fatalf("nested deferred text was not analyzed: %#v", usage)
	}
}

func TestNestedRangeSerializedFieldIsCompleteUsage(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- range $item := .Values.stalwart.appliedConfig }}
{{- range $type, $config := $item }}
{{- if $config.singleton }}
{{ $config.value | toJson }}
{{- else if $config.matchOn }}
{{ $config.value | toJson }}
{{- else }}
{{ $config.value | toJson }}
{{- end }}
{{- end }}
{{- end }}
`)
	valueUsage := usage.AtPath("stalwart", "appliedConfig").Elements.Elements.Properties["value"]
	if valueUsage == nil || !valueUsage.Open {
		t.Fatalf("nested serialized value usage = %#v", usage)
	}
}

func TestTPLAnalyzesOnlyDefaultsThatReachTPL(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{
		{
			Name:    "templates/output.yaml",
			Entry:   true,
			Content: []byte(`{{ tpl .Values.used $ }}`),
		},
		{
			Name:              "values.yaml/used",
			Content:           []byte(`{{ .Values.embedded }}`),
			DeferredValuePath: propertyValuePath("used"),
		},
		{
			Name:              "values.yaml/unused",
			Content:           []byte(`{{ .Values.unusedEmbedded }}`),
			DeferredValuePath: propertyValuePath("unused"),
		},
		{
			Name:              "values.yaml/invalid-unused",
			Content:           []byte(`{{`),
			DeferredValuePath: propertyValuePath("invalidUnused"),
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 || !strings.Contains(diagnostics[0].Message, "dynamic tpl") {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if requireProperty(t, usage, "embedded").Empty() {
		t.Error("default template text passed to tpl was not analyzed")
	}
	if _, exists := usage.Properties["unusedEmbedded"]; exists {
		t.Error("unused default template text created usage evidence")
	}
}

func TestTPLReportsInvalidDefaultTextWhenUsed(t *testing.T) {
	_, _, err := Templates([]Template{
		{
			Name:    "templates/output.yaml",
			Entry:   true,
			Content: []byte(`{{ tpl .Values.text $ }}`),
		},
		{
			Name:              "values.yaml/text",
			Content:           []byte(`{{`),
			DeferredValuePath: propertyValuePath("text"),
		},
	})
	if err == nil || !strings.Contains(err.Error(), "parse fixed tpl text") {
		t.Fatalf("error = %v", err)
	}
}

func propertyValuePath(names ...string) []ValuePathStep {
	result := make([]ValuePathStep, len(names))
	for index, name := range names {
		result[index].Property = name
	}
	return result
}

func TestUnknownFunctionUsesGenericFallback(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:    "templates/output.yaml",
		Entry:   true,
		Content: []byte(`{{ futureHelmFunction .Values.payload }}`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 || !strings.Contains(diagnostics[0].Message, "futureHelmFunction") {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if !requireProperty(t, usage, "payload").Open {
		t.Error("unknown function did not consume its complete value argument")
	}
}

func TestUnknownFunctionWithNoValueOriginIsSilent(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:    "templates/output.yaml",
		Entry:   true,
		Content: []byte(`{{ futureHelmFunction "literal" }}`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if !usage.Empty() {
		t.Fatalf("usage = %#v", usage)
	}
}

func TestOmitPreservesUnexcludedOrigins(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- $settings := omit .Values.settings "secret" -}}
{{ $settings.visible }}
`)
	settings := requireProperty(t, usage, "settings")
	if !requireProperty(t, settings, "visible").Open {
		t.Error("omit lost an unexcluded field origin")
	}
	if _, exists := settings.Properties["secret"]; exists {
		t.Error("omit retained the excluded field origin")
	}
}

func TestSortedDiagnosticsRemovesDuplicates(t *testing.T) {
	diagnostic := Diagnostic{Template: "template.yaml", Line: 2, Column: 10, Message: "same"}
	got := sortedDiagnostics([]Diagnostic{diagnostic, diagnostic})
	if len(got) != 1 || got[0] != diagnostic {
		t.Fatalf("diagnostics = %#v", got)
	}
}

func TestDiagnosticUsesLineAndColumn(t *testing.T) {
	_, diagnostics, err := Templates([]Template{{
		Name:    "templates/output.yaml",
		Entry:   true,
		Content: []byte("first line\n{{ futureHelmFunction .Values.payload }}\n"),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if diagnostics[0].Line != 2 || diagnostics[0].Column <= 0 {
		t.Fatalf("diagnostic location = %s", diagnostics[0].String())
	}
}

func TestSetAndUnsetDoNotReadPreviousTarget(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- $_ := set .Values.settings "generated" .Values.source -}}
{{- $_ := unset .Values.other "removed" -}}
`)
	if _, exists := usage.Properties["settings"]; exists {
		t.Error("set marked the previous target as read")
	}
	if _, exists := usage.Properties["other"]; exists {
		t.Error("unset marked the previous target as read")
	}
	if _, exists := usage.Properties["source"]; exists {
		t.Error("unused set result consumed the assigned value")
	}
}

func TestSetMutatesAnInitiallyEmptyObject(t *testing.T) {
	usage := analyzeTemplate(t, `
{{- $settings := dict -}}
{{- $_ := set $settings "name" .Values.name -}}
{{- $settings.name -}}
`)
	if !requireProperty(t, usage, "name").Open {
		t.Fatalf("set value was not visible through the mutated object: %#v", usage)
	}
}

func TestSetAddsSyntheticFieldToRootContext(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{
		{
			Name:    "templates/entry.yaml",
			Entry:   true,
			Content: []byte(`{{- $_ := set $ "ObjectValues" (dict "payload" .Values.source) -}}{{ include "render" $ }}`),
		},
		{
			Name:    "templates/helper.tpl",
			Content: []byte(`{{- define "render" -}}{{ .ObjectValues.payload.path }}{{- end -}}`),
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	if !requireProperty(t, requireProperty(t, usage, "source"), "path").Open {
		t.Fatalf("synthetic root field did not preserve source usage: %#v", usage)
	}
}

func TestSetBelowRealRootValuesDoesNotCreateConfigurablePath(t *testing.T) {
	usage := analyzeTemplate(t, `{{- $_ := set $.Values "generated" .Values.source -}}{{ $.Values.generated.path }}`)
	if source := usage.AtPath("source"); !source.Empty() {
		t.Fatalf("generated value was attributed to its helper source: %#v", source)
	}
	if !usage.AtPath("generated", "path").Open {
		t.Fatalf("direct generated path use was not recorded: %#v", usage)
	}
}

func TestDynamicMutationPermitsDirectKeysWithoutOpeningDescendants(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:  "templates/test.yaml",
		Entry: true,
		Content: []byte(`
{{- $_ := set .Values.settings .Values.selected .Values.source -}}
{{- $_ = unset .Values.other .Values.selected -}}
`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 2 {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	for _, name := range []string{"settings", "other"} {
		node := requireProperty(t, usage, name)
		if node.Open || !node.AllowUnknown {
			t.Errorf("dynamic mutation target %q = %#v", name, node)
		}
	}
	if !requireProperty(t, usage, "selected").Read {
		t.Error("dynamic mutation key was not read")
	}
}

func TestDynamicSetKeepsAssignedValueInConsumedResult(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:  "templates/test.yaml",
		Entry: true,
		Content: []byte(`
{{- $result := set (dict) .Values.selected .Values.payload -}}
{{- $result | toYaml -}}
`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	if !requireProperty(t, usage, "payload").Open {
		t.Fatalf("dynamic set lost assigned value: %#v", usage)
	}
	if !requireProperty(t, usage, "selected").Read {
		t.Fatalf("dynamic set key was not read: %#v", usage)
	}
}

func TestRangeOverDynamicSetReturnsAssignedValue(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:  "templates/test.yaml",
		Entry: true,
		Content: []byte(`
{{- $items := dict -}}
{{- $_ := set $items .Values.selected .Values.payload -}}
{{- range $item := $items -}}{{ $item.primary }}{{- end -}}
`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	payload := requireProperty(t, usage, "payload")
	if !requireProperty(t, payload, "primary").Open {
		t.Fatalf("dynamic set range lost assigned item: %#v", usage)
	}
	if payload.Elements != nil {
		t.Fatalf("dynamic set range added an extra collection level: %#v", payload)
	}
}

func TestDynamicDictionaryKeyDoesNotOpenValueDescendants(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:    "templates/test.yaml",
		Entry:   true,
		Content: []byte(`{{- $unused := dict .Values.selected .Values.payload -}}`),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	payload := requireProperty(t, usage, "payload")
	if payload.Open || !payload.AllowUnknown {
		t.Fatalf("dynamic dictionary value = %#v", payload)
	}
}

func TestLaterDefinitionReplacesEarlierDefinition(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{
		{Name: "first.tpl", Content: []byte(`{{ define "shared" }}{{ .Values.first }}{{ end }}`)},
		{Name: "second.tpl", Content: []byte(`{{ define "shared" }}{{ .Values.second }}{{ end }}`)},
		{Name: "entry.yaml", Entry: true, Content: []byte(`{{ include "shared" . }}`)},
	})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	if _, exists := usage.Properties["first"]; exists {
		t.Error("earlier helper definition remained active")
	}
	if !requireProperty(t, usage, "second").Open {
		t.Error("later helper definition was not active")
	}
}

func TestTemplateSyntaxError(t *testing.T) {
	usage, diagnostics, err := Templates([]Template{{
		Name:    "broken.yaml",
		Entry:   true,
		Content: []byte(`{{ if }}`),
	}})
	if err == nil {
		t.Fatal("expected a parse error")
	}
	if usage != nil || diagnostics != nil {
		t.Fatalf("usage = %#v, diagnostics = %#v", usage, diagnostics)
	}
}

func analyzeTemplate(t *testing.T, content string) *Usage {
	t.Helper()
	usage, diagnostics, err := Templates([]Template{{
		Name:    "templates/test.yaml",
		Entry:   true,
		Content: []byte(content),
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	return usage
}

func analyzeDynamicTPL(t *testing.T, content string, valuesPrefix ...string) *Usage {
	t.Helper()
	usage, diagnostics, err := Templates([]Template{{
		Name:         "templates/test.yaml",
		Entry:        true,
		Content:      []byte(content),
		ValuesPrefix: valuesPrefix,
	}})
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 1 || !strings.Contains(diagnostics[0].Message, "dynamic tpl") {
		t.Fatalf("diagnostics = %v", diagnostics)
	}
	return usage
}

func requireProperty(t *testing.T, usage *Usage, name string) *Usage {
	t.Helper()
	if usage == nil {
		t.Fatalf("cannot find property %q in nil usage", name)
	}
	property := usage.Properties[name]
	if property == nil {
		t.Fatalf("property %q not found; available properties: %v", name, sortedPropertyNames(usage.Properties))
	}
	return property
}
