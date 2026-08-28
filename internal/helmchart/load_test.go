package helmchart

// This file tests chart loading, dependency scopes, descriptions, metadata
// usage, templated defaults, and explicit null defaults.

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/arch-anes/helm-schema/internal/analyze"
)

func TestLoadCoalescesAliasesAndRetainsTemplateScopes(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    alias: worker
    version: 1.2.0
    repository: file://charts/child
`)
	writeChartFile(t, chartDirectory, "values.yaml", `# Values for the parent chart.

# -- Server settings.
# @section -- Ignored documentation directive.
server:
  # Host name.
  host: localhost
  a/b~c: original # -- Escaped key description.
worker:
  overridden: parent
`)
	writeChartFile(t, chartDirectory, "templates/deployment.yaml", `{{ .Values.server.host }} {{ .Subcharts.worker.Values.parentVisible }}`)
	writeChartFile(t, chartDirectory, "templates/_helpers.tpl", `{{ define "parent.name" }}parent{{ end }}`)

	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeChartFile(t, childDirectory, "Chart.yaml", `apiVersion: v2
name: child
version: 1.2.0
`)
	writeChartFile(t, childDirectory, "values.yaml", `# Child settings.

# Value provided by the child.
overridden: child
# Retained child value.
fromChild: retained
parentVisible: exposed
`)
	writeChartFile(t, childDirectory, "templates/config.yaml", `{{ .Values.fromChild }}`)
	writeChartFile(t, childDirectory, "templates/_helpers.tpl", `{{ define "child.name" }}child{{ end }}`)

	data, err := Load(chartDirectory)
	if err != nil {
		t.Fatalf("Load() error = %v", err)
	}

	wantScopes := []ChartScope{
		{Directory: childDirectory, ValuesPrefixes: [][]string{{"worker"}}},
		{Directory: filepath.Clean(chartDirectory), ValuesPrefixes: [][]string{nil}},
	}
	if !reflect.DeepEqual(data.Scopes, wantScopes) {
		t.Errorf("Scopes = %#v, want %#v", data.Scopes, wantScopes)
	}

	worker, ok := data.Defaults["worker"].(map[string]any)
	if !ok {
		t.Fatalf("Defaults[worker] = %#v, want a map", data.Defaults["worker"])
	}
	if worker["overridden"] != "parent" {
		t.Errorf("worker.overridden = %#v, want parent", worker["overridden"])
	}
	if worker["fromChild"] != "retained" {
		t.Errorf("worker.fromChild = %#v, want retained", worker["fromChild"])
	}

	wantDescriptions := map[string]string{
		"":                  "Values for the parent chart.",
		"/server":           "Server settings.",
		"/server/host":      "Host name.",
		"/server/a~1b~0c":   "Escaped key description.",
		"/worker":           "Child settings.",
		"/worker/fromChild": "Retained child value.",
	}
	for pointer, want := range wantDescriptions {
		if got := data.Descriptions[pointer]; got != want {
			t.Errorf("Descriptions[%q] = %q, want %q", pointer, got, want)
		}
	}

	templates := make(map[string]struct {
		entry    bool
		prefix   []string
		basePath string
		chart    string
	})
	for _, template := range data.Templates {
		templates[template.Name] = struct {
			entry    bool
			prefix   []string
			basePath string
			chart    string
		}{template.Entry, template.ValuesPrefix, template.BasePath, template.Context["Chart"].(map[string]any)["Name"].(string)}
	}

	assertTemplate := func(name string, entry bool, prefix []string, basePath, chartName string) {
		t.Helper()
		got, ok := templates[name]
		if !ok {
			t.Errorf("template %q was not loaded", name)
			return
		}
		if got.entry != entry || !reflect.DeepEqual(got.prefix, prefix) || got.basePath != basePath || got.chart != chartName {
			t.Errorf("template %q = %#v, want entry=%t prefix=%v basePath=%q chart=%q", name, got, entry, prefix, basePath, chartName)
		}
	}
	assertTemplate("parent/templates/deployment.yaml", true, nil, "parent/templates", "parent")
	assertTemplate("parent/templates/_helpers.tpl", false, nil, "parent/templates", "parent")
	assertTemplate("parent/charts/worker/templates/config.yaml", true, []string{"worker"}, "parent/charts/worker/templates", "worker")
	assertTemplate("parent/charts/worker/templates/_helpers.tpl", false, []string{"worker"}, "parent/charts/worker/templates", "worker")

	usage, diagnostics, err := analyze.Templates(data.Templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	if node := usageProperty(usage, "worker", "parentVisible"); node == nil || !node.Open {
		t.Fatalf("subchart value usage = %#v", usage)
	}
}

func TestLoadCoalescesNestedDependencyAliases(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    alias: app
    version: 1.0.0
    repository: file://charts/child
`)
	writeChartFile(t, chartDirectory, "values.yaml", "app:\n  nested:\n    parent: true\n")

	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeChartFile(t, childDirectory, "Chart.yaml", `apiVersion: v2
name: child
version: 1.0.0
dependencies:
  - name: grandchild
    alias: backend
    version: 1.0.0
    repository: file://charts/grandchild
`)
	writeChartFile(t, childDirectory, "values.yaml", "nested:\n  child: true\n")

	grandchildDirectory := filepath.Join(childDirectory, "charts", "grandchild")
	writeChartFile(t, grandchildDirectory, "Chart.yaml", "apiVersion: v2\nname: grandchild\nversion: 1.0.0\n")
	writeChartFile(t, grandchildDirectory, "values.yaml", "setting: true\n")

	data, err := Load(chartDirectory)
	if err != nil {
		t.Fatal(err)
	}
	app := data.Defaults["app"].(map[string]any)
	nested := app["nested"].(map[string]any)
	if nested["parent"] != true || nested["child"] != true {
		t.Fatalf("nested child defaults were not coalesced: %#v", nested)
	}
	backend := app["backend"].(map[string]any)
	if backend["setting"] != true {
		t.Fatalf("grandchild defaults were not coalesced below aliases: %#v", backend)
	}

	wantScopes := []ChartScope{
		{Directory: grandchildDirectory, ValuesPrefixes: [][]string{{"app", "backend"}}},
		{Directory: childDirectory, ValuesPrefixes: [][]string{{"app"}}},
		{Directory: chartDirectory, ValuesPrefixes: [][]string{nil}},
	}
	if !reflect.DeepEqual(data.Scopes, wantScopes) {
		t.Fatalf("nested dependency scopes = %#v, want %#v", data.Scopes, wantScopes)
	}
}

func TestLoadRejectsInvalidValuesYAML(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: invalid-values\nversion: 1.0.0\n")
	writeChartFile(t, chartDirectory, "values.yaml", "key: [\n")

	if _, err := Load(chartDirectory); err == nil {
		t.Fatal("Load accepted invalid values.yaml")
	}
}
func TestLoadRetainsTemplatesFromDefaultDisabledDependency(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    version: 1.0.0
    repository: file://charts/child
    condition: child.enabled
`)
	writeChartFile(t, chartDirectory, "values.yaml", "child:\n  enabled: false\n")
	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeChartFile(t, childDirectory, "Chart.yaml", "apiVersion: v2\nname: child\nversion: 1.0.0\n")
	writeChartFile(t, childDirectory, "values.yaml", "message: hello\n")
	writeChartFile(t, childDirectory, "templates/config.yaml", `{{ .Values.message }}`)

	data, err := Load(chartDirectory)
	if err != nil {
		t.Fatalf("Load() error = %v", err)
	}
	childDefaults, ok := data.Defaults["child"].(map[string]any)
	if !ok {
		t.Fatalf("Defaults[child] = %#v, want a map with the condition value", data.Defaults["child"])
	}
	if childDefaults["message"] != "hello" {
		t.Errorf("disabled dependency default child.message = %#v, want hello", childDefaults["message"])
	}
	condition := data.MetadataUsage.Properties["child"].Properties["enabled"]
	if condition == nil || !condition.Read {
		t.Fatalf("dependency condition usage = %#v", data.MetadataUsage)
	}
	found := false
	for _, template := range data.Templates {
		if template.Name == "parent/charts/child/templates/config.yaml" {
			found = true
			break
		}
	}
	if !found {
		t.Error("disabled dependency template was not retained")
	}
}

func TestLoadPreservesExplicitNullDefaults(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    alias: worker
    version: 1.0.0
    repository: file://charts/child
`)
	writeChartFile(t, chartDirectory, "values.yaml", "optional: null\nworker:\n  blockedNull: parent-value\n  parentNull: null\n")
	writeChartFile(t, chartDirectory, "templates/config.yaml", `{{ range .Values.optional }}{{ . }}{{ end }}`)

	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeChartFile(t, childDirectory, "Chart.yaml", "apiVersion: v2\nname: child\nversion: 1.0.0\n")
	writeChartFile(t, childDirectory, "values.yaml", "blockedNull: null\nchildNull: null\nparentNull: child-value\n")
	writeChartFile(t, childDirectory, "templates/config.yaml", `{{ .Values.childNull }}`)

	data, err := Load(chartDirectory)
	if err != nil {
		t.Fatal(err)
	}
	if value, exists := data.Defaults["optional"]; !exists || value != nil {
		t.Errorf("Defaults[optional] = %#v, exists=%t; want an explicit null", value, exists)
	}
	worker, ok := data.Defaults["worker"].(map[string]any)
	if !ok {
		t.Fatalf("Defaults[worker] = %#v, want an object", data.Defaults["worker"])
	}
	if value, exists := worker["childNull"]; !exists || value != nil {
		t.Errorf("worker.childNull = %#v, exists=%t; want an explicit null", value, exists)
	}
	if value := worker["blockedNull"]; value != "parent-value" {
		t.Errorf("worker.blockedNull = %#v, want the parent value", value)
	}
	if value := worker["parentNull"]; value != "child-value" {
		t.Errorf("worker.parentNull = %#v, want the coalesced child value", value)
	}
	wantNulls := [][]string{{"optional"}, {"worker", "childNull"}, {"worker", "parentNull"}}
	if !reflect.DeepEqual(data.ExplicitNullDefaults, wantNulls) {
		t.Errorf("ExplicitNullDefaults = %#v, want %#v", data.ExplicitNullDefaults, wantNulls)
	}
}

func TestLoadMetadataUsageAndValueFlows(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    alias: worker
    version: 1.0.0
    repository: file://charts/child
    condition: worker.enabled
    tags: [backend]
    import-values:
      - child: settings
        parent: imported
`)
	writeChartFile(t, chartDirectory, "values.yaml", "worker:\n  enabled: false\ntags:\n  backend: false\n")
	writeChartFile(t, chartDirectory, "templates/config.yaml", `{{ .Values.imported.message }}`)

	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeChartFile(t, childDirectory, "Chart.yaml", "apiVersion: v2\nname: child\nversion: 1.0.0\n")
	writeChartFile(t, childDirectory, "values.yaml", "settings:\n  message: hello\n")
	writeChartFile(t, childDirectory, "templates/config.yaml", `{{ .Values.global.region }}`)

	data, err := Load(chartDirectory)
	if err != nil {
		t.Fatal(err)
	}
	if node := usageProperty(data.MetadataUsage, "worker", "enabled"); node == nil || !node.Read {
		t.Fatalf("condition usage = %#v", data.MetadataUsage)
	}
	if node := usageProperty(data.MetadataUsage, "tags", "backend"); node == nil || !node.Read {
		t.Fatalf("tag usage = %#v", data.MetadataUsage)
	}

	usage, diagnostics, err := analyze.Templates(data.Templates)
	if err != nil {
		t.Fatal(err)
	}
	if len(diagnostics) != 0 {
		t.Fatalf("unexpected diagnostics: %v", diagnostics)
	}
	usage.Merge(data.MetadataUsage)
	if err := analyze.ApplyValueFlows(usage, data.ValueFlows); err != nil {
		t.Fatal(err)
	}
	if node := usageProperty(usage, "worker", "settings", "message"); node == nil || !node.Open {
		t.Fatalf("import source usage = %#v", usage)
	}
	if node := usageProperty(usage, "global", "region"); node == nil || !node.Open {
		t.Fatalf("global source usage = %#v", usage)
	}
}

func TestLoadRejectsSelectedLibraryChart(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: helpers\ntype: library\nversion: 1.0.0\n")

	_, err := Load(chartDirectory)
	if err == nil || !strings.Contains(err.Error(), "library chart") {
		t.Fatalf("Load() error = %v, want a library chart error", err)
	}
}

func TestLoadDoesNotExecuteLibraryDependencyFiles(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: helpers
    version: 1.0.0
    repository: file://charts/helpers
`)
	libraryDirectory := filepath.Join(chartDirectory, "charts", "helpers")
	writeChartFile(t, libraryDirectory, "Chart.yaml", "apiVersion: v2\nname: helpers\ntype: library\nversion: 1.0.0\n")
	writeChartFile(t, libraryDirectory, "templates/output.yaml", `{{ .Values.notAnEntry }}`)

	data, err := Load(chartDirectory)
	if err != nil {
		t.Fatal(err)
	}
	for _, template := range data.Templates {
		if strings.HasSuffix(template.Name, "templates/output.yaml") {
			t.Fatalf("invalid library template was loaded: %#v", template)
		}
	}
}

func TestLoadRejectsMissingDeclaredDependency(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: absent
    version: 1.0.0
    repository: file://charts/absent
`)

	_, err := Load(chartDirectory)
	if err == nil || !strings.Contains(err.Error(), `dependency "absent"`) || !strings.Contains(err.Error(), "missing from charts/") {
		t.Fatalf("Load() error = %v, want a missing dependency error", err)
	}
}

func writeChartFile(t *testing.T, chartDirectory, name, content string) {
	t.Helper()
	filename := filepath.Join(chartDirectory, filepath.FromSlash(name))
	if err := os.MkdirAll(filepath.Dir(filename), 0o755); err != nil {
		t.Fatalf("create chart directory: %v", err)
	}
	if err := os.WriteFile(filename, []byte(content), 0o600); err != nil {
		t.Fatalf("write chart file %s: %v", name, err)
	}
}

func usageProperty(usage *analyze.Usage, path ...string) *analyze.Usage {
	for _, name := range path {
		if usage == nil {
			return nil
		}
		usage = usage.Properties[name]
	}
	return usage
}
