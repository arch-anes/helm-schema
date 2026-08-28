package main

// This file tests command behavior, safe file replacement, Helm lint, and the
// packaged Helm plugin.

import (
	"bytes"
	"encoding/json"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	chartarchive "helm.sh/helm/v4/pkg/chart/loader/archive"
)

func TestReplaceFile(t *testing.T) {
	t.Parallel()

	path := filepath.Join(t.TempDir(), "values.schema.json")
	if err := os.WriteFile(path, []byte("old\n"), 0o600); err != nil {
		t.Fatal(err)
	}

	changed, err := replaceFile(path, []byte("new\n"))
	if err != nil {
		t.Fatal(err)
	}
	if !changed {
		t.Fatal("replaceFile reported no change")
	}
	content, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(content) != "new\n" {
		t.Fatalf("content = %q", content)
	}

	changed, err = replaceFile(path, content)
	if err != nil {
		t.Fatal(err)
	}
	if changed {
		t.Fatal("replaceFile replaced equal content")
	}
}

func TestHelp(t *testing.T) {
	t.Parallel()

	var stdout bytes.Buffer
	if err := run([]string{"--help"}, &stdout, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	if !bytes.Contains(stdout.Bytes(), []byte("helm schema [CHART]")) {
		t.Fatalf("help output = %q", stdout.String())
	}
}

func TestVersion(t *testing.T) {
	t.Parallel()

	var stdout bytes.Buffer
	if err := run([]string{"--version"}, &stdout, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	if stdout.String() != "helm-schema dev\n" {
		t.Fatalf("version output = %q", stdout.String())
	}
}

func TestTooManyArguments(t *testing.T) {
	t.Parallel()

	err := run([]string{"one", "two"}, &bytes.Buffer{}, &bytes.Buffer{})
	if err == nil {
		t.Fatal("run accepted two chart arguments")
	}
}

func TestUnknownOption(t *testing.T) {
	t.Parallel()

	err := run([]string{"--unknown"}, &bytes.Buffer{}, &bytes.Buffer{})
	if err == nil {
		t.Fatal("run accepted an unknown option")
	}
}

func TestPrecisionNoteOnlyReportsOpenRoot(t *testing.T) {
	t.Parallel()

	var stderr bytes.Buffer
	writePrecisionNote(&stderr, false)
	if stderr.Len() != 0 {
		t.Fatalf("closed-root output = %q", stderr.String())
	}

	writePrecisionNote(&stderr, true)
	if !strings.Contains(stderr.String(), "permits root properties that templates do not name statically") {
		t.Fatalf("open-root output = %q", stderr.String())
	}
}

func TestCheckGeneratedSchemaSizeUsesHelmLimit(t *testing.T) {
	content := make([]byte, int(chartarchive.MaxDecompressedFileSize)+1)
	if err := checkGeneratedSchemaSize("chart", content[:len(content)-1]); err != nil {
		t.Fatalf("schema at Helm's limit was rejected: %v", err)
	}
	if err := checkGeneratedSchemaSize("chart", content); err == nil {
		t.Fatal("schema above Helm's limit was accepted")
	}
}

func TestRunGeneratesSchemaAndHelmLintUsesIt(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := copyBasicChart(t)
	schemaPath := filepath.Join(chartDirectory, "values.schema.json")
	if err := os.WriteFile(schemaPath, []byte(`{"old":true}`), 0o600); err != nil {
		t.Fatal(err)
	}

	var stdout bytes.Buffer
	var stderr bytes.Buffer
	if err := run([]string{chartDirectory}, &stdout, &stderr); err != nil {
		t.Fatalf("run() error = %v\nstderr:\n%s", err, stderr.String())
	}

	generated, err := os.ReadFile(schemaPath)
	if err != nil {
		t.Fatal(err)
	}
	var root map[string]any
	if err := json.Unmarshal(generated, &root); err != nil {
		t.Fatalf("generated schema is invalid JSON: %v", err)
	}
	properties := schemaProperties(t, root)
	if fixed, ok := properties["unusedSetting"].(map[string]any)["const"]; !ok || fixed != "unchanged" {
		t.Fatalf("unusedSetting is not fixed: %#v", properties["unusedSetting"])
	}
	image := properties["image"].(map[string]any)
	if fixed := schemaProperties(t, image)["pullPolicy"].(map[string]any)["const"]; fixed != "IfNotPresent" {
		t.Fatalf("image.pullPolicy is not fixed: %#v", fixed)
	}
	if properties["route"] == nil {
		t.Fatal("route usage is missing")
	}

	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, true, "--set", "replicaCount=3")
	assertHelmLint(t, chartDirectory, true, "--set", "route.annotations.acceptance=yes")
	assertHelmLint(t, chartDirectory, true, "--set", "selectedPort=extra", "--set", "ports.extra.port=9090")
	assertHelmLint(t, chartDirectory, true, "--set", "items[0].name=second")
	assertHelmLint(t, chartDirectory, true, "--set-json", "unusedSetting=null")
	assertHelmLint(t, chartDirectory, false, "--set-string", "unusedSetting=changed")
	assertHelmLint(t, chartDirectory, false, "--set", "unknownRoot=true")
	assertHelmLint(t, chartDirectory, false, "--set", "items[0].name=second", "--set", "items[0].internalNote=changed")
	assertHelmLint(t, chartDirectory, false, "--set", "ports.extra.port=9090", "--set", "ports.extra.internalNote=changed")
}

func TestRunRejectsValueDeclaredOnlyInComment(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: comments\nversion: 1.0.0\n")
	writeTestFile(t, chartDirectory, "values.yaml", "# commentedOnly: true\nknown: true\n")
	writeTestFile(t, chartDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: comments
data:
  known: {{ .Values.known | quote }}
`)

	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, false, "--set", "commentedOnly=true")
}

func TestRunTreatsNullOnlyRootAsEmptyForTruthTest(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: null-root\nversion: 1.0.0\n")
	writeTestFile(t, chartDirectory, "values.yaml", "optional: null\n")
	writeTestFile(t, chartDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: null-root
data:
  state: {{ if .Values }}"nonempty"{{ else }}"empty"{{ end }}
`)

	var stderr bytes.Buffer
	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &stderr); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(stderr.String(), "permits root properties that templates do not name statically") {
		t.Fatalf("null-only root precision note = %q", stderr.String())
	}
	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, true, "--set", "dynamic=true")
}

func TestRunInfersDynamicRootEntriesWithoutImageSelectorRule(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: images\nversion: 1.0.0\n")
	writeTestFile(t, chartDirectory, "values.yaml", `imageSelector: mainImage
mainImage:
  repository: example/application
`)
	writeTestFile(t, chartDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: images
data:
  repository: {{ (index .Values .Values.imageSelector).repository | quote }}
`)

	var stderr bytes.Buffer
	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &stderr); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(stderr.String(), "permits root properties that templates do not name statically") {
		t.Fatalf("dynamic root precision note = %q", stderr.String())
	}
	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, true,
		"--set", "imageSelector=extraImage",
		"--set", "extraImage.repository=example/extra",
	)
	assertHelmLint(t, chartDirectory, false,
		"--set", "imageSelector=extraImage",
		"--set", "extraImage.repository=example/extra",
		"--set", "extraImage.repositry=example/typo",
	)
}

func TestRunSupportsDefaultDisabledDependency(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    version: 1.0.0
    repository: file://charts/child
    condition: child.enabled
`)
	writeTestFile(t, chartDirectory, "values.yaml", "global:\n  region: local\nchild:\n  enabled: false\n")
	writeTestFile(t, chartDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: parent
data:
  region: {{ .Values.global.region | quote }}
`)
	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeTestFile(t, childDirectory, "Chart.yaml", "apiVersion: v2\nname: child\nversion: 1.0.0\n")
	writeTestFile(t, childDirectory, "values.yaml", "message: hello\ninternal: fixed\n")
	writeTestFile(t, childDirectory, "values.schema.json", `{"type":"object","additionalProperties":false}`)
	writeTestFile(t, childDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: child
data:
  message: {{ .Values.message | quote }}
`)

	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(childDirectory, "values.schema.json")); err != nil {
		t.Fatalf("dependency schema was not generated: %v", err)
	}
	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, true, "--set", "child.enabled=true")
	assertHelmLint(t, chartDirectory, true, "--set", "global.region=remote")
	assertHelmLint(t, chartDirectory, true, "--set", "child.enabled=true", "--set", "child.message=changed")
	assertHelmLint(t, chartDirectory, false, "--set", "child.enabled=true", "--set", "child.internal=changed")
}

func TestRunCombinesSharedDependencyAliases(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", `apiVersion: v2
name: parent
version: 1.0.0
dependencies:
  - name: child
    alias: first
    version: 1.0.0
    repository: file://charts/child
  - name: child
    alias: second
    version: 1.0.0
    repository: file://charts/child
`)
	writeTestFile(t, chartDirectory, "values.yaml", "first:\n  message: text\nsecond:\n  message: 2\n")
	childDirectory := filepath.Join(chartDirectory, "charts", "child")
	writeTestFile(t, childDirectory, "Chart.yaml", "apiVersion: v2\nname: child\nversion: 1.0.0\n")
	writeTestFile(t, childDirectory, "values.yaml", "message: default\n")
	writeTestFile(t, childDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: {{ .Release.Name }}
data:
  message: {{ .Values.message | quote }}
`)

	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, true)

	generated, err := os.ReadFile(filepath.Join(childDirectory, "values.schema.json"))
	if err != nil {
		t.Fatal(err)
	}
	var childSchema map[string]any
	if err := json.Unmarshal(generated, &childSchema); err != nil {
		t.Fatal(err)
	}
	if alternatives, ok := childSchema["anyOf"].([]any); !ok || len(alternatives) != 2 {
		t.Fatalf("shared dependency schema alternatives = %#v, want two", childSchema["anyOf"])
	}
}

func TestRunAcceptsExplicitNullDefault(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: nullable\nversion: 1.0.0\n")
	writeTestFile(t, chartDirectory, "values.yaml", "extraManifests: null\n")
	writeTestFile(t, chartDirectory, "templates/configmap.yaml", `{{- range .Values.extraManifests }}
{{ toYaml . }}
{{- end }}
`)

	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, true)
}

func TestRunAcceptsUnusedObjectWhoseChildrenAreNull(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := t.TempDir()
	writeTestFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: null-children\nversion: 1.0.0\n")
	writeTestFile(t, chartDirectory, "values.yaml", `component:
  enabled: true
  image:
    registry: null
    repository: null
    tag: null
`)
	writeTestFile(t, chartDirectory, "templates/configmap.yaml", `apiVersion: v1
kind: ConfigMap
metadata:
  name: null-children
data:
  enabled: {{ .Values.component.enabled | quote }}
`)

	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, true)

	generated, err := os.ReadFile(filepath.Join(chartDirectory, "values.schema.json"))
	if err != nil {
		t.Fatal(err)
	}
	var root map[string]any
	if err := json.Unmarshal(generated, &root); err != nil {
		t.Fatal(err)
	}
	component := schemaProperties(t, root)["component"].(map[string]any)
	image := schemaProperties(t, component)["image"].(map[string]any)
	if image["type"] != "object" || image["additionalProperties"] != false {
		t.Fatalf("null-only image default is not a closed object: %#v", image)
	}
	imageProperties := schemaProperties(t, image)
	for _, name := range []string{"registry", "repository", "tag"} {
		property := imageProperties[name].(map[string]any)
		constant, exists := property["const"]
		if !exists || constant != nil {
			t.Fatalf("image.%s is not fixed to null: %#v", name, property)
		}
	}
}

func TestRunKeepsKnownObjectsStrictWithDynamicTPL(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := copyFixture(t, "kube-prometheus-stack-88-regression")

	var stderr bytes.Buffer
	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &stderr); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(stderr.String(), "permits root properties that templates do not name statically") {
		t.Fatalf("dynamic tpl precision note = %q", stderr.String())
	}
	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, true, "--set", "dynamic=value")
	assertHelmLint(t, chartDirectory, true, "--set", "prometheus.prometheusSpec.embedded=value")
	assertHelmLint(t, chartDirectory, false, "--set", "prometheus.prometheusSpec.unusedEmbedded=value")
	assertHelmLint(t, chartDirectory, false, "--set", "prometheus.prometheusSpec.retentionSiz=1")

	valuesPath := filepath.Join(chartDirectory, "values.yaml")
	values, err := os.ReadFile(valuesPath)
	if err != nil {
		t.Fatal(err)
	}
	misspelled := bytes.Replace(values, []byte(`retentionSize: ""`), []byte(`retentionSiz: ""`), 1)
	if bytes.Equal(misspelled, values) {
		t.Fatal("retentionSize fixture value was not found")
	}
	if err := os.WriteFile(valuesPath, misspelled, 0o600); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, false)
}

func TestRunKeepsDynamicMapEntriesStrict(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := copyFixture(t, "octoprint-common-29-regression")
	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, true)
	assertHelmLint(t, chartDirectory, true,
		"--set", "service.extra.enabled=true",
		"--set", "service.extra.ports.http.enabled=true",
		"--set", "service.extra.ports.http.port=8080",
		"--set", "service.extra.ports.http.targetPort=80",
	)
	assertHelmLint(t, chartDirectory, false, "--set", "service.main.ports.main.enablede=true")

	valuesPath := filepath.Join(chartDirectory, "values.yaml")
	values, err := os.ReadFile(valuesPath)
	if err != nil {
		t.Fatal(err)
	}
	misspelled := bytes.Replace(values, []byte("        enabled: true\n        port:"), []byte("        enablede: true\n        port:"), 1)
	if bytes.Equal(misspelled, values) {
		t.Fatal("enabled fixture value was not found")
	}
	if err := os.WriteFile(valuesPath, misspelled, 0o600); err != nil {
		t.Fatal(err)
	}
	assertHelmLint(t, chartDirectory, false)
}

func TestRunLeavesExistingSchemaAfterAnalysisError(t *testing.T) {
	chartDirectory := copyBasicChart(t)
	schemaPath := filepath.Join(chartDirectory, "values.schema.json")
	sentinel := []byte("existing schema\n")
	if err := os.WriteFile(schemaPath, sentinel, 0o600); err != nil {
		t.Fatal(err)
	}

	templatePath := filepath.Join(chartDirectory, "templates", "invalid.yaml")
	if err := os.WriteFile(templatePath, []byte("{{"), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err == nil {
		t.Fatal("run accepted invalid template syntax")
	}

	content, err := os.ReadFile(schemaPath)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(content, sentinel) {
		t.Fatalf("existing schema changed to %q", content)
	}
}

func TestRunReplacesOversizedExistingSchema(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}

	chartDirectory := copyBasicChart(t)
	schemaPath := filepath.Join(chartDirectory, "values.schema.json")
	if err := os.WriteFile(schemaPath, []byte(strings.Repeat(" ", int(chartarchive.MaxDecompressedFileSize)+1)), 0o600); err != nil {
		t.Fatal(err)
	}

	if err := run([]string{chartDirectory}, &bytes.Buffer{}, &bytes.Buffer{}); err != nil {
		t.Fatal(err)
	}
	info, err := os.Stat(schemaPath)
	if err != nil {
		t.Fatal(err)
	}
	if info.Size() >= chartarchive.MaxDecompressedFileSize {
		t.Fatalf("replacement schema remains oversized: %d bytes", info.Size())
	}
	assertHelmLint(t, chartDirectory, true)
}

func TestHelmPluginInstallAndRun(t *testing.T) {
	if _, err := exec.LookPath("helm"); err != nil {
		t.Skip("helm is not installed")
	}
	if _, err := exec.LookPath("go"); err != nil {
		t.Skip("go is not installed")
	}

	projectRoot, err := filepath.Abs(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	temporary := t.TempDir()
	pluginSource := filepath.Join(temporary, "schema")
	if err := os.MkdirAll(filepath.Join(pluginSource, "bin"), 0o755); err != nil {
		t.Fatal(err)
	}
	binaryPath := filepath.Join(pluginSource, "bin", "helm-schema")
	build := exec.Command("go", "build", "-trimpath", "-o", binaryPath, "./cmd/helm-schema")
	build.Dir = projectRoot
	if output, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build plugin binary: %v\n%s", err, output)
	}
	manifest, err := os.ReadFile(filepath.Join(projectRoot, "plugin.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(pluginSource, "plugin.yaml"), manifest, 0o600); err != nil {
		t.Fatal(err)
	}

	dataHome := filepath.Join(temporary, "data")
	pluginDirectory := filepath.Join(dataHome, "plugins")
	if err := os.MkdirAll(pluginDirectory, 0o755); err != nil {
		t.Fatal(err)
	}
	helmEnvironment := append(os.Environ(),
		"HELM_PLUGINS="+pluginDirectory,
		"HELM_CACHE_HOME="+filepath.Join(temporary, "cache"),
		"HELM_CONFIG_HOME="+filepath.Join(temporary, "config"),
		"HELM_DATA_HOME="+dataHome,
	)
	install := exec.Command("helm", "plugin", "install", pluginSource)
	install.Env = helmEnvironment
	if output, err := install.CombinedOutput(); err != nil {
		t.Fatalf("install plugin: %v\n%s", err, output)
	}
	list := exec.Command("helm", "plugin", "list")
	list.Env = helmEnvironment
	listOutput, err := list.CombinedOutput()
	if err != nil {
		t.Fatalf("list plugins: %v\n%s", err, listOutput)
	}
	if !bytes.Contains(listOutput, []byte("schema")) || !bytes.Contains(listOutput, []byte("cli/v1")) {
		t.Fatalf("plugin list does not identify the cli/v1 plugin:\n%s", listOutput)
	}

	chartDirectory := copyBasicChart(t)
	generate := exec.Command("helm", "schema", chartDirectory)
	generate.Env = helmEnvironment
	if output, err := generate.CombinedOutput(); err != nil {
		t.Fatalf("run plugin: %v\n%s", err, output)
	}
	if _, err := os.Stat(filepath.Join(chartDirectory, "values.schema.json")); err != nil {
		t.Fatalf("plugin did not generate values.schema.json: %v", err)
	}
}

func copyBasicChart(t *testing.T) string {
	return copyFixture(t, "basic")
}

func copyFixture(t *testing.T, name string) string {
	t.Helper()
	destination := filepath.Join(t.TempDir(), name)
	if err := os.CopyFS(destination, os.DirFS(filepath.Join("..", "..", "testdata", name))); err != nil {
		t.Fatal(err)
	}
	return destination
}

func schemaProperties(t *testing.T, value map[string]any) map[string]any {
	t.Helper()
	properties, ok := value["properties"].(map[string]any)
	if !ok {
		t.Fatalf("schema has no properties: %#v", value)
	}
	return properties
}

func assertHelmLint(t *testing.T, chartDirectory string, wantSuccess bool, arguments ...string) {
	t.Helper()
	commandArguments := append([]string{"lint", chartDirectory}, arguments...)
	output, err := exec.Command("helm", commandArguments...).CombinedOutput()
	if wantSuccess && err != nil {
		t.Fatalf("helm %v failed: %v\n%s", commandArguments, err, output)
	}
	if !wantSuccess && err == nil {
		t.Fatalf("helm %v succeeded unexpectedly:\n%s", commandArguments, output)
	}
}

func writeTestFile(t *testing.T, directory, name, content string) {
	t.Helper()
	path := filepath.Join(directory, filepath.FromSlash(name))
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(content), 0o600); err != nil {
		t.Fatal(err)
	}
}
