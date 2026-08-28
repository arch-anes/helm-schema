package helmchart

// This file tests generated-schema validation through Helm's validator.

import (
	"path/filepath"
	"testing"
)

func TestValidate(t *testing.T) {
	defaults := map[string]any{"replicas": 2}
	validSchema := []byte(`{"type":"object","properties":{"replicas":{"type":"integer"}}}`)
	if err := Validate(defaults, validSchema); err != nil {
		t.Fatalf("Validate() error = %v", err)
	}

	invalidSchema := []byte(`{"type":"object","properties":{"replicas":{"type":"string"}}}`)
	if err := Validate(defaults, invalidSchema); err == nil {
		t.Fatal("Validate() error = nil, want a validation error")
	}
}

func TestValidateTreeChecksRawValuesBeforeCoalescing(t *testing.T) {
	chartDirectory := t.TempDir()
	writeChartFile(t, chartDirectory, "Chart.yaml", "apiVersion: v2\nname: raw-values\nversion: 1.0.0\n")
	writeChartFile(t, chartDirectory, "values.yaml", "image:\n  registry: null\n")

	schemaJSON := []byte(`{
  "type": "object",
  "properties": {
    "image": {"const": {}}
  },
  "additionalProperties": false
}`)
	err := ValidateTree(chartDirectory, map[string][]byte{
		filepath.Clean(chartDirectory): schemaJSON,
	})
	if err == nil {
		t.Fatal("ValidateTree accepted raw values that only pass after null coalescing")
	}
}
