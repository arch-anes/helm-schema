package helmchart

// This file validates generated schemas with Helm's own value processing.

import (
	"bytes"
	"fmt"
	"path/filepath"
	"strings"

	chartcommon "helm.sh/helm/v4/pkg/chart/common"
	chartcommonutil "helm.sh/helm/v4/pkg/chart/common/util"
	chartv2 "helm.sh/helm/v4/pkg/chart/v2"
)

// Validate checks values against one generated schema with Helm's validator.
func Validate(defaults map[string]any, schemaJSON []byte) error {
	if defaults == nil {
		defaults = map[string]any{}
	}
	if err := chartcommonutil.ValidateAgainstSingleSchema(chartcommon.Values(defaults), schemaJSON); err != nil {
		return fmt.Errorf("validate chart defaults against generated schema: %w", err)
	}
	return nil
}

// ValidateTree checks the generated root and dependency schemas against the
// complete values tree that Helm builds for the selected chart. It includes
// dependencies that defaults disable because an override can enable them.
func ValidateTree(chartPath string, schemas map[string][]byte) error {
	absolutePath, err := chartDirectory(chartPath)
	if err != nil {
		return err
	}
	root, err := loadChartForGeneration(absolutePath)
	if err != nil {
		return fmt.Errorf("load chart %q: %w", absolutePath, err)
	}
	applySchemas(root, root, absolutePath, schemas)
	if err := chartcommonutil.ValidateAgainstSingleSchema(chartcommon.Values(root.Values), root.Schema); err != nil {
		return fmt.Errorf("validate raw root values against generated schema: %w", err)
	}
	defaults, err := coalesceAllValues(root)
	if err != nil {
		return err
	}
	if err := chartcommonutil.ValidateAgainstSchema(root, defaults.AsMap()); err != nil {
		return fmt.Errorf("validate generated chart schemas: %w", err)
	}
	return nil
}

// applySchemas places prepared schema bytes into the matching loaded chart.
func applySchemas(current, root *chartv2.Chart, rootDirectory string, schemas map[string][]byte) {
	directory := rootDirectory
	if current != root {
		relativePath, found := strings.CutPrefix(current.ChartFullPath(), root.ChartFullPath()+"/")
		if !found {
			return
		}
		directory = filepath.Join(rootDirectory, filepath.FromSlash(relativePath))
	}
	if schemaJSON, exists := schemas[directory]; exists {
		current.Schema = bytes.Clone(schemaJSON)
	}
	for _, dependency := range current.Dependencies() {
		applySchemas(dependency, root, rootDirectory, schemas)
	}
}
