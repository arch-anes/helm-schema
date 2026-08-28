package helmchart

// This file converts Helm chart files and contexts into analyzer inputs.

import (
	"bytes"
	"maps"
	"path"
	"slices"
	"sort"
	"strconv"
	"strings"

	"github.com/arch-anes/helm-schema/internal/analyze"
	chartv2 "helm.sh/helm/v4/pkg/chart/v2"
)

// loadTemplates converts chart files into analyzer inputs. It preserves the
// parse order that Helm uses for named-template replacement.
func loadTemplates(root *chartv2.Chart) ([]analyze.Template, error) {
	templates := make([]analyze.Template, 0)
	if err := appendTemplates(root, root.Name(), nil, &templates); err != nil {
		return nil, err
	}

	// Helm parses deeper chart paths first, then reverse lexical paths at the
	// same depth. Definition replacement depends on this order.
	sort.SliceStable(templates, func(i, j int) bool {
		leftDepth := strings.Count(templates[i].Name, "/")
		rightDepth := strings.Count(templates[j].Name, "/")
		if leftDepth != rightDepth {
			return leftDepth > rightDepth
		}
		return templates[i].Name > templates[j].Name
	})
	return templates, nil
}

// appendTemplates adds one chart scope and then adds all dependency scopes.
// Library charts contribute valid partial files but no entry points.
func appendTemplates(ch *chartv2.Chart, chartFullPath string, valuesPrefix []string, destination *[]analyze.Template) error {
	basePath := path.Join(chartFullPath, "templates")
	dependencies, err := bindDependencies(ch)
	if err != nil {
		return err
	}
	subcharts, err := subchartScopes(dependencies, valuesPrefix)
	if err != nil {
		return err
	}
	library := strings.EqualFold(ch.Metadata.Type, "library")
	for _, file := range ch.Templates {
		if file == nil {
			continue
		}
		partial := strings.HasPrefix(path.Base(file.Name), "_")
		if library && !partial {
			continue
		}
		*destination = append(*destination, analyze.Template{
			Name:         path.Join(chartFullPath, file.Name),
			Content:      bytes.Clone(file.Data),
			Entry:        !library && !partial,
			ValuesPrefix: slices.Clone(valuesPrefix),
			BasePath:     basePath,
			Context:      immutableContext(ch, path.Base(chartFullPath), len(valuesPrefix) == 0),
			Subcharts:    subcharts,
		})
	}
	appendValueTemplates(ch.Values, nil, nil, analyze.Template{
		ValuesPrefix: slices.Clone(valuesPrefix),
		BasePath:     basePath,
		Context:      immutableContext(ch, path.Base(chartFullPath), len(valuesPrefix) == 0),
		Subcharts:    subcharts,
	}, chartFullPath, destination)

	for _, dependency := range dependencies {
		dependencyPath := path.Join(chartFullPath, "charts", dependency.name)
		dependencyPrefix := append(slices.Clone(valuesPrefix), dependency.name)
		if err := appendTemplates(dependency.chart, dependencyPath, dependencyPrefix, destination); err != nil {
			return err
		}
	}
	return nil
}

// appendValueTemplates records template expressions in string defaults as
// deferred analyzer sources. Analysis parses a source only if it reaches tpl.
func appendValueTemplates(value any, valuePath []analyze.ValuePathStep, sourcePath []string, source analyze.Template, chartFullPath string, destination *[]analyze.Template) {
	switch typed := value.(type) {
	case string:
		if !strings.Contains(typed, "{{") {
			return
		}
		source.Name = path.Join(chartFullPath, "values.yaml"+jsonPointer(sourcePath))
		source.Content = []byte(typed)
		source.DeferredValuePath = append(valuePrefixPath(source.ValuesPrefix), valuePath...)
		*destination = append(*destination, source)
	case map[string]any:
		for _, name := range slices.Sorted(maps.Keys(typed)) {
			childPath := append(slices.Clone(valuePath), analyze.ValuePathStep{Property: name})
			appendValueTemplates(typed[name], childPath, appendValuePath(sourcePath, name), source, chartFullPath, destination)
		}
	case []any:
		for index, item := range typed {
			childPath := append(slices.Clone(valuePath), analyze.ValuePathStep{CollectionItem: true})
			appendValueTemplates(item, childPath, appendValuePath(sourcePath, strconv.Itoa(index)), source, chartFullPath, destination)
		}
	}
}

// valuePrefixPath converts a dependency prefix into analyzer path steps.
func valuePrefixPath(prefix []string) []analyze.ValuePathStep {
	result := make([]analyze.ValuePathStep, len(prefix))
	for index, name := range prefix {
		result[index].Property = name
	}
	return result
}

// subchartScopes builds the recursive context exposed through .Subcharts.
func subchartScopes(dependencies []dependencyBinding, valuesPrefix []string) (map[string]analyze.Scope, error) {
	if len(dependencies) == 0 {
		return nil, nil
	}
	result := make(map[string]analyze.Scope, len(dependencies))
	for _, dependency := range dependencies {
		childPrefix := appendValuePath(valuesPrefix, dependency.name)
		children, err := bindDependencies(dependency.chart)
		if err != nil {
			return nil, err
		}
		nested, err := subchartScopes(children, childPrefix)
		if err != nil {
			return nil, err
		}
		result[dependency.name] = analyze.Scope{
			ValuesPrefix: childPrefix,
			Context:      immutableContext(dependency.chart, dependency.name, false),
			Subcharts:    nested,
		}
	}
	return result, nil
}

// immutableContext copies stable .Chart fields into an analyzer context.
// renderedName accounts for a dependency alias.
func immutableContext(ch *chartv2.Chart, renderedName string, isRoot bool) map[string]any {
	metadata := ch.Metadata
	return map[string]any{
		"Chart": map[string]any{
			"Name":        renderedName,
			"Home":        metadata.Home,
			"Sources":     metadata.Sources,
			"Version":     metadata.Version,
			"Description": metadata.Description,
			"Keywords":    metadata.Keywords,
			"Icon":        metadata.Icon,
			"APIVersion":  metadata.APIVersion,
			"AppVersion":  metadata.AppVersion,
			"Deprecated":  metadata.Deprecated,
			"Annotations": metadata.Annotations,
			"KubeVersion": metadata.KubeVersion,
			"Type":        metadata.Type,
			"IsRoot":      isRoot,
		},
	}
}
