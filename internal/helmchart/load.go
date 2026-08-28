// Package helmchart loads Helm charts for analysis, generation, and validation.
package helmchart

// This file loads chart data, maps dependency scopes, and records value flows
// that Helm metadata creates.

import (
	"errors"
	"fmt"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"sort"
	"strings"

	"github.com/arch-anes/helm-schema/internal/analyze"
	chartcommon "helm.sh/helm/v4/pkg/chart/common"
	chartcommonutil "helm.sh/helm/v4/pkg/chart/common/util"
	chartarchive "helm.sh/helm/v4/pkg/chart/loader/archive"
	chartv2 "helm.sh/helm/v4/pkg/chart/v2"
	chartv2loader "helm.sh/helm/v4/pkg/chart/v2/loader"
	chartv2util "helm.sh/helm/v4/pkg/chart/v2/util"
)

// Data contains the chart input needed for analysis and schema generation.
// Scopes lists physical schema targets. Defaults contains Helm's merged values.
// Descriptions uses JSON pointers. Templates contains all analyzer inputs.
// MetadataUsage and ValueFlows describe values Helm reads or copies outside
// templates. ExplicitNullDefaults contains paths from uncoalesced values files.
type Data struct {
	Scopes               []ChartScope
	Defaults             map[string]any
	Descriptions         map[string]string
	Templates            []analyze.Template
	MetadataUsage        *analyze.Usage
	ValueFlows           []analyze.ValueFlow
	ExplicitNullDefaults [][]string
}

// SchemaData contains defaults and annotations rebased to one chart scope.
// Description pointers and null-default paths are relative to that scope.
type SchemaData struct {
	Defaults             map[string]any
	Descriptions         map[string]string
	ExplicitNullDefaults [][]string
}

// ChartScope identifies one absolute chart directory and every root-relative
// values path that Helm validates against its schema. Multiple paths mean that
// dependency aliases share the same directory.
type ChartScope struct {
	Directory      string
	ValuesPrefixes [][]string
}

// Load reads an unpacked Helm chart and its local dependencies.
//
// Scope directories are cleaned absolute paths. Defaults use Helm's dependency
// and value coalescing rules. Analysis includes disabled local dependencies
// because a user-supplied value can enable them later.
func Load(chartPath string) (*Data, error) {
	absolutePath, err := chartDirectory(chartPath)
	if err != nil {
		return nil, err
	}

	analysisChart, err := loadChartForGeneration(absolutePath)
	if err != nil {
		return nil, fmt.Errorf("load chart %q: %w", absolutePath, err)
	}
	if strings.EqualFold(analysisChart.Metadata.Type, "library") {
		return nil, fmt.Errorf("chart %q is a library chart and has no standalone values scope", analysisChart.Name())
	}
	scopes, err := chartScopes(analysisChart, absolutePath)
	if err != nil {
		return nil, err
	}

	templates, err := loadTemplates(analysisChart)
	if err != nil {
		return nil, err
	}
	descriptions, err := loadDescriptions(analysisChart)
	if err != nil {
		return nil, fmt.Errorf("load value descriptions for chart %q: %w", analysisChart.Name(), err)
	}
	metadataUsage, valueFlows, err := loadMetadataUsage(analysisChart)
	if err != nil {
		return nil, err
	}

	// Dependency processing mutates the chart and removes dependencies disabled
	// by defaults. Use a fresh chart so static analysis still sees their files.
	defaultsChart, err := loadChartForGeneration(absolutePath)
	if err != nil {
		return nil, fmt.Errorf("reload chart %q for value coalescing: %w", absolutePath, err)
	}
	defaults, err := coalesceAllValues(defaultsChart)
	if err != nil {
		return nil, err
	}
	nullDefaults, err := collectNullDefaults(analysisChart)
	if err != nil {
		return nil, err
	}
	defaultValues := defaults.AsMap()
	for _, valuePath := range nullDefaults {
		restoreAbsentNull(defaultValues, valuePath)
	}

	return &Data{
		Scopes:               scopes,
		Defaults:             defaultValues,
		Descriptions:         descriptions,
		Templates:            templates,
		MetadataUsage:        metadataUsage,
		ValueFlows:           valueFlows,
		ExplicitNullDefaults: nullDefaults,
	}, nil
}

// loadChartForGeneration loads a chart while allowing replacement of an old
// unpacked schema that exceeds Helm's chart-file size limit.
func loadChartForGeneration(absolutePath string) (*chartv2.Chart, error) {
	loaded, err := chartv2loader.Load(absolutePath)
	if err == nil || !hasOversizedUnpackedSchema(absolutePath) {
		return loaded, err
	}

	temporary, temporaryErr := os.MkdirTemp("", "helm-schema-load-*")
	if temporaryErr != nil {
		return nil, fmt.Errorf("prepare chart copy without old schemas: %w", temporaryErr)
	}
	defer os.RemoveAll(temporary)
	if copyErr := os.CopyFS(temporary, os.DirFS(absolutePath)); copyErr != nil {
		return nil, fmt.Errorf("copy chart without old schemas: %w", copyErr)
	}
	if removeErr := removeUnpackedSchemas(temporary); removeErr != nil {
		return nil, fmt.Errorf("remove old schemas from chart copy: %w", removeErr)
	}
	return chartv2loader.Load(temporary)
}

// hasOversizedUnpackedSchema reports whether Helm's directory loader rejects
// at least one replaceable values.schema.json file because of its size.
func hasOversizedUnpackedSchema(chartPath string) bool {
	found := false
	_ = filepath.WalkDir(chartPath, func(path string, entry fs.DirEntry, err error) error {
		if err != nil || entry.IsDir() || entry.Name() != "values.schema.json" {
			return nil
		}
		info, infoErr := entry.Info()
		if infoErr == nil && info.Size() > chartarchive.MaxDecompressedFileSize {
			found = true
			return fs.SkipAll
		}
		return nil
	})
	return found
}

// removeUnpackedSchemas removes replaceable schema files from a temporary
// chart copy. Schemas inside dependency archives remain active.
func removeUnpackedSchemas(chartPath string) error {
	return filepath.WalkDir(chartPath, func(path string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if entry.IsDir() || entry.Name() != "values.schema.json" {
			return nil
		}
		return os.Remove(path)
	})
}

// coalesceAllValues processes every local dependency and returns the complete
// default values tree. It ignores default condition and tag filters because a
// user override can enable each dependency.
func coalesceAllValues(ch *chartv2.Chart) (chartcommon.Values, error) {
	removeDependencyFilters(ch)
	if err := chartv2util.ProcessDependencies(ch, chartcommon.Values{}); err != nil {
		return nil, fmt.Errorf("process dependencies for chart %q: %w", ch.Name(), err)
	}
	values, err := chartcommonutil.CoalesceValues(ch, map[string]any{})
	if err != nil {
		return nil, fmt.Errorf("coalesce defaults for chart %q: %w", ch.Name(), err)
	}
	return values, nil
}

// chartScopes returns the selected chart and each unpacked dependency chart.
// Dependencies come before parents so callers can write them in that order.
func chartScopes(root *chartv2.Chart, absolutePath string) ([]ChartScope, error) {
	rootChartPath := root.ChartFullPath()
	scopes := make([]ChartScope, 0)
	scopeIndexes := make(map[string]int)
	var appendDependencies func(*chartv2.Chart, []string) error
	appendDependencies = func(parent *chartv2.Chart, parentPrefix []string) error {
		bindings, err := bindDependencies(parent)
		if err != nil {
			return err
		}
		for _, binding := range bindings {
			dependency := binding.chart
			dependencyPrefix := appendValuePath(parentPrefix, binding.name)
			if err := appendDependencies(dependency, dependencyPrefix); err != nil {
				return err
			}

			relativePath, found := strings.CutPrefix(dependency.ChartFullPath(), rootChartPath+"/")
			if !found {
				return fmt.Errorf("dependency chart path %q is outside root chart %q", dependency.ChartFullPath(), rootChartPath)
			}
			directory := filepath.Join(absolutePath, filepath.FromSlash(relativePath))
			info, err := os.Stat(directory)
			if err != nil {
				if errors.Is(err, os.ErrNotExist) && len(dependency.Schema) == 0 {
					continue
				}
				if errors.Is(err, os.ErrNotExist) {
					return fmt.Errorf("dependency %q has a schema inside an archive; unpack it before generation", dependency.ChartFullPath())
				}
				return fmt.Errorf("inspect dependency chart path %q: %w", directory, err)
			}
			if !info.IsDir() {
				return fmt.Errorf("dependency chart path %q is not a directory", directory)
			}
			if index, exists := scopeIndexes[directory]; exists {
				scopes[index].ValuesPrefixes = append(scopes[index].ValuesPrefixes, dependencyPrefix)
				continue
			}
			scopeIndexes[directory] = len(scopes)
			scopes = append(scopes, ChartScope{Directory: directory, ValuesPrefixes: [][]string{dependencyPrefix}})
		}
		return nil
	}
	if err := appendDependencies(root, nil); err != nil {
		return nil, err
	}
	return append(scopes, ChartScope{Directory: absolutePath, ValuesPrefixes: [][]string{nil}}), nil
}

// ForScope selects effective defaults and rebases annotations to one chart's
// local .Values path.
func (data *Data) ForScope(valuesPrefix []string) (SchemaData, error) {
	var current any = data.Defaults
	for _, name := range valuesPrefix {
		object, ok := current.(map[string]any)
		if !ok {
			return SchemaData{}, fmt.Errorf("values path %q is not an object", jsonPointer(valuesPrefix))
		}
		var exists bool
		current, exists = object[name]
		if !exists {
			current = map[string]any{}
		}
	}
	defaults, ok := current.(map[string]any)
	if !ok {
		return SchemaData{}, fmt.Errorf("values path %q is not an object", jsonPointer(valuesPrefix))
	}

	prefixPointer := jsonPointer(valuesPrefix)
	descriptions := make(map[string]string)
	for pointer, description := range data.Descriptions {
		switch {
		case pointer == prefixPointer:
			descriptions[""] = description
		case strings.HasPrefix(pointer, prefixPointer+"/"):
			descriptions[strings.TrimPrefix(pointer, prefixPointer)] = description
		}
	}
	nullDefaults := make([][]string, 0)
	for _, valuePath := range data.ExplicitNullDefaults {
		if len(valuePath) < len(valuesPrefix) || !slices.Equal(valuePath[:len(valuesPrefix)], valuesPrefix) {
			continue
		}
		nullDefaults = append(nullDefaults, slices.Clone(valuePath[len(valuesPrefix):]))
	}
	return SchemaData{
		Defaults:             defaults,
		Descriptions:         descriptions,
		ExplicitNullDefaults: nullDefaults,
	}, nil
}

// chartDirectory resolves and validates one unpacked chart directory.
func chartDirectory(chartPath string) (string, error) {
	absolutePath, err := filepath.Abs(chartPath)
	if err != nil {
		return "", fmt.Errorf("resolve chart path %q: %w", chartPath, err)
	}
	absolutePath = filepath.Clean(absolutePath)

	info, err := os.Stat(absolutePath)
	if err != nil {
		return "", fmt.Errorf("inspect chart path %q: %w", absolutePath, err)
	}
	if !info.IsDir() {
		return "", fmt.Errorf("chart path %q is not a directory", absolutePath)
	}
	return absolutePath, nil
}

// collectNullDefaults returns effective paths that are explicitly null in a
// values file. Parent values take precedence over dependency defaults.
func collectNullDefaults(root *chartv2.Chart) ([][]string, error) {
	paths := make([][]string, 0)
	if err := collectChartNulls(root, nil, nil, &paths); err != nil {
		return nil, err
	}
	sort.Slice(paths, func(i, j int) bool {
		return jsonPointer(paths[i]) < jsonPointer(paths[j])
	})
	return paths, nil
}

// collectChartNulls records nulls from one chart and then visits its
// dependencies with the applicable parent overrides.
func collectChartNulls(ch *chartv2.Chart, prefix []string, overrides map[string]any, paths *[][]string) error {
	collectMapNulls(ch.Values, overrides, prefix, paths)

	bindings, err := bindDependencies(ch)
	if err != nil {
		return err
	}
	for _, binding := range bindings {
		childOverrides, blocked := dependencyOverrides(ch.Values, overrides, binding.name)
		if blocked {
			continue
		}
		childPrefix := appendValuePath(prefix, binding.name)
		if err := collectChartNulls(binding.chart, childPrefix, childOverrides, paths); err != nil {
			return err
		}
	}
	return nil
}

// collectMapNulls records null values that a higher-priority values map does
// not replace.
func collectMapNulls(raw, overrides map[string]any, prefix []string, paths *[][]string) {
	for name, rawValue := range raw {
		overrideValue, overridden := overrides[name]
		if rawValue == nil {
			if !overridden {
				*paths = append(*paths, appendValuePath(prefix, name))
			}
			continue
		}

		rawObject, rawIsObject := rawValue.(map[string]any)
		if !rawIsObject {
			continue
		}
		if !overridden {
			collectMapNulls(rawObject, nil, appendValuePath(prefix, name), paths)
			continue
		}
		overrideObject, ok := overrideValue.(map[string]any)
		if ok {
			collectMapNulls(rawObject, overrideObject, appendValuePath(prefix, name), paths)
		}
	}
}

// dependencyOverrides combines direct dependency values with inherited
// parent values. The inherited values have higher priority.
func dependencyOverrides(local, inherited map[string]any, name string) (map[string]any, bool) {
	localValue, localExists := local[name]
	inheritedValue, inheritedExists := inherited[name]

	if inheritedExists {
		inheritedObject, ok := inheritedValue.(map[string]any)
		if !ok {
			return nil, true
		}
		localObject, _ := localValue.(map[string]any)
		return mergeValueMaps(localObject, inheritedObject), false
	}
	if !localExists {
		return nil, false
	}
	localObject, ok := localValue.(map[string]any)
	return localObject, !ok
}

// mergeValueMaps copies lower-priority values and replaces them with higher-
// priority values. It recursively combines object values.
func mergeValueMaps(lower, higher map[string]any) map[string]any {
	merged := maps.Clone(lower)
	if merged == nil {
		merged = make(map[string]any, len(higher))
	}
	for name, higherValue := range higher {
		lowerObject, lowerIsObject := merged[name].(map[string]any)
		higherObject, higherIsObject := higherValue.(map[string]any)
		if lowerIsObject && higherIsObject {
			merged[name] = mergeValueMaps(lowerObject, higherObject)
			continue
		}
		merged[name] = higherValue
	}
	return merged
}

// restoreAbsentNull adds a null marker when coalescing removed the path. The
// schema builder uses these markers to accept raw and coalesced values.
func restoreAbsentNull(defaults map[string]any, valuePath []string) {
	for index, name := range valuePath {
		if index == len(valuePath)-1 {
			if _, exists := defaults[name]; !exists {
				defaults[name] = nil
			}
			return
		}
		nested, ok := defaults[name].(map[string]any)
		if !ok {
			return
		}
		defaults = nested
	}
}

// dependencyBinding pairs one loaded dependency with its alias or chart name.
type dependencyBinding struct {
	chart      *chartv2.Chart
	name       string
	dependency *chartv2.Dependency
}

// bindDependencies matches each declared dependency with a loaded local chart.
// The returned name is the alias when Chart.yaml declares one.
func bindDependencies(ch *chartv2.Chart) ([]dependencyBinding, error) {
	loaded := ch.Dependencies()
	matched := make([]bool, len(loaded))
	bindings := make([]dependencyBinding, 0, len(loaded))

	for _, declared := range ch.Metadata.Dependencies {
		if declared == nil {
			continue
		}
		match := -1
		nameFound := false
		for index, candidate := range loaded {
			if candidate == nil || candidate.Metadata == nil || candidate.Name() != declared.Name {
				continue
			}
			nameFound = true
			if chartv2util.IsCompatibleRange(declared.Version, candidate.Metadata.Version) {
				match = index
				break
			}
		}

		if match < 0 {
			if nameFound {
				return nil, fmt.Errorf("chart %q has no local dependency %q matching version %q", ch.Name(), declared.Name, declared.Version)
			}
			return nil, fmt.Errorf("chart %q declares dependency %q, but it is missing from charts/", ch.Name(), declared.Name)
		}

		matched[match] = true
		name := declared.Name
		if declared.Alias != "" {
			name = declared.Alias
		}
		bindings = append(bindings, dependencyBinding{chart: loaded[match], name: name, dependency: declared})
	}

	// Helm also loads charts present in charts/ but absent from Chart.yaml.
	undeclared := make([]dependencyBinding, 0)
	for index, dependency := range loaded {
		if matched[index] || dependency == nil {
			continue
		}
		undeclared = append(undeclared, dependencyBinding{chart: dependency, name: dependency.Name()})
	}
	sort.SliceStable(undeclared, func(i, j int) bool {
		if undeclared[i].name != undeclared[j].name {
			return undeclared[i].name < undeclared[j].name
		}
		return undeclared[i].chart.Metadata.Version < undeclared[j].chart.Metadata.Version
	})
	bindings = append(bindings, undeclared...)
	return bindings, nil
}

// loadMetadataUsage records values that Helm reads outside template execution.
func loadMetadataUsage(root *chartv2.Chart) (*analyze.Usage, []analyze.ValueFlow, error) {
	usage := analyze.NewUsage()
	flows := make([]analyze.ValueFlow, 0)
	if err := appendMetadataUsage(root, nil, usage, &flows); err != nil {
		return nil, nil, err
	}
	return usage, flows, nil
}

// appendMetadataUsage records dependency conditions, tags, imports, and global
// value copies for one chart scope.
func appendMetadataUsage(ch *chartv2.Chart, valuesPrefix []string, usage *analyze.Usage, flows *[]analyze.ValueFlow) error {
	bindings, err := bindDependencies(ch)
	if err != nil {
		return err
	}
	for _, binding := range bindings {
		childPrefix := appendValuePath(valuesPrefix, binding.name)
		*flows = append(*flows, analyze.ValueFlow{
			Source:      appendValuePath(valuesPrefix, "global"),
			Destination: appendValuePath(childPrefix, "global"),
		})

		if dependency := binding.dependency; dependency != nil {
			for condition := range strings.SplitSeq(strings.TrimSpace(dependency.Condition), ",") {
				if condition == "" {
					continue
				}
				usage.MarkPath(append(valuesPrefixCopy(valuesPrefix), strings.Split(condition, ".")...)...)
			}
			for _, tag := range dependency.Tags {
				usage.MarkPath(append(valuesPrefixCopy(valuesPrefix), "tags", tag)...)
			}
			for _, imported := range dependency.ImportValues {
				source, destination, ok := importValuePaths(imported)
				if !ok {
					continue
				}
				*flows = append(*flows, analyze.ValueFlow{
					Source:      appendHelmPath(childPrefix, source),
					Destination: appendHelmPath(valuesPrefix, destination),
				})
			}
		}

		if err := appendMetadataUsage(binding.chart, childPrefix, usage, flows); err != nil {
			return err
		}
	}
	return nil
}

// importValuePaths converts one import-values entry into child and parent
// paths. Invalid entry shapes return ok=false.
func importValuePaths(value any) (source, destination string, ok bool) {
	switch typed := value.(type) {
	case string:
		return "exports." + typed, ".", true
	case map[string]any:
		return fmt.Sprint(typed["child"]), fmt.Sprint(typed["parent"]), true
	case map[string]string:
		return typed["child"], typed["parent"], true
	default:
		return "", "", false
	}
}

// appendHelmPath appends a dotted Helm metadata path to a values prefix.
func appendHelmPath(prefix []string, dotted string) []string {
	if dotted == "." {
		return valuesPrefixCopy(prefix)
	}
	return append(valuesPrefixCopy(prefix), strings.Split(dotted, ".")...)
}

// appendValuePath returns a copy of prefix with one additional property.
func appendValuePath(prefix []string, name string) []string {
	return append(valuesPrefixCopy(prefix), name)
}

// valuesPrefixCopy returns a copy that callers can extend without aliasing the
// source slice.
func valuesPrefixCopy(prefix []string) []string {
	return slices.Clone(prefix)
}

// removeDependencyFilters makes all local dependencies available during
// default coalescing. Users can enable a disabled dependency with an override.
func removeDependencyFilters(ch *chartv2.Chart) {
	if ch == nil || ch.Metadata == nil {
		return
	}
	for _, dependency := range ch.Metadata.Dependencies {
		if dependency == nil {
			continue
		}
		dependency.Condition = ""
		dependency.Tags = nil
	}
	for _, dependency := range ch.Dependencies() {
		removeDependencyFilters(dependency)
	}
}
