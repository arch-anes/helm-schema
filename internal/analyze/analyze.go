// Package analyze finds chart-value use in Helm template parse trees.
package analyze

// This file parses template sources, creates entry contexts, and starts tree
// evaluation. It also creates stable diagnostics.

import (
	"fmt"
	"slices"
	"sort"
	"strconv"
	"strings"
	"text/template/parse"
)

// maximumCallDepth limits recursive or deeply nested named-template calls.
const maximumCallDepth = 64

// entryPoint stores the root context for one executable template file.
type entryPoint struct {
	name         string
	valuesPrefix []string
	basePath     string
	context      map[string]any
	subcharts    map[string]Scope
}

// analyzer owns the parse trees, abstract state, usage result, and diagnostics
// for one Templates call.
type analyzer struct {
	trees             map[string]*parse.Tree
	deferredTemplates []Template
	usage             *Usage
	diagnostics       []Diagnostic
	err               error
	activeTrees       map[string]int
	finished          map[string]struct{}
	outputs           map[string]value
	finishedTPL       map[string]struct{}
	outputFrames      []outputFrame
	callDepth         int
	currentTree       *parse.Tree
}

// outputFrame records output actions from one named-template call. Opaque is
// true when a visited branch also writes literal text around those actions.
type outputFrame struct {
	values []value
	opaque bool
}

// Templates parses and analyzes Helm template sources.
func Templates(templates []Template) (*Usage, []Diagnostic, error) {
	trees := make(map[string]*parse.Tree)
	entries := make([]entryPoint, 0, len(templates))
	entryIndexes := make(map[string]int)
	deferredTemplates := make([]Template, 0)

	for _, source := range templates {
		if source.Name == "" {
			return nil, nil, fmt.Errorf("template name is empty")
		}
		if source.DeferredValuePath != nil {
			deferredTemplates = append(deferredTemplates, source)
			continue
		}
		parsed, err := parseTemplate(source.Name, source.Content)
		if err != nil {
			return nil, nil, fmt.Errorf("parse template %q: %w", source.Name, err)
		}
		for name, tree := range parsed {
			if old := trees[name]; old != nil && parse.IsEmptyTree(tree.Root) {
				continue
			}
			trees[name] = tree
		}
		if source.Entry {
			entry := entryPoint{
				name:         source.Name,
				valuesPrefix: slices.Clone(source.ValuesPrefix),
				basePath:     source.BasePath,
				context:      source.Context,
				subcharts:    source.Subcharts,
			}
			if index, exists := entryIndexes[source.Name]; exists {
				entries[index] = entry
			} else {
				entryIndexes[source.Name] = len(entries)
				entries = append(entries, entry)
			}
		}
	}

	a := &analyzer{
		trees:             trees,
		deferredTemplates: deferredTemplates,
		usage:             NewUsage(),
		activeTrees:       make(map[string]int),
		finished:          make(map[string]struct{}),
		outputs:           make(map[string]value),
		finishedTPL:       make(map[string]struct{}),
	}
	for _, entry := range entries {
		tree := trees[entry.name]
		if tree == nil || tree.Root == nil || parse.IsEmptyTree(tree.Root) {
			continue
		}
		root := entryRoot(entry)
		a.executeTree(tree, root, false, false)
		if a.err != nil {
			return nil, sortedDiagnostics(a.diagnostics), a.err
		}
	}

	return a.usage, sortedDiagnostics(a.diagnostics), nil
}

// parseTemplate parses one file without requiring registered Helm functions.
func parseTemplate(name string, content []byte) (map[string]*parse.Tree, error) {
	treeSet := make(map[string]*parse.Tree)
	tree := parse.New(name)
	tree.Mode = parse.SkipFuncCheck
	if _, err := tree.Parse(string(content), "", "", treeSet); err != nil {
		return nil, err
	}
	return treeSet, nil
}

// entryRoot builds the abstract root object for an executable template file.
func entryRoot(entry entryPoint) value {
	fields := scopeFields(Scope{
		ValuesPrefix: entry.valuesPrefix,
		Context:      entry.context,
		Subcharts:    entry.subcharts,
	})
	fields["Template"] = objectValue(map[string]value{
		"BasePath": constantValue(entry.basePath),
		"Name":     constantValue(entry.name),
	})
	return objectValue(fields)
}

// scopeValue converts one dependency scope into an abstract object.
func scopeValue(scope Scope) value {
	return objectValue(scopeFields(scope))
}

// scopeFields creates .Values, .Subcharts, and immutable context fields.
func scopeFields(scope Scope) map[string]value {
	fields := make(map[string]value, len(scope.Context)+2)
	for name, immutable := range scope.Context {
		fields[name] = immutableValue(immutable)
	}
	fields["Values"] = referenceValue(referenceForProperties(scope.ValuesPrefix...))
	subcharts := make(map[string]value, len(scope.Subcharts))
	for name, child := range scope.Subcharts {
		subcharts[name] = scopeValue(child)
	}
	fields["Subcharts"] = objectValue(subcharts)
	return fields
}

// immutableValue converts stable scalar, map, and list data into abstract
// values. Unsupported Go values become unknown values without origins.
func immutableValue(input any) value {
	switch typed := input.(type) {
	case map[string]any:
		fields := make(map[string]value, len(typed))
		for name, child := range typed {
			fields[name] = immutableValue(child)
		}
		return objectValue(fields)
	case map[string]string:
		fields := make(map[string]value, len(typed))
		for name, child := range typed {
			fields[name] = constantValue(child)
		}
		return objectValue(fields)
	case []any:
		elements := make([]value, len(typed))
		for index, child := range typed {
			elements[index] = immutableValue(child)
		}
		return listValue(elements)
	case []string:
		elements := make([]value, len(typed))
		for index, child := range typed {
			elements[index] = constantValue(child)
		}
		return listValue(elements)
	case nil, bool, string, int, int64, uint64, float64:
		return constantValue(typed)
	default:
		return unknownValue()
	}
}

// addDiagnostic records a message and the current parse-tree location.
func (a *analyzer) addDiagnostic(node parse.Node, message string) {
	diagnostic := Diagnostic{Message: message}
	if a.currentTree != nil {
		diagnostic.Template = a.currentTree.ParseName
		if diagnostic.Template == "" {
			diagnostic.Template = a.currentTree.Name
		}
	}
	if node != nil && a.currentTree != nil {
		location, _ := a.currentTree.ErrorContext(node)
		diagnostic.Line, diagnostic.Column = parseLocation(location)
	}
	a.diagnostics = append(a.diagnostics, diagnostic)
}

// sortedDiagnostics returns stable diagnostics and removes exact duplicates.
func sortedDiagnostics(diagnostics []Diagnostic) []Diagnostic {
	result := slices.Clone(diagnostics)
	sort.SliceStable(result, func(i, j int) bool {
		if result[i].Template != result[j].Template {
			return result[i].Template < result[j].Template
		}
		if result[i].Line != result[j].Line {
			return result[i].Line < result[j].Line
		}
		if result[i].Column != result[j].Column {
			return result[i].Column < result[j].Column
		}
		return result[i].Message < result[j].Message
	})
	unique := result[:0]
	for _, diagnostic := range result {
		if len(unique) > 0 && unique[len(unique)-1] == diagnostic {
			continue
		}
		unique = append(unique, diagnostic)
	}
	return unique
}

// parseLocation extracts line and column numbers from a Go template location.
func parseLocation(location string) (line, column int) {
	columnSeparator := strings.LastIndexByte(location, ':')
	if columnSeparator < 0 {
		return 0, 0
	}
	lineSeparator := strings.LastIndexByte(location[:columnSeparator], ':')
	if lineSeparator < 0 {
		return 0, 0
	}
	line, lineErr := strconv.Atoi(location[lineSeparator+1 : columnSeparator])
	column, columnErr := strconv.Atoi(location[columnSeparator+1:])
	if lineErr != nil || columnErr != nil {
		return 0, 0
	}
	return line, column
}
