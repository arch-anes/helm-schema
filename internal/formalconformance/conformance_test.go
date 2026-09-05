// Package formalconformance compares production analyzer results with the
// executable Lean reference model.
package formalconformance

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/arch-anes/helm-schema/internal/analyze"
	chartschema "github.com/arch-anes/helm-schema/internal/schema"
	chartcommon "helm.sh/helm/v4/pkg/chart/common"
	chartcommonutil "helm.sh/helm/v4/pkg/chart/common/util"
)

// wireSegment is one path step in the versioned Go-to-Lean protocol.
type wireSegment struct {
	Kind string `json:"kind"`
	Name string `json:"name,omitempty"`
}

// wireOperation is one behavior class understood by the Lean analyzer.
type wireOperation struct {
	Kind   string        `json:"kind"`
	Path   []wireSegment `json:"path"`
	Name   string        `json:"name,omitempty"`
	Names  []string      `json:"names,omitempty"`
	Mode   string        `json:"mode,omitempty"`
	Reason string        `json:"reason,omitempty"`
}

// wireUsageProperty is one named child in the raw recursive usage protocol.
type wireUsageProperty struct {
	Name  string    `json:"name"`
	Usage wireUsage `json:"usage"`
}

// wireUsage copies the production analyzer tree without deriving policy
// decisions. Pointer fields preserve the difference between absent and present
// empty nodes.
type wireUsage struct {
	Read         bool                `json:"read"`
	Exact        bool                `json:"exact"`
	AllowUnknown bool                `json:"allowUnknown"`
	Open         bool                `json:"open"`
	Iterated     bool                `json:"iterated"`
	Properties   []wireUsageProperty `json:"properties"`
	Additional   *wireUsage          `json:"additional"`
	Items        *wireUsage          `json:"items"`
	Elements     *wireUsage          `json:"elements"`
}

// wireCase connects one real template with its normalized formal operations.
type wireCase struct {
	Name       string          `json:"name"`
	Operations []wireOperation `json:"operations"`
	Usage      *wireUsage      `json:"usage"`
}

// wireValueFlow is one dependency or global-value prefix copy.
type wireValueFlow struct {
	Source      []string `json:"source"`
	Destination []string `json:"destination"`
}

// wireFlowCase compares production propagation with the executable Lean
// value-flow model.
type wireFlowCase struct {
	Name   string          `json:"name"`
	Before *wireUsage      `json:"before"`
	Flows  []wireValueFlow `json:"flows"`
	After  *wireUsage      `json:"after"`
}

// wireFunctionOperation is one row of the complete production function
// matrix. Lean independently lowers the class and checks this operation name.
type wireFunctionOperation struct {
	Name     string `json:"name"`
	Class    string `json:"class"`
	Lowering string `json:"lowering"`
}

// wireBoundary compares the exported Go decision with the Lean definition.
type wireBoundary struct {
	Name     string          `json:"name"`
	Defaults []wireJSONValue `json:"defaults"`
	Usage    *wireUsage      `json:"usage"`
	GoAllows bool            `json:"goAllows"`
}

// wireBoundaryInput is the boundary part of one supported core policy input.
type wireBoundaryInput struct {
	Defaults      []wireJSONValue `json:"defaults"`
	Usage         *wireUsage      `json:"usage"`
	InheritedOpen bool            `json:"inheritedOpen"`
}

// wireScalarValue is one scalar value in the semantic schema protocol.
type wireScalarValue struct {
	Kind  string `json:"kind"`
	Value any    `json:"value,omitempty"`
}

// wireJSONProperty is one named property in a recursive JSON value.
type wireJSONProperty struct {
	Name  string        `json:"name"`
	Value wireJSONValue `json:"value"`
}

// wireJSONValue represents constants of every JSON shape.
type wireJSONValue struct {
	Kind       string             `json:"kind"`
	Value      any                `json:"value,omitempty"`
	Items      []wireJSONValue    `json:"items"`
	Properties []wireJSONProperty `json:"properties"`
}

// wireValueProperty describes one recursive compiled value in the formal
// adapter input.
type wireValueProperty struct {
	Name          string              `json:"name"`
	Kind          string              `json:"kind"`
	Default       wireScalarValue     `json:"default"`
	Fixed         *wireJSONValue      `json:"fixed,omitempty"`
	Type          string              `json:"type,omitempty"`
	DirectUsage   bool                `json:"directUsage"`
	InheritedOpen bool                `json:"inheritedOpen"`
	ExplicitNull  bool                `json:"explicitNull"`
	Properties    []wireValueProperty `json:"properties"`
	Additional    *wireValueProperty  `json:"additional"`
	Items         *wireValueProperty  `json:"items,omitempty"`
	Alternatives  []wireValueProperty `json:"alternatives,omitempty"`
	Constraints   []wireValueProperty `json:"constraints,omitempty"`
	Boundary      wireBoundaryInput   `json:"boundary"`
}

// wireCoreInput is the currently supported production policy fragment.
type wireCoreInput struct {
	Properties []wireValueProperty `json:"properties"`
	Additional *wireValueProperty  `json:"additional"`
	Boundary   wireBoundaryInput   `json:"boundary"`
}

// wireSchemaProperty is one named property in a semantic object schema.
type wireSchemaProperty struct {
	Name   string             `json:"name"`
	Schema wireSemanticSchema `json:"schema"`
}

// wireSemanticSchema omits annotations and JSON Schema syntax that do not
// change acceptance.
type wireSemanticSchema struct {
	Kind         string               `json:"kind"`
	Value        *wireJSONValue       `json:"value,omitempty"`
	Type         string               `json:"type,omitempty"`
	Properties   []wireSchemaProperty `json:"properties"`
	Additional   *wireSemanticSchema  `json:"additional"`
	Items        *wireSemanticSchema  `json:"items,omitempty"`
	Alternatives []wireSemanticSchema `json:"alternatives,omitempty"`
	Constraints  []wireSemanticSchema `json:"constraints,omitempty"`
}

// wireSchemaCase compares one generated Go schema with a Lean core input.
type wireSchemaCase struct {
	Name     string             `json:"name"`
	Input    wireCoreInput      `json:"input"`
	GoSchema wireSemanticSchema `json:"goSchema"`
}

// wireValidationCase compares the executable Lean validator with Helm 4's
// Draft 7 validator for one schema and candidate value.
type wireValidationCase struct {
	Name        string             `json:"name"`
	Schema      wireSemanticSchema `json:"schema"`
	Value       wireJSONValue      `json:"value"`
	HelmAccepts bool               `json:"helmAccepts"`
}

// wireDocument is the complete input consumed by the Lean verifier.
type wireDocument struct {
	Version     int                     `json:"version"`
	Cases       []wireCase              `json:"cases"`
	Flows       []wireFlowCase          `json:"flows"`
	Functions   []wireFunctionOperation `json:"functions"`
	Boundaries  []wireBoundary          `json:"boundaries"`
	Schemas     []wireSchemaCase        `json:"schemas"`
	Validations []wireValidationCase    `json:"validations"`
}

// formalFixture states the lowering expected for one concrete Helm template.
// The production analyzer computes Usage; Lean computes Usage from Operations.
// diagnosticSubstring optionally checks the named production fallback.
type formalFixture struct {
	name                string
	template            string
	operations          []wireOperation
	diagnosticSubstring string
}

// boundaryFixture is one input for the exported Go root-boundary decision.
type boundaryFixture struct {
	name     string
	defaults map[string]any
	usage    *analyze.Usage
}

// schemaFixture is one input in the bounded production schema fragment.
type schemaFixture struct {
	name         string
	defaults     map[string]any
	usage        *analyze.Usage
	nullDefaults [][]string
	formalInput  *wireCoreInput
}

// validatorFixture supplies raw Draft 7 syntax and final root values directly
// to Helm. It tests the semantic model independently from schema generation.
type validatorFixture struct {
	name       string
	schema     map[string]any
	candidates []validatorCandidate
}

// generatedValidatorFixture compares production output with Helm validation
// independently from the structural CoreInput comparison.
type generatedValidatorFixture struct {
	name         string
	defaults     map[string]any
	usage        *analyze.Usage
	nullDefaults [][]string
	candidates   []validatorCandidate
}

// validatorCandidate is one named final values object and expected Helm input.
type validatorCandidate struct {
	name   string
	values map[string]any
}

// propertyPath creates a path from fixed property names.
func propertyPath(names ...string) []wireSegment {
	path := make([]wireSegment, len(names))
	for index, name := range names {
		path[index] = wireSegment{Kind: "property", Name: name}
	}
	return path
}

// pathWith returns a copy of path with one non-property segment appended.
func pathWith(path []wireSegment, kind string) []wireSegment {
	result := slices.Clone(path)
	return append(result, wireSegment{Kind: kind})
}

// rawUsage copies one recursive production usage node. It rejects nil named
// children because analyzer-created property entries are always concrete.
func rawUsage(source *analyze.Usage) (*wireUsage, error) {
	if source == nil {
		return nil, nil
	}
	result := &wireUsage{
		Read:         source.Read,
		Exact:        source.Exact,
		AllowUnknown: source.AllowUnknown,
		Open:         source.Open,
		Iterated:     source.Iterated,
	}
	propertyNames := make([]string, 0, len(source.Properties))
	for name := range source.Properties {
		propertyNames = append(propertyNames, name)
	}
	slices.Sort(propertyNames)
	result.Properties = make([]wireUsageProperty, 0, len(propertyNames))
	for _, name := range propertyNames {
		child, err := rawUsage(source.Properties[name])
		if err != nil {
			return nil, fmt.Errorf("property %q: %w", name, err)
		}
		if child == nil {
			return nil, fmt.Errorf("property %q has a nil usage node", name)
		}
		result.Properties = append(result.Properties, wireUsageProperty{
			Name: name, Usage: *child,
		})
	}
	var err error
	if result.Additional, err = rawUsage(source.Additional); err != nil {
		return nil, fmt.Errorf("additional usage: %w", err)
	}
	if result.Items, err = rawUsage(source.Items); err != nil {
		return nil, fmt.Errorf("item usage: %w", err)
	}
	if result.Elements, err = rawUsage(source.Elements); err != nil {
		return nil, fmt.Errorf("element usage: %w", err)
	}
	return result, nil
}

// boundaryDefaults converts direct defaults to canonical JSON values. The
// formal decision does not depend on property names, but sorting makes the
// protocol deterministic.
func boundaryDefaults(defaults map[string]any) ([]wireJSONValue, error) {
	names := make([]string, 0, len(defaults))
	for name := range defaults {
		names = append(names, name)
	}
	slices.Sort(names)

	result := make([]wireJSONValue, 0, len(names))
	for _, name := range names {
		value, err := jsonValue(defaults[name])
		if err != nil {
			return nil, fmt.Errorf("default %q: %w", name, err)
		}
		result = append(result, value)
	}
	return result, nil
}

// hasContainerUsage reports whether usage requires a shape below this value.
func hasContainerUsage(usage *analyze.Usage) bool {
	return usage != nil && (len(usage.Properties) > 0 || usage.Additional != nil ||
		usage.Items != nil || usage.Elements != nil || usage.Iterated)
}

// validateObjectUsage rejects shapes that the automatic raw-to-CoreInput test
// adapter does not derive yet. Explicit compiled fixtures cover these shapes.
func validateObjectUsage(defaults map[string]any, usage *analyze.Usage) error {
	if usage == nil {
		return nil
	}
	if usage.Items != nil || usage.Elements != nil || usage.Iterated {
		return fmt.Errorf("array or element usage is outside the formal fragment")
	}
	if usage.Additional != nil &&
		(len(defaults) > 0 || len(usage.Properties) > 0 ||
			hasContainerUsage(usage.Additional)) {
		return fmt.Errorf("dynamic entry contracts are outside the formal fragment")
	}
	return nil
}

// canonicalJSON applies the same standard-library JSON conversion used for
// schema constants. It also preserves exact decimal tokens as json.Number.
func canonicalJSON(value any) (any, error) {
	encoded, err := json.Marshal(value)
	if err != nil {
		return nil, err
	}
	decoder := json.NewDecoder(bytes.NewReader(encoded))
	decoder.UseNumber()
	var canonical any
	if err := decoder.Decode(&canonical); err != nil {
		return nil, err
	}
	return canonical, nil
}

// objectValue classifies maps with the same reflection rules as the
// production generator while retaining each child's original Go scalar type.
func objectValue(value any) (map[string]any, bool, error) {
	if value == nil {
		return nil, false, nil
	}
	reflected := reflect.ValueOf(value)
	for reflected.Kind() == reflect.Interface || reflected.Kind() == reflect.Pointer {
		if reflected.IsNil() {
			return nil, false, nil
		}
		reflected = reflected.Elem()
	}
	if reflected.Kind() != reflect.Map || reflected.IsNil() {
		return nil, false, nil
	}

	object := make(map[string]any, reflected.Len())
	iterator := reflected.MapRange()
	for iterator.Next() {
		key := iterator.Key()
		for key.Kind() == reflect.Interface {
			key = key.Elem()
		}
		if key.Kind() != reflect.String {
			return nil, false, fmt.Errorf("object key %v is not a string", iterator.Key().Interface())
		}
		object[key.String()] = iterator.Value().Interface()
	}
	return object, true, nil
}

// isJSONNull reports the nil forms that the production value inspector treats
// as JSON null, including typed nil pointers, maps, and slices stored in an
// interface.
func isJSONNull(value any) bool {
	if value == nil {
		return true
	}
	reflected := reflect.ValueOf(value)
	for reflected.Kind() == reflect.Interface || reflected.Kind() == reflect.Pointer {
		if reflected.IsNil() {
			return true
		}
		reflected = reflected.Elem()
	}
	return (reflected.Kind() == reflect.Map || reflected.Kind() == reflect.Slice) && reflected.IsNil()
}

// scalarValue converts one Go scalar into the formal protocol. It reports
// template-containing strings separately because Go does not infer their type.
func scalarValue(value any, exists bool) (wireScalarValue, error) {
	if !exists {
		return wireScalarValue{Kind: "missing"}, nil
	}
	if isJSONNull(value) {
		return wireScalarValue{Kind: "null"}, nil
	}
	if number, ok := value.(json.Number); ok {
		if strings.ContainsAny(number.String(), ".eE") {
			return wireScalarValue{Kind: "number", Value: number}, nil
		}
		return wireScalarValue{Kind: "integer", Value: number}, nil
	}

	reflected := reflect.ValueOf(value)
	for reflected.Kind() == reflect.Interface || reflected.Kind() == reflect.Pointer {
		if reflected.IsNil() {
			return wireScalarValue{Kind: "null"}, nil
		}
		reflected = reflected.Elem()
	}
	switch reflected.Kind() {
	case reflect.Bool:
		return wireScalarValue{Kind: "boolean", Value: reflected.Bool()}, nil
	case reflect.String:
		text := reflected.String()
		if strings.Contains(text, "{{") {
			return wireScalarValue{Kind: "templateString", Value: text}, nil
		}
		return wireScalarValue{Kind: "string", Value: text}, nil
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
		canonical, err := canonicalJSON(value)
		return wireScalarValue{Kind: "integer", Value: canonical}, err
	case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		canonical, err := canonicalJSON(value)
		return wireScalarValue{Kind: "integer", Value: canonical}, err
	case reflect.Float32, reflect.Float64:
		canonical, err := canonicalJSON(value)
		return wireScalarValue{Kind: "number", Value: canonical}, err
	default:
		return wireScalarValue{}, fmt.Errorf("unsupported formal scalar %T", value)
	}
}

// jsonValue converts one Go value into the complete formal JSON protocol.
func jsonValue(value any) (wireJSONValue, error) {
	canonical, err := canonicalJSON(value)
	if err != nil {
		return wireJSONValue{}, err
	}
	return canonicalWireJSONValue(canonical)
}

// canonicalWireJSONValue converts values returned by canonicalJSON into the
// recursive protocol. Canonical objects have unique string keys.
func canonicalWireJSONValue(value any) (wireJSONValue, error) {
	switch value := value.(type) {
	case nil:
		return wireJSONValue{Kind: "null"}, nil
	case bool:
		return wireJSONValue{Kind: "boolean", Value: value}, nil
	case string:
		return wireJSONValue{Kind: "string", Value: value}, nil
	case json.Number:
		return wireJSONValue{Kind: "number", Value: value}, nil
	case []any:
		items := make([]wireJSONValue, len(value))
		for index, rawItem := range value {
			item, err := canonicalWireJSONValue(rawItem)
			if err != nil {
				return wireJSONValue{}, fmt.Errorf("item %d: %w", index, err)
			}
			items[index] = item
		}
		return wireJSONValue{Kind: "array", Items: items}, nil
	case map[string]any:
		names := make([]string, 0, len(value))
		for name := range value {
			names = append(names, name)
		}
		slices.Sort(names)
		properties := make([]wireJSONProperty, 0, len(names))
		for _, name := range names {
			child, err := canonicalWireJSONValue(value[name])
			if err != nil {
				return wireJSONValue{}, fmt.Errorf("property %q: %w", name, err)
			}
			properties = append(properties, wireJSONProperty{Name: name, Value: child})
		}
		return wireJSONValue{Kind: "object", Properties: properties}, nil
	default:
		return wireJSONValue{}, fmt.Errorf("canonical JSON value has type %T", value)
	}
}

// nullPathNode stores explicit-null paths without repeated prefix scans.
type nullPathNode struct {
	explicit bool
	children map[string]*nullPathNode
}

// nullPathTree converts value paths into a recursive lookup tree.
func nullPathTree(paths [][]string) (*nullPathNode, error) {
	root := &nullPathNode{children: make(map[string]*nullPathNode)}
	for _, path := range paths {
		if len(path) == 0 {
			return nil, fmt.Errorf("an explicit-null path cannot be empty")
		}
		current := root
		for _, name := range path {
			child := current.children[name]
			if child == nil {
				child = &nullPathNode{children: make(map[string]*nullPathNode)}
				current.children[name] = child
			}
			current = child
		}
		current.explicit = true
	}
	return root, nil
}

// nullPathChild returns one child without requiring a non-nil parent.
func nullPathChild(parent *nullPathNode, name string) *nullPathNode {
	if parent == nil {
		return nil
	}
	return parent.children[name]
}

// valueProperty converts one value in the bounded scalar-and-object adapter.
func valueProperty(
	name string,
	value any,
	exists bool,
	usage *analyze.Usage,
	inheritedOpen bool,
	nulls *nullPathNode,
) (wireValueProperty, error) {
	explicitNull := nulls != nil && nulls.explicit
	objectDefaults, isObject, err := objectValue(value)
	if err != nil {
		return wireValueProperty{}, err
	}
	hasNullDescendant := nulls != nil && len(nulls.children) > 0
	if usage == nil && !inheritedOpen && exists && (!isObject || !hasNullDescendant) {
		fixed, err := jsonValue(value)
		if err != nil {
			return wireValueProperty{}, err
		}
		return wireValueProperty{
			Name: name, Kind: "fixed", Fixed: &fixed, ExplicitNull: explicitNull,
		}, nil
	}
	if !isObject {
		if hasContainerUsage(usage) {
			return wireValueProperty{}, fmt.Errorf(
				"container property %q has no supported object default", name,
			)
		}
		if nulls != nil && len(nulls.children) > 0 {
			return wireValueProperty{}, fmt.Errorf(
				"explicit-null path continues below scalar property %q", name,
			)
		}
		defaultValue, err := scalarValue(value, exists)
		if err != nil {
			return wireValueProperty{}, err
		}
		return wireValueProperty{
			Name: name, Kind: "leaf", Default: defaultValue,
			DirectUsage: usage != nil, InheritedOpen: inheritedOpen,
			ExplicitNull: explicitNull,
		}, nil
	}

	if usage == nil {
		usage = &analyze.Usage{}
	}
	if err := validateObjectUsage(objectDefaults, usage); err != nil {
		return wireValueProperty{}, err
	}
	open := inheritedOpen || usage.Open

	seen := make(map[string]struct{}, len(objectDefaults)+len(usage.Properties))
	for childName := range objectDefaults {
		seen[childName] = struct{}{}
	}
	for childName := range usage.Properties {
		seen[childName] = struct{}{}
	}
	names := make([]string, 0, len(seen))
	for childName := range seen {
		names = append(names, childName)
	}
	slices.Sort(names)

	properties := make([]wireValueProperty, 0, len(names))
	for _, childName := range names {
		childValue, childExists := objectDefaults[childName]
		child, err := valueProperty(
			childName,
			childValue,
			childExists,
			usage.Properties[childName],
			open,
			nullPathChild(nulls, childName),
		)
		if err != nil {
			return wireValueProperty{}, fmt.Errorf("property %q: %w", childName, err)
		}
		properties = append(properties, child)
	}
	boundaryUsage, err := rawUsage(usage)
	if err != nil {
		return wireValueProperty{}, fmt.Errorf("object usage: %w", err)
	}
	defaultValues, err := boundaryDefaults(objectDefaults)
	if err != nil {
		return wireValueProperty{}, fmt.Errorf("object defaults: %w", err)
	}
	return wireValueProperty{
		Name:         name,
		Kind:         "object",
		ExplicitNull: explicitNull,
		Properties:   properties,
		Boundary: wireBoundaryInput{
			Defaults:      defaultValues,
			Usage:         boundaryUsage,
			InheritedOpen: inheritedOpen,
		},
	}, nil
}

// coreInput converts the supported bounded Go inputs into the Lean policy input.
func coreInput(
	defaults map[string]any,
	usage *analyze.Usage,
	nullDefaults [][]string,
) (wireCoreInput, error) {
	if err := validateObjectUsage(defaults, usage); err != nil {
		return wireCoreInput{}, fmt.Errorf("root object: %w", err)
	}
	nulls, err := nullPathTree(nullDefaults)
	if err != nil {
		return wireCoreInput{}, err
	}

	propertyNames := make([]string, 0, len(defaults))
	seen := make(map[string]struct{}, len(defaults))
	for name := range defaults {
		seen[name] = struct{}{}
	}
	if usage != nil {
		for name := range usage.Properties {
			seen[name] = struct{}{}
		}
	}
	for name := range seen {
		propertyNames = append(propertyNames, name)
	}
	slices.Sort(propertyNames)

	properties := make([]wireValueProperty, 0, len(propertyNames))
	for _, name := range propertyNames {
		value, exists := defaults[name]
		var propertyUsage *analyze.Usage
		if usage != nil {
			propertyUsage = usage.Properties[name]
		}
		property, err := valueProperty(
			name,
			value,
			exists,
			propertyUsage,
			usage != nil && usage.Open,
			nullPathChild(nulls, name),
		)
		if err != nil {
			return wireCoreInput{}, fmt.Errorf("property %q: %w", name, err)
		}
		properties = append(properties, property)
	}

	rootUsage, err := rawUsage(usage)
	if err != nil {
		return wireCoreInput{}, fmt.Errorf("root usage: %w", err)
	}
	defaultValues, err := boundaryDefaults(defaults)
	if err != nil {
		return wireCoreInput{}, fmt.Errorf("root defaults: %w", err)
	}
	return wireCoreInput{
		Properties: properties,
		Boundary: wireBoundaryInput{
			Defaults: defaultValues,
			Usage:    rootUsage,
		},
	}, nil
}

// semanticConjunction returns the exact intersection of zero or more schema
// constraints without adding an unnecessary wrapper around one constraint.
func semanticConjunction(constraints []wireSemanticSchema) wireSemanticSchema {
	switch len(constraints) {
	case 0:
		return wireSemanticSchema{Kind: "any"}
	case 1:
		return constraints[0]
	default:
		return wireSemanticSchema{Kind: "allOf", Constraints: constraints}
	}
}

// schemaTypes parses the Draft 7 string-or-array representation of `type`.
func schemaTypes(document map[string]any) ([]string, bool, error) {
	raw, exists := document["type"]
	if !exists {
		return nil, false, nil
	}
	var names []string
	switch raw := raw.(type) {
	case string:
		names = []string{raw}
	case []any:
		if len(raw) == 0 {
			return nil, true, fmt.Errorf("schema type array is empty")
		}
		names = make([]string, len(raw))
		for index, value := range raw {
			name, ok := value.(string)
			if !ok {
				return nil, true, fmt.Errorf("schema type %d is %T", index, value)
			}
			names[index] = name
		}
	default:
		return nil, true, fmt.Errorf("schema type is %T", raw)
	}

	seen := make(map[string]struct{}, len(names))
	for _, name := range names {
		if _, duplicate := seen[name]; duplicate {
			return nil, true, fmt.Errorf("schema type %q is repeated", name)
		}
		seen[name] = struct{}{}
	}
	return names, true, nil
}

// normalizeObjectSchema converts the object-only keywords. Draft 7 permits
// unknown properties when additionalProperties is absent.
func normalizeObjectSchema(document map[string]any) (wireSemanticSchema, error) {
	var rawProperties map[string]any
	if raw, exists := document["properties"]; exists {
		var ok bool
		rawProperties, ok = raw.(map[string]any)
		if !ok {
			return wireSemanticSchema{}, fmt.Errorf("properties is %T", raw)
		}
	}
	propertyNames := make([]string, 0, len(rawProperties))
	for name := range rawProperties {
		propertyNames = append(propertyNames, name)
	}
	slices.Sort(propertyNames)
	properties := make([]wireSchemaProperty, 0, len(propertyNames))
	for _, name := range propertyNames {
		child, ok := rawProperties[name].(map[string]any)
		if !ok {
			return wireSemanticSchema{}, fmt.Errorf("property %q is %T", name, rawProperties[name])
		}
		normalized, err := normalizeSchema(child)
		if err != nil {
			return wireSemanticSchema{}, fmt.Errorf("property %q: %w", name, err)
		}
		properties = append(properties, wireSchemaProperty{Name: name, Schema: normalized})
	}

	additional := &wireSemanticSchema{Kind: "any"}
	if raw, exists := document["additionalProperties"]; exists {
		switch rule := raw.(type) {
		case bool:
			if !rule {
				additional = nil
			}
		case map[string]any:
			normalized, err := normalizeSchema(rule)
			if err != nil {
				return wireSemanticSchema{}, fmt.Errorf("additional properties: %w", err)
			}
			additional = &normalized
		default:
			return wireSemanticSchema{}, fmt.Errorf("additionalProperties is %T", raw)
		}
	}
	return wireSemanticSchema{
		Kind: "object", Properties: properties, Additional: additional,
	}, nil
}

// normalizeArraySchema converts the array-only keywords. Draft 7 treats an
// absent items keyword as an unrestricted item schema.
func normalizeArraySchema(document map[string]any) (wireSemanticSchema, error) {
	items := wireSemanticSchema{Kind: "any"}
	if raw, exists := document["items"]; exists {
		child, ok := raw.(map[string]any)
		if !ok {
			return wireSemanticSchema{}, fmt.Errorf("array items are %T", raw)
		}
		var err error
		items, err = normalizeSchema(child)
		if err != nil {
			return wireSemanticSchema{}, fmt.Errorf("array items: %w", err)
		}
	}
	return wireSemanticSchema{Kind: "array", Items: &items}, nil
}

// normalizeSchema removes annotations and converts every supported Draft 7
// validation keyword into the semantic schema language used by Lean. It
// rejects unknown keywords instead of silently weakening their constraints.
func normalizeSchema(document map[string]any) (wireSemanticSchema, error) {
	for keyword := range document {
		switch keyword {
		case "$schema", "description", "default", "const", "anyOf", "type",
			"properties", "items", "additionalProperties":
		default:
			return wireSemanticSchema{}, fmt.Errorf("unsupported schema keyword %q", keyword)
		}
	}

	constraints := make([]wireSemanticSchema, 0, 3)
	if constant, exists := document["const"]; exists {
		value, err := jsonValue(constant)
		if err != nil {
			return wireSemanticSchema{}, fmt.Errorf("constant: %w", err)
		}
		constraints = append(constraints, wireSemanticSchema{Kind: "constant", Value: &value})
	}

	types, hasTypes, err := schemaTypes(document)
	if err != nil {
		return wireSemanticSchema{}, err
	}
	if hasTypes {
		branches := make([]wireSemanticSchema, 0, len(types))
		hasObject := false
		hasArray := false
		for _, typeName := range types {
			var branch wireSemanticSchema
			switch typeName {
			case "object":
				hasObject = true
				branch, err = normalizeObjectSchema(document)
			case "array":
				hasArray = true
				branch, err = normalizeArraySchema(document)
			case "null", "boolean", "integer", "number", "string":
				branch = wireSemanticSchema{Kind: "typed", Type: typeName}
			default:
				return wireSemanticSchema{}, fmt.Errorf("unsupported schema type %q", typeName)
			}
			if err != nil {
				return wireSemanticSchema{}, err
			}
			branches = append(branches, branch)
		}
		if _, exists := document["properties"]; exists && !hasObject {
			return wireSemanticSchema{}, fmt.Errorf("properties requires object in schema type")
		}
		if _, exists := document["additionalProperties"]; exists && !hasObject {
			return wireSemanticSchema{}, fmt.Errorf("additionalProperties requires object in schema type")
		}
		if _, exists := document["items"]; exists && !hasArray {
			return wireSemanticSchema{}, fmt.Errorf("items requires array in schema type")
		}
		if len(branches) == 1 {
			constraints = append(constraints, branches[0])
		} else {
			constraints = append(constraints, wireSemanticSchema{
				Kind: "anyOf", Alternatives: branches,
			})
		}
	} else if _, properties := document["properties"]; properties {
		return wireSemanticSchema{}, fmt.Errorf("properties without type is outside the semantic subset")
	} else if _, additional := document["additionalProperties"]; additional {
		return wireSemanticSchema{}, fmt.Errorf("additionalProperties without type is outside the semantic subset")
	} else if _, items := document["items"]; items {
		return wireSemanticSchema{}, fmt.Errorf("items without type is outside the semantic subset")
	}

	if rawAlternatives, exists := document["anyOf"]; exists {
		items, ok := rawAlternatives.([]any)
		if !ok {
			return wireSemanticSchema{}, fmt.Errorf("anyOf is %T", rawAlternatives)
		}
		alternatives := make([]wireSemanticSchema, 0, len(items))
		for index, item := range items {
			child, ok := item.(map[string]any)
			if !ok {
				return wireSemanticSchema{}, fmt.Errorf("anyOf item %d is %T", index, item)
			}
			normalized, err := normalizeSchema(child)
			if err != nil {
				return wireSemanticSchema{}, fmt.Errorf("anyOf item %d: %w", index, err)
			}
			alternatives = append(alternatives, normalized)
		}
		constraints = append(constraints, wireSemanticSchema{
			Kind: "anyOf", Alternatives: alternatives,
		})
	}

	return semanticConjunction(constraints), nil
}

// generatedSemanticSchema runs the production generator and normalizes its
// validation rules for Lean comparison.
func generatedSemanticSchema(
	defaults map[string]any,
	usage *analyze.Usage,
	nullDefaults [][]string,
) (wireSemanticSchema, error) {
	generated, err := chartschema.Generate(defaults, nil, usage, nullDefaults...)
	if err != nil {
		return wireSemanticSchema{}, err
	}
	document, err := decodeSchemaDocument(generated)
	if err != nil {
		return wireSemanticSchema{}, err
	}
	return normalizeSchema(document)
}

// decodeSchemaDocument retains exact JSON numbers while decoding generated
// Draft 7 syntax.
func decodeSchemaDocument(schemaJSON []byte) (map[string]any, error) {
	decoder := json.NewDecoder(bytes.NewReader(schemaJSON))
	decoder.UseNumber()
	var document map[string]any
	if err := decoder.Decode(&document); err != nil {
		return nil, err
	}
	return document, nil
}

// helmAccepts validates one final values object with Helm 4. Validation
// failures are ordinary rejection; schema loading and compilation failures are
// conformance errors.
func helmAccepts(values map[string]any, schemaJSON []byte) (bool, error) {
	err := chartcommonutil.ValidateAgainstSingleSchema(
		chartcommon.Values(values), schemaJSON,
	)
	if err == nil {
		return true, nil
	}
	var validationError chartcommonutil.JSONSchemaValidationError
	if errors.As(err, &validationError) {
		return false, nil
	}
	return false, fmt.Errorf("Helm could not apply schema: %w", err)
}

// validationCase asks Helm and Lean to validate the same canonical schema and
// root value.
func validationCase(
	fixtureName string,
	candidate validatorCandidate,
	schemaDocument map[string]any,
) (wireValidationCase, error) {
	schemaJSON, err := json.Marshal(schemaDocument)
	if err != nil {
		return wireValidationCase{}, err
	}
	accepted, err := helmAccepts(candidate.values, schemaJSON)
	if err != nil {
		return wireValidationCase{}, err
	}
	semanticSchema, err := normalizeSchema(schemaDocument)
	if err != nil {
		return wireValidationCase{}, err
	}
	value, err := jsonValue(candidate.values)
	if err != nil {
		return wireValidationCase{}, err
	}
	return wireValidationCase{
		Name:        fixtureName + "/" + candidate.name,
		Schema:      semanticSchema,
		Value:       value,
		HelmAccepts: accepted,
	}, nil
}

// formalVerifier returns the executable supplied by `make verify`.
func formalVerifier(t *testing.T) string {
	t.Helper()
	verifier := os.Getenv("HELM_SCHEMA_FORMAL_VERIFY")
	if verifier == "" {
		t.Skip("formal verifier path is not set")
	}
	return verifier
}

// TestProductionMatchesLean compares the supported production behavior with
// Lean. Normal Go test runs do not require a Lean installation.
func TestProductionMatchesLean(t *testing.T) {
	verifier := formalVerifier(t)
	type namedKey string
	type namedObject map[namedKey]any
	type namedString string
	integerPointer := 3
	fractionPointer := 2.5
	var nilObject map[string]any
	var nilList []any
	var nilPointer *string

	fixtures := []formalFixture{
		{
			name:     "truth test reads a scalar",
			template: `{{ if .Values.feature.enabled }}enabled{{ end }}`,
			operations: []wireOperation{{
				Kind: "read", Path: propertyPath("feature", "enabled"),
			}},
		},
		{
			name:     "complete root serialization",
			template: `{{ toYaml .Values }}`,
			operations: []wireOperation{{
				Kind: "complete", Path: []wireSegment{},
			}},
		},
		{
			name:     "literal index selects a fixed property",
			template: `{{ index .Values.settings "name" }}`,
			operations: []wireOperation{{
				Kind: "complete", Path: propertyPath("settings", "name"),
			}},
		},
		{
			name:     "unused fixed selection creates no usage",
			template: `{{- $unused := index .Values.settings "name" -}}`,
			operations: []wireOperation{{
				Kind: "selectFixed", Path: propertyPath("settings"), Name: "name",
			}},
		},
		{
			name:     "unused dynamic selection reads only its key",
			template: `{{- $unused := get .Values.services .Values.selected -}}`,
			operations: []wireOperation{
				{Kind: "read", Path: propertyPath("selected")},
				{Kind: "selectDynamic", Path: propertyPath("services")},
			},
		},
		{
			name: "finite calculated selection keeps fixed properties",
			template: `{{- $name := ternary "http" "https" .Values.tls -}}
{{ get .Values.services $name }}`,
			operations: []wireOperation{
				{Kind: "read", Path: propertyPath("tls")},
				{
					Kind: "selectFinite", Path: propertyPath("services"),
					Names: []string{"http", "https"},
				},
				{Kind: "complete", Path: propertyPath("services", "http")},
				{Kind: "complete", Path: propertyPath("services", "https")},
			},
		},
		{
			name:     "key inspection permits direct keys",
			template: `{{ keys .Values.settings }}`,
			operations: []wireOperation{{
				Kind: "allowUnknown", Path: propertyPath("settings"),
			}},
		},
		{
			name:     "calculated get selects a dynamic property",
			template: `{{ get .Values.services .Values.selected }}`,
			operations: []wireOperation{
				{Kind: "read", Path: propertyPath("selected")},
				{Kind: "selectDynamic", Path: propertyPath("services")},
				{Kind: "complete", Path: pathWith(propertyPath("services"), "additional")},
			},
		},
		{
			name:     "checksum consumes an exact value",
			template: `{{ .Values.service | toJson | sha256sum }}`,
			operations: []wireOperation{{
				Kind: "exact", Path: propertyPath("service"),
			}},
		},
		{
			name:     "range records collection and element use",
			template: `{{ range .Values.items }}{{ .name }}{{ end }}`,
			operations: []wireOperation{
				{Kind: "iterate", Path: propertyPath("items")},
				{Kind: "complete", Path: append(
					pathWith(propertyPath("items"), "elements"),
					wireSegment{Kind: "property", Name: "name"},
				)},
			},
		},
		{
			name:                "unknown function records conservative complete use",
			template:            `{{ futureHelmFunction .Values.payload }}`,
			diagnosticSubstring: "futureHelmFunction",
			operations: []wireOperation{{
				Kind: "unsupported", Path: propertyPath("payload"),
				Mode: "open", Reason: "unknownFunction",
			}},
		},
	}

	document := wireDocument{
		Version: 3,
		Cases:   make([]wireCase, 0, len(fixtures)),
	}
	for _, operation := range analyze.FormalFunctionOperations() {
		document.Functions = append(document.Functions, wireFunctionOperation{
			Name: operation.Name, Class: operation.Class, Lowering: operation.Lowering,
		})
	}
	for _, fixture := range fixtures {
		usage, diagnostics, err := analyze.Templates([]analyze.Template{{
			Name: "templates/conformance.yaml", Content: []byte(fixture.template), Entry: true,
		}})
		if err != nil {
			t.Fatalf("analyze %q: %v", fixture.name, err)
		}
		if fixture.diagnosticSubstring == "" && len(diagnostics) != 0 {
			t.Fatalf("analyze %q returned diagnostics: %v", fixture.name, diagnostics)
		}
		if fixture.diagnosticSubstring != "" &&
			(len(diagnostics) != 1 ||
				!strings.Contains(diagnostics[0].Message, fixture.diagnosticSubstring)) {
			t.Fatalf("analyze %q diagnostics = %v", fixture.name, diagnostics)
		}
		wireUsage, err := rawUsage(usage)
		if err != nil {
			t.Fatalf("encode usage %q: %v", fixture.name, err)
		}
		document.Cases = append(document.Cases, wireCase{
			Name: fixture.name, Operations: fixture.operations, Usage: wireUsage,
		})
	}

	addFlowCase := func(name string, usage *analyze.Usage, flows []analyze.ValueFlow) {
		t.Helper()
		before, err := rawUsage(usage)
		if err != nil {
			t.Fatalf("encode flow input %q: %v", name, err)
		}
		if err := analyze.ApplyValueFlows(usage, flows); err != nil {
			t.Fatalf("apply flow %q: %v", name, err)
		}
		after, err := rawUsage(usage)
		if err != nil {
			t.Fatalf("encode flow result %q: %v", name, err)
		}
		wireFlows := make([]wireValueFlow, len(flows))
		for index, flow := range flows {
			wireFlows[index] = wireValueFlow{
				Source: slices.Clone(flow.Source), Destination: slices.Clone(flow.Destination),
			}
		}
		document.Flows = append(document.Flows, wireFlowCase{
			Name: name, Before: before, Flows: wireFlows, After: after,
		})
	}
	addFlowCase("import propagates back to source", &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"imported": {Properties: map[string]*analyze.Usage{
				"message": {Read: true, Open: true},
			}},
		},
	}, []analyze.ValueFlow{{
		Source:      []string{"worker", "exports", "settings"},
		Destination: []string{"imported"},
	}})
	addFlowCase("global propagates to dependency", &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"global": {Properties: map[string]*analyze.Usage{
				"region": {Read: true},
			}},
		},
	}, []analyze.ValueFlow{{
		Source: []string{"global"}, Destination: []string{"worker", "global"},
	}})
	addFlowCase("transitive copies use distinct edges", &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"published": {Properties: map[string]*analyze.Usage{
				"enabled": {Exact: true},
			}},
		},
	}, []analyze.ValueFlow{
		{Source: []string{"source"}, Destination: []string{"middle"}},
		{Source: []string{"middle"}, Destination: []string{"published"}},
	})
	addFlowCase("cycle remains finite", &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"left": {Properties: map[string]*analyze.Usage{
				"value": {Read: true},
			}},
		},
	}, []analyze.ValueFlow{
		{Source: []string{"right"}, Destination: []string{"left"}},
		{Source: []string{"left"}, Destination: []string{"right"}},
	})
	addFlowCase("non-property suffix is retained", &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"global": {Additional: &analyze.Usage{
				Iterated: true,
				Properties: map[string]*analyze.Usage{
					"name": {AllowUnknown: true},
				},
			}},
		},
	}, []analyze.ValueFlow{{
		Source: []string{"global"}, Destination: []string{"worker", "global"},
	}})
	addFlowCase("all usage modes propagate independently", &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"source": {
				Read: true, Exact: true, AllowUnknown: true, Open: true, Iterated: true,
			},
		},
	}, []analyze.ValueFlow{{
		Source: []string{"source"}, Destination: []string{"destination"},
	}})

	boundaryFixtures := []boundaryFixture{
		{name: "no evidence", defaults: map[string]any{}, usage: nil},
		{name: "complete use", usage: &analyze.Usage{Open: true}},
		{name: "template context", usage: &analyze.Usage{AllowUnknown: true}},
		{name: "iteration", usage: &analyze.Usage{Iterated: true}},
		{name: "dynamic map key", usage: &analyze.Usage{Additional: &analyze.Usage{}}},
		{name: "shape-neutral element", usage: &analyze.Usage{Elements: &analyze.Usage{}}},
		{name: "truth test with empty defaults", usage: &analyze.Usage{Read: true}},
		{
			name:     "truth test with null-only defaults",
			defaults: map[string]any{"optional": nil},
			usage:    &analyze.Usage{Read: true},
		},
		{
			name:     "truth test with a typed nil default",
			defaults: map[string]any{"optional": nilObject},
			usage:    &analyze.Usage{Read: true},
		},
		{
			name:     "truth test with a non-null default",
			defaults: map[string]any{"fixed": "value"},
			usage:    &analyze.Usage{Read: true},
		},
		{
			name: "truth test with a field contract",
			usage: &analyze.Usage{Read: true, Properties: map[string]*analyze.Usage{
				"enabled": {Read: true},
			}},
		},
	}
	boundaryDefaultCases := []struct {
		name     string
		defaults map[string]any
	}{
		{name: "empty", defaults: map[string]any{}},
		{name: "null-only", defaults: map[string]any{"optional": nil}},
		{name: "non-null", defaults: map[string]any{"fixed": "value"}},
	}
	const boundaryBits = 9
	for mask := range 1 << boundaryBits {
		usage := &analyze.Usage{
			Read:         mask&(1<<0) != 0,
			Exact:        mask&(1<<1) != 0,
			AllowUnknown: mask&(1<<2) != 0,
			Open:         mask&(1<<3) != 0,
			Iterated:     mask&(1<<4) != 0,
		}
		if mask&(1<<5) != 0 {
			usage.Properties = map[string]*analyze.Usage{"field": {}}
		}
		if mask&(1<<6) != 0 {
			usage.Additional = &analyze.Usage{}
		}
		if mask&(1<<7) != 0 {
			usage.Items = &analyze.Usage{}
		}
		if mask&(1<<8) != 0 {
			usage.Elements = &analyze.Usage{}
		}
		for _, defaultCase := range boundaryDefaultCases {
			boundaryFixtures = append(boundaryFixtures, boundaryFixture{
				name:     fmt.Sprintf("all flags/%03x/%s", mask, defaultCase.name),
				defaults: defaultCase.defaults,
				usage:    usage,
			})
		}
	}
	for _, fixture := range boundaryFixtures {
		wireUsage, err := rawUsage(fixture.usage)
		if err != nil {
			t.Fatalf("encode boundary usage %q: %v", fixture.name, err)
		}
		defaultValues, err := boundaryDefaults(fixture.defaults)
		if err != nil {
			t.Fatalf("encode boundary defaults %q: %v", fixture.name, err)
		}
		document.Boundaries = append(document.Boundaries, wireBoundary{
			Name:     fixture.name,
			Defaults: defaultValues,
			Usage:    wireUsage,
			GoAllows: chartschema.AllowsUnknownRootProperties(
				fixture.defaults, fixture.usage,
			),
		})
	}

	schemaFixtures := []schemaFixture{
		{
			name: "flat scalar defaults and uses",
			defaults: map[string]any{
				"computed": "{{ .Values.source }}",
				"enabled":  true,
				"fixed":    "unchanged",
				"message":  "hello",
				"optional": nil,
				"ratio":    2.5,
				"replicas": 2,
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"computed": {Read: true},
				"enabled":  {Read: true},
				"message":  {Read: true},
				"missing":  {Read: true},
				"ratio":    {Read: true},
				"replicas": {Read: true},
			}},
		},
		{
			name:     "open root does not infer child scalar types",
			defaults: map[string]any{"enabled": true},
			usage:    &analyze.Usage{Open: true},
		},
		{
			name: "present empty usage nodes preserve direct use",
			defaults: map[string]any{
				"literal":  "text",
				"template": "{{ .Values.source }}",
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"literal":  {},
				"template": {},
			}},
		},
		{
			name: "read object keeps unused descendants fixed",
			defaults: map[string]any{
				"settings": map[string]any{"name": "fixed"},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"settings": {Read: true},
			}},
		},
		{
			name:     "exact root keeps unused descendants fixed",
			defaults: map[string]any{"name": "fixed"},
			usage:    &analyze.Usage{Exact: true},
		},
		{
			name: "Go JSON aliases pointers and typed nil values",
			defaults: map[string]any{
				"fraction":   &fractionPointer,
				"integer":    &integerPointer,
				"nilList":    nilList,
				"nilObject":  nilObject,
				"nilPointer": nilPointer,
				"object": namedObject{
					namedKey("name"): namedString("value"),
				},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"fraction":   {Read: true},
				"integer":    {Read: true},
				"nilList":    {Read: true},
				"nilObject":  {Read: true},
				"nilPointer": {Read: true},
				"object": {Properties: map[string]*analyze.Usage{
					"name": {Read: true},
				}},
			}},
		},
		{name: "open empty root", usage: &analyze.Usage{Open: true}},
		{name: "truth-tested empty root", usage: &analyze.Usage{Read: true}},
		{
			name: "truth test with a fixed field contract",
			usage: &analyze.Usage{
				Read: true,
				Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				},
			},
		},
		{
			name:  "dynamic root property",
			usage: &analyze.Usage{Additional: &analyze.Usage{Read: true}},
		},
		{
			name:     "raw null with a coalesced scalar default",
			defaults: map[string]any{"message": "from-dependency"},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"message": {Read: true},
			}},
			nullDefaults: [][]string{{"message"}},
		},
		{
			name: "closed object with scalar fields",
			defaults: map[string]any{
				"settings": map[string]any{
					"enabled": true,
					"fixed":   "unchanged",
				},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"settings": {
					Properties: map[string]*analyze.Usage{
						"enabled": {Read: true},
					},
				},
			}},
		},
		{
			name: "recursively nested closed objects",
			defaults: map[string]any{
				"service": map[string]any{
					"main": map[string]any{
						"ports": map[string]any{
							"http": 8080,
						},
					},
				},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"service": {Properties: map[string]*analyze.Usage{
					"main": {Properties: map[string]*analyze.Usage{
						"ports": {Properties: map[string]*analyze.Usage{
							"http": {Read: true},
						}},
					}},
				}},
			}},
		},
		{
			name: "nested raw null with a coalesced scalar default",
			defaults: map[string]any{
				"settings": map[string]any{"message": "from-dependency"},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"settings": {Properties: map[string]*analyze.Usage{
					"message": {Read: true},
				}},
			}},
			nullDefaults: [][]string{{"settings", "message"}},
		},
		{
			name: "explicitly nullable object",
			defaults: map[string]any{
				"feature": map[string]any{"enabled": true},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"feature": {Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				}},
			}},
			nullDefaults: [][]string{{"feature"}},
		},
		{
			name: "unused container constants",
			defaults: map[string]any{
				"items": []any{"one", float64(2)},
				"settings": map[string]any{
					"enabled": true,
					"nested":  map[string]any{"name": "fixed"},
				},
			},
		},
		{
			name: "explicitly nullable unused object constant",
			defaults: map[string]any{
				"settings": map[string]any{"enabled": true},
			},
			nullDefaults: [][]string{{"settings"}},
		},
	}
	emptyFormalBoundary := func() wireBoundaryInput {
		return wireBoundaryInput{Defaults: []wireJSONValue{}}
	}
	mustFormalValue := func(value any) wireJSONValue {
		t.Helper()
		result, err := jsonValue(value)
		if err != nil {
			t.Fatalf("encode formal fixture value: %v", err)
		}
		return result
	}
	usedString := wireValueProperty{
		Kind:        "leaf",
		Default:     wireScalarValue{Kind: "string", Value: "one"},
		DirectUsage: true,
	}
	strictItem := wireValueProperty{
		Kind: "object",
		Properties: []wireValueProperty{{Name: "name", Kind: usedString.Kind,
			Default: usedString.Default, DirectUsage: true}},
		Boundary: emptyFormalBoundary(),
	}
	originalItems := []any{map[string]any{"name": "one", "unused": "fixed"}}
	originalItemsValue := mustFormalValue(originalItems)
	usedArrayInput := wireCoreInput{
		Properties: []wireValueProperty{{
			Name: "items", Kind: "allOf",
			Constraints: []wireValueProperty{
				{Kind: "array", Items: &wireValueProperty{Kind: "unrestricted"}},
				{Kind: "anyOf", Alternatives: []wireValueProperty{
					{Kind: "fixed", Fixed: &originalItemsValue},
					{Kind: "array", Items: &strictItem},
				}},
			},
		}},
		Boundary: emptyFormalBoundary(),
	}
	shapeInput := wireCoreInput{
		Properties: []wireValueProperty{{
			Name: "feature", Kind: "anyOf",
			Alternatives: []wireValueProperty{
				{Kind: "fixed", Fixed: func() *wireJSONValue {
					value := mustFormalValue("off")
					return &value
				}()},
				{Kind: "object", Properties: []wireValueProperty{
					{Name: "enabled", Kind: "unrestricted"},
				}, Boundary: emptyFormalBoundary()},
			},
		}},
		Boundary: emptyFormalBoundary(),
	}
	usedBoolean := wireValueProperty{
		Name: "enabled", Kind: "leaf",
		Default:     wireScalarValue{Kind: "boolean", Value: true},
		DirectUsage: true,
	}
	dynamicEntry := wireValueProperty{
		Kind: "object", Properties: []wireValueProperty{usedBoolean},
		Boundary: emptyFormalBoundary(),
	}
	structuredDynamicInput := wireCoreInput{
		Properties: []wireValueProperty{{
			Name: "services", Kind: "object",
			Properties: []wireValueProperty{{
				Name: "first", Kind: dynamicEntry.Kind,
				Properties: dynamicEntry.Properties, Boundary: emptyFormalBoundary(),
			}},
			Additional: &dynamicEntry,
			Boundary:   emptyFormalBoundary(),
		}},
		Boundary: emptyFormalBoundary(),
	}
	schemaFixtures = append(schemaFixtures,
		schemaFixture{
			name:     "formal used replacement array",
			defaults: map[string]any{"items": originalItems},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"items": {Items: &analyze.Usage{Properties: map[string]*analyze.Usage{
					"name": {Read: true},
				}}},
			}},
			formalInput: &usedArrayInput,
		},
		schemaFixture{
			name:     "formal scalar and object shape alternatives",
			defaults: map[string]any{"feature": "off"},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"feature": {Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				}},
			}},
			formalInput: &shapeInput,
		},
		schemaFixture{
			name: "formal structured dynamic entries",
			defaults: map[string]any{"services": map[string]any{
				"first": map[string]any{"enabled": true},
			}},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"services": {Additional: &analyze.Usage{Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				}}},
			}},
			formalInput: &structuredDynamicInput,
		},
	)
	scalarDefaults := []struct {
		name   string
		value  any
		exists bool
	}{
		{name: "missing"},
		{name: "null", value: nil, exists: true},
		{name: "boolean", value: true, exists: true},
		{name: "integer", value: int64(2), exists: true},
		{name: "integral-float", value: float64(2), exists: true},
		{name: "integral-decimal-token", value: json.Number("2.0"), exists: true},
		{name: "integral-exponent-token", value: json.Number("2e0"), exists: true},
		{name: "number", value: 2.5, exists: true},
		{name: "string", value: "text", exists: true},
		{name: "template", value: "{{ .Values.source }}", exists: true},
	}
	scalarUsageCases := []struct {
		name string
		make func() *analyze.Usage
	}{
		{name: "absent", make: func() *analyze.Usage { return nil }},
		{name: "empty", make: func() *analyze.Usage { return &analyze.Usage{} }},
		{name: "read", make: func() *analyze.Usage { return &analyze.Usage{Read: true} }},
		{name: "exact", make: func() *analyze.Usage { return &analyze.Usage{Exact: true} }},
		{name: "context", make: func() *analyze.Usage { return &analyze.Usage{AllowUnknown: true} }},
		{name: "open", make: func() *analyze.Usage { return &analyze.Usage{Open: true} }},
	}
	for _, defaultCase := range scalarDefaults {
		for _, usageCase := range scalarUsageCases {
			for _, rootOpen := range []bool{false, true} {
				for _, explicitNull := range []bool{false, true} {
					defaults := make(map[string]any)
					if defaultCase.exists {
						defaults["value"] = defaultCase.value
					}
					childUsage := usageCase.make()
					var usage *analyze.Usage
					if rootOpen || childUsage != nil {
						usage = &analyze.Usage{Open: rootOpen}
						if childUsage != nil {
							usage.Properties = map[string]*analyze.Usage{"value": childUsage}
						}
					}
					var nullDefaults [][]string
					if explicitNull {
						nullDefaults = [][]string{{"value"}}
					}
					schemaFixtures = append(schemaFixtures, schemaFixture{
						name: fmt.Sprintf(
							"bounded scalar/%s/%s/root-open-%t/null-%t",
							defaultCase.name, usageCase.name, rootOpen, explicitNull,
						),
						defaults:     defaults,
						usage:        usage,
						nullDefaults: nullDefaults,
					})
				}
			}
		}
	}
	for _, fixture := range schemaFixtures {
		var input wireCoreInput
		if fixture.formalInput != nil {
			input = *fixture.formalInput
		} else {
			var err error
			input, err = coreInput(fixture.defaults, fixture.usage, fixture.nullDefaults)
			if err != nil {
				t.Fatalf("formal input %q: %v", fixture.name, err)
			}
		}
		semanticSchema, err := generatedSemanticSchema(
			fixture.defaults, fixture.usage, fixture.nullDefaults,
		)
		if err != nil {
			t.Fatalf("generate schema %q: %v", fixture.name, err)
		}
		document.Schemas = append(document.Schemas, wireSchemaCase{
			Name: fixture.name, Input: input, GoSchema: semanticSchema,
		})
	}

	validatorFixtures := []validatorFixture{
		{
			name: "numeric constant uses mathematical equality",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"value": map[string]any{"const": json.Number("1")},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "same integer", values: map[string]any{"value": json.Number("1")}},
				{name: "same decimal", values: map[string]any{"value": json.Number("1.0")}},
				{name: "same exponent", values: map[string]any{"value": json.Number("1e0")}},
				{name: "different number", values: map[string]any{"value": json.Number("1.5")}},
			},
		},
		{
			name: "integer means mathematically integral",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"value": map[string]any{"type": "integer"},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "integer token", values: map[string]any{"value": json.Number("2")}},
				{name: "integral decimal", values: map[string]any{"value": json.Number("2.0")}},
				{name: "integral exponent", values: map[string]any{"value": json.Number("2e0")}},
				{name: "fraction", values: map[string]any{"value": json.Number("2.5")}},
			},
		},
		{
			name: "scientific number normalization",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"fraction": map[string]any{"const": json.Number("0.01")},
					"thousand": map[string]any{"const": json.Number("1000")},
					"zero":     map[string]any{"const": json.Number("0")},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "equivalent exponents", values: map[string]any{
					"fraction": json.Number("1e-2"),
					"thousand": json.Number("1e3"),
					"zero":     json.Number("-0.0"),
				}},
				{name: "different exponent", values: map[string]any{
					"fraction": json.Number("1e-3"),
					"thousand": json.Number("1e3"),
					"zero":     json.Number("0"),
				}},
			},
		},
		{
			name: "object constant ignores member order",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"value": map[string]any{"const": map[string]any{
						"left": json.Number("1"), "right": "fixed",
					}},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "equal object", values: map[string]any{"value": map[string]any{
					"right": "fixed", "left": json.Number("1.0"),
				}}},
				{name: "changed object", values: map[string]any{"value": map[string]any{
					"right": "changed", "left": json.Number("1"),
				}}},
			},
		},
		{
			name: "closed nested object",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"settings": map[string]any{
						"type": "object",
						"properties": map[string]any{
							"enabled": map[string]any{"type": "boolean"},
						},
						"additionalProperties": false,
					},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "known field", values: map[string]any{"settings": map[string]any{"enabled": true}}},
				{name: "omitted optional field", values: map[string]any{}},
				{name: "unknown nested field", values: map[string]any{"settings": map[string]any{"enablede": true}}},
				{name: "wrong nested type", values: map[string]any{"settings": map[string]any{"enabled": "true"}}},
			},
		},
		{
			name: "nullable object type union",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"settings": map[string]any{
						"type": []any{"object", "null"},
						"properties": map[string]any{
							"enabled": map[string]any{"type": "boolean"},
						},
						"additionalProperties": false,
					},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "null", values: map[string]any{"settings": nil}},
				{name: "valid object", values: map[string]any{"settings": map[string]any{"enabled": false}}},
				{name: "object typo", values: map[string]any{"settings": map[string]any{"enablede": false}}},
				{name: "wrong scalar", values: map[string]any{"settings": "disabled"}},
			},
		},
		{
			name: "array type and anyOf siblings",
			schema: map[string]any{
				"type": "object",
				"properties": map[string]any{
					"items": map[string]any{
						"type": "array",
						"anyOf": []any{
							map[string]any{"const": []any{"fixed", json.Number("1")}},
							map[string]any{"type": "array", "items": map[string]any{"type": "string"}},
						},
					},
				},
				"additionalProperties": false,
			},
			candidates: []validatorCandidate{
				{name: "exact mixed default", values: map[string]any{"items": []any{"fixed", json.Number("1.0")}}},
				{name: "string replacement", values: map[string]any{"items": []any{"one", "two"}}},
				{name: "invalid replacement", values: map[string]any{"items": []any{"one", true}}},
				{name: "wrong outer type", values: map[string]any{"items": "one"}},
			},
		},
	}
	generatedValidatorFixtures := []generatedValidatorFixture{
		{
			name: "generated structured dynamic entries",
			defaults: map[string]any{
				"services": map[string]any{
					"first": map[string]any{"enabled": true},
				},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"services": {Additional: &analyze.Usage{
					Properties: map[string]*analyze.Usage{"enabled": {Read: true}},
				}},
			}},
			candidates: []validatorCandidate{
				{name: "original", values: map[string]any{"services": map[string]any{
					"first": map[string]any{"enabled": true},
				}}},
				{name: "valid new key", values: map[string]any{"services": map[string]any{
					"second": map[string]any{"enabled": false},
				}}},
				{name: "typo in new entry", values: map[string]any{"services": map[string]any{
					"second": map[string]any{"enablede": false},
				}}},
				{name: "wrong entry field type", values: map[string]any{"services": map[string]any{
					"second": map[string]any{"enabled": "false"},
				}}},
			},
		},
		{
			name: "generated strict replacement array",
			defaults: map[string]any{
				"items": []any{map[string]any{"name": "one", "unused": "fixed"}},
			},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"items": {Items: &analyze.Usage{Properties: map[string]*analyze.Usage{
					"name": {Read: true},
				}}},
			}},
			candidates: []validatorCandidate{
				{name: "exact original", values: map[string]any{
					"items": []any{map[string]any{"name": "one", "unused": "fixed"}},
				}},
				{name: "valid replacement", values: map[string]any{
					"items": []any{map[string]any{"name": "two"}},
				}},
				{name: "replacement typo", values: map[string]any{
					"items": []any{map[string]any{"nam": "two"}},
				}},
				{name: "replacement wrong type", values: map[string]any{
					"items": []any{map[string]any{"name": true}},
				}},
			},
		},
		{
			name:     "generated shape conflict keeps default",
			defaults: map[string]any{"feature": "off"},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"feature": {Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				}},
			}},
			candidates: []validatorCandidate{
				{name: "original scalar", values: map[string]any{"feature": "off"}},
				{name: "valid object", values: map[string]any{"feature": map[string]any{"enabled": true}}},
				{name: "object typo", values: map[string]any{"feature": map[string]any{"enablede": true}}},
				{name: "unrelated scalar", values: map[string]any{"feature": "on"}},
			},
		},
		{
			name: "generated missing object permits null",
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"settings": {Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				}},
			}},
			candidates: []validatorCandidate{
				{name: "omitted", values: map[string]any{}},
				{name: "null", values: map[string]any{"settings": nil}},
				{name: "valid object", values: map[string]any{"settings": map[string]any{"enabled": true}}},
				{name: "object typo", values: map[string]any{"settings": map[string]any{"enablede": true}}},
			},
		},
		{
			name:     "generated iteration accepts map or array",
			defaults: map[string]any{"items": []any{json.Number("1")}},
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"items": {Iterated: true},
			}},
			candidates: []validatorCandidate{
				{name: "replacement array", values: map[string]any{"items": []any{true, "two"}}},
				{name: "replacement map", values: map[string]any{"items": map[string]any{"one": true}}},
				{name: "wrong scalar", values: map[string]any{"items": "one"}},
			},
		},
	}
	for _, fixture := range generatedValidatorFixtures {
		rawSchema, err := chartschema.Generate(
			fixture.defaults, nil, fixture.usage, fixture.nullDefaults...,
		)
		if err != nil {
			t.Fatalf("generate validator schema %q: %v", fixture.name, err)
		}
		schemaDocument, err := decodeSchemaDocument(rawSchema)
		if err != nil {
			t.Fatalf("decode validator schema %q: %v", fixture.name, err)
		}
		for _, candidate := range fixture.candidates {
			validation, err := validationCase(fixture.name, candidate, schemaDocument)
			if err != nil {
				t.Fatalf("validator conformance %q/%q: %v", fixture.name, candidate.name, err)
			}
			document.Validations = append(document.Validations, validation)
		}
	}
	for _, fixture := range validatorFixtures {
		for _, candidate := range fixture.candidates {
			validation, err := validationCase(fixture.name, candidate, fixture.schema)
			if err != nil {
				t.Fatalf("validator conformance %q/%q: %v", fixture.name, candidate.name, err)
			}
			document.Validations = append(document.Validations, validation)
		}
	}

	input, err := json.Marshal(document)
	if err != nil {
		t.Fatal(err)
	}
	command := exec.Command(verifier)
	command.Stdin = bytes.NewReader(input)
	output, err := command.CombinedOutput()
	if err != nil {
		t.Fatalf("Lean conformance failed: %v\n%s\ninput: %s", err, output, input)
	}
	if len(output) != 0 {
		t.Fatalf("Lean conformance wrote unexpected output: %s", output)
	}
	fmt.Fprintf(os.Stderr,
		"verified %d analyzer, %d flow, %d function, %d boundary, %d schema, and %d Helm validator cases against Lean\n",
		len(fixtures), len(document.Flows), len(document.Functions),
		len(boundaryFixtures), len(schemaFixtures), len(document.Validations),
	)
}

// TestConflictingDynamicExamplesValidateAsAlternatives makes sure that
// inferred dynamic-entry alternatives accept only the observed field types.
func TestConflictingDynamicExamplesValidateAsAlternatives(t *testing.T) {
	t.Parallel()

	schemaJSON, err := chartschema.Generate(map[string]any{
		"services": map[string]any{
			"numeric": map[string]any{"port": 8080},
			"named":   map[string]any{"port": "http"},
		},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"services": {Additional: &analyze.Usage{
			Properties: map[string]*analyze.Usage{"port": {Read: true}},
		}},
	}})
	if err != nil {
		t.Fatal(err)
	}

	tests := []struct {
		name   string
		entry  map[string]any
		accept bool
	}{
		{name: "integer port", entry: map[string]any{"port": 9090}, accept: true},
		{name: "string port", entry: map[string]any{"port": "metrics"}, accept: true},
		{name: "boolean port", entry: map[string]any{"port": true}, accept: false},
		{name: "unknown field", entry: map[string]any{"poort": 9090}, accept: false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			accepted, err := helmAccepts(map[string]any{
				"services": map[string]any{"replacement": test.entry},
			}, schemaJSON)
			if err != nil {
				t.Fatal(err)
			}
			if accepted != test.accept {
				t.Fatalf("accepted = %t, want %t", accepted, test.accept)
			}
		})
	}
}

// TestVerifierRejectsUnknownProtocolVersion protects the protocol boundary
// from silent interpretation of a newer document format.
func TestVerifierRejectsUnknownProtocolVersion(t *testing.T) {
	command := exec.Command(formalVerifier(t))
	command.Stdin = bytes.NewBufferString(`{"version":4,"cases":[]}`)
	output, err := command.CombinedOutput()
	if err == nil {
		t.Fatalf("Lean verifier accepted an unknown protocol version: %s", output)
	}
	if !bytes.Contains(output, []byte("unsupported protocol version 4")) {
		t.Fatalf("Lean verifier returned an unclear version error: %s", output)
	}
}

// TestVerifierRejectsMalformedProtocol protects assumptions such as unique
// object keys and complete raw usage nodes at the Go-to-Lean boundary.
func TestVerifierRejectsMalformedProtocol(t *testing.T) {
	t.Parallel()

	emptyUsage := `{"read":false,"exact":false,"allowUnknown":false,"open":false,"iterated":false,"properties":[],"additional":null,"items":null,"elements":null}`
	tests := []struct {
		name    string
		input   string
		message string
	}{
		{
			name: "incomplete raw usage",
			input: `{"version":3,"cases":[{"name":"bad","operations":[],"usage":{"read":false}}],` +
				`"flows":[],"functions":[],"boundaries":[],"schemas":[],"validations":[]}`,
			message: "property not found",
		},
		{
			name: "duplicate raw usage property",
			input: `{"version":3,"cases":[{"name":"bad","operations":[],"usage":` +
				`{"read":false,"exact":false,"allowUnknown":false,"open":false,"iterated":false,` +
				`"properties":[{"name":"same","usage":` + emptyUsage + `},{"name":"same","usage":` + emptyUsage + `}],` +
				`"additional":null,"items":null,"elements":null}}],"flows":[],"functions":[],` +
				`"boundaries":[],"schemas":[],"validations":[]}`,
			message: "duplicate object property same",
		},
		{
			name: "duplicate JSON object property",
			input: `{"version":3,"cases":[],"flows":[],"functions":[],"boundaries":[],"schemas":[],"validations":[` +
				`{"name":"bad","schema":{"kind":"any","properties":null,"additional":null},` +
				`"value":{"kind":"object","items":null,"properties":[` +
				`{"name":"same","value":{"kind":"null","items":null,"properties":null}},` +
				`{"name":"same","value":{"kind":"null","items":null,"properties":null}}]},` +
				`"helmAccepts":true}]}`,
			message: "duplicate object property same",
		},
		{
			name: "unknown semantic schema",
			input: `{"version":3,"cases":[],"flows":[],"functions":[],"boundaries":[],"schemas":[],"validations":[` +
				`{"name":"bad","schema":{"kind":"future"},` +
				`"value":{"kind":"null","items":null,"properties":null},"helmAccepts":false}]}`,
			message: "unsupported semantic schema kind future",
		},
		{
			name: "unknown fallback reason",
			input: `{"version":3,"cases":[{"name":"bad","operations":[` +
				`{"kind":"unsupported","path":[],"mode":"open","reason":"future"}],` +
				`"usage":` + emptyUsage + `}],"flows":[],"functions":[],` +
				`"boundaries":[],"schemas":[],"validations":[]}`,
			message: "unknown fallback reason future",
		},
		{
			name: "duplicate function row",
			input: `{"version":3,"cases":[],"flows":[],"functions":[` +
				`{"name":"same","class":"read","lowering":"read"},` +
				`{"name":"same","class":"read","lowering":"read"}],` +
				`"boundaries":[],"schemas":[],"validations":[]}`,
			message: "duplicate function matrix row same",
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			t.Parallel()
			command := exec.Command(formalVerifier(t))
			command.Stdin = strings.NewReader(test.input)
			output, err := command.CombinedOutput()
			if err == nil {
				t.Fatalf("Lean verifier accepted malformed input: %s", output)
			}
			if !bytes.Contains(output, []byte(test.message)) {
				t.Fatalf("Lean verifier returned an unclear error: %s", output)
			}
		})
	}
}

// TestCoreInputRejectsOutsideFragment prevents unsupported production inputs
// from receiving a misleading formal interpretation.
func TestCoreInputRejectsOutsideFragment(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name         string
		defaults     map[string]any
		usage        *analyze.Usage
		nullDefaults [][]string
	}{
		{
			name:     "open array default",
			defaults: map[string]any{"items": []any{"one"}},
			usage:    &analyze.Usage{Open: true},
		},
		{
			name: "missing nested object",
			usage: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"settings": {
					Properties: map[string]*analyze.Usage{"enabled": {Read: true}},
				},
			}},
		},
		{
			name:     "dynamic contract with known defaults",
			defaults: map[string]any{"known": "value"},
			usage:    &analyze.Usage{Additional: &analyze.Usage{Read: true}},
		},
		{
			name:  "array usage",
			usage: &analyze.Usage{Items: &analyze.Usage{Read: true}},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			t.Parallel()
			if _, err := coreInput(test.defaults, test.usage, test.nullDefaults); err == nil {
				t.Fatal("unsupported input was accepted by the formal adapter")
			}
		})
	}
}

// TestNormalizeSchemaPreservesDraft7Semantics covers syntax that previously
// became an unrestricted schema during conformance normalization.
func TestNormalizeSchemaPreservesDraft7Semantics(t *testing.T) {
	t.Parallel()

	tests := []struct {
		name     string
		document map[string]any
		want     wireSemanticSchema
	}{
		{
			name: "nullable closed object",
			document: map[string]any{
				"type":                 []any{"object", "null"},
				"properties":           map[string]any{"enabled": map[string]any{"type": "boolean"}},
				"additionalProperties": false,
			},
			want: wireSemanticSchema{Kind: "anyOf", Alternatives: []wireSemanticSchema{
				{
					Kind: "object",
					Properties: []wireSchemaProperty{{
						Name: "enabled", Schema: wireSemanticSchema{Kind: "typed", Type: "boolean"},
					}},
				},
				{Kind: "typed", Type: "null"},
			}},
		},
		{
			name:     "object defaults to open",
			document: map[string]any{"type": "object"},
			want: wireSemanticSchema{
				Kind:       "object",
				Properties: []wireSchemaProperty{},
				Additional: &wireSemanticSchema{Kind: "any"},
			},
		},
		{
			name:     "array defaults to unrestricted items",
			document: map[string]any{"type": "array"},
			want: wireSemanticSchema{
				Kind: "array", Items: &wireSemanticSchema{Kind: "any"},
			},
		},
		{
			name: "sibling constraints form a conjunction",
			document: map[string]any{
				"type": "array",
				"anyOf": []any{
					map[string]any{"const": []any{"fixed"}},
					map[string]any{"type": "array", "items": map[string]any{"type": "string"}},
				},
			},
			want: wireSemanticSchema{Kind: "allOf", Constraints: []wireSemanticSchema{
				{Kind: "array", Items: &wireSemanticSchema{Kind: "any"}},
				{Kind: "anyOf", Alternatives: []wireSemanticSchema{
					{
						Kind: "constant",
						Value: &wireJSONValue{
							Kind: "array", Items: []wireJSONValue{{Kind: "string", Value: "fixed"}},
						},
					},
					{Kind: "array", Items: &wireSemanticSchema{Kind: "typed", Type: "string"}},
				}},
			}},
		},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			t.Parallel()
			got, err := normalizeSchema(test.document)
			if err != nil {
				t.Fatal(err)
			}
			if !reflect.DeepEqual(got, test.want) {
				t.Fatalf("normalized schema mismatch\n got: %#v\nwant: %#v", got, test.want)
			}
		})
	}
}

// TestNormalizeSchemaRejectsUnsupportedSyntax ensures conformance cannot pass
// by dropping validation rules that the Lean model does not understand.
func TestNormalizeSchemaRejectsUnsupportedSyntax(t *testing.T) {
	t.Parallel()

	tests := []map[string]any{
		{"type": "string", "minLength": 1},
		{"type": []any{}},
		{"type": []any{"string", "string"}},
		{"properties": map[string]any{}},
		{"type": "string", "items": map[string]any{}},
		{"anyOf": "not-an-array"},
	}
	for _, document := range tests {
		if _, err := normalizeSchema(document); err == nil {
			t.Fatalf("unsupported schema was accepted: %#v", document)
		}
	}
}
