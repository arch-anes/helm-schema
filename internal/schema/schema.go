// Package schema builds a Helm values JSON Schema from template usage.
package schema

// This file combines the effective defaults and analyzer evidence. It emits a
// Draft 7 schema with explicit property and shape rules.

import (
	"bytes"
	"encoding/json"
	"fmt"
	"maps"
	"reflect"
	"slices"
	"strings"

	"github.com/arch-anes/helm-schema/internal/analyze"
)

// draft7 is the schema identifier supported by Helm 4 validation.
const draft7 = "http://json-schema.org/draft-07/schema#"

// document is deliberately small. JSON Schema permits many more keywords, but
// generation currently needs only the keywords represented here.
type document struct {
	Schema               string                `json:"$schema,omitempty"`
	Type                 any                   `json:"type,omitempty"`
	Description          string                `json:"description,omitempty"`
	Default              *json.RawMessage      `json:"default,omitempty"`
	Const                *json.RawMessage      `json:"const,omitempty"`
	AnyOf                []*document           `json:"anyOf,omitempty"`
	Properties           *map[string]*document `json:"properties,omitempty"`
	Items                *document             `json:"items,omitempty"`
	AdditionalProperties any                   `json:"additionalProperties,omitempty"`
}

// builder owns the annotations shared by one recursive schema build.
type builder struct {
	descriptions         map[string]string
	explicitNullPointers []string
}

// Generate creates a deterministic Draft 7 schema. Description keys are RFC
// 6901 JSON pointers, with the empty string naming the root object. Each final
// argument is a values path that has an explicit null default.
func Generate(defaults map[string]any, descriptions map[string]string, usage *analyze.Usage, nullDefaults ...[]string) ([]byte, error) {
	if defaults == nil {
		defaults = map[string]any{}
	}
	if usage == nil {
		usage = &analyze.Usage{}
	}
	if usage.Items != nil {
		return nil, fmt.Errorf("schema for /: values root cannot be an array")
	}

	root := &document{
		Schema:      draft7,
		Type:        "object",
		Description: descriptions[""],
	}
	b := builder{
		descriptions:         descriptions,
		explicitNullPointers: make([]string, len(nullDefaults)),
	}
	for index, valuePath := range nullDefaults {
		pointer := ""
		for _, name := range valuePath {
			pointer = joinPointer(pointer, name)
		}
		b.explicitNullPointers[index] = pointer
	}
	if err := b.buildObject(root, defaults, usage, "", usage.Open, usage.Open); err != nil {
		return nil, err
	}
	for _, valuePath := range nullDefaults {
		permitNullAtPath(root, valuePath)
	}

	return encode(root)
}

// Combine returns one schema that accepts every supplied generated schema.
// This supports dependency aliases that share one physical chart directory.
func Combine(schemas ...[]byte) ([]byte, error) {
	if len(schemas) == 0 {
		return nil, fmt.Errorf("combine schemas: no schemas supplied")
	}
	if len(schemas) == 1 {
		return bytes.Clone(schemas[0]), nil
	}

	alternatives := make([]*document, 0, len(schemas))
	for index, schemaJSON := range schemas {
		var alternative document
		if err := json.Unmarshal(schemaJSON, &alternative); err != nil {
			return nil, fmt.Errorf("combine schema %d: %w", index+1, err)
		}
		alternative.Schema = ""
		alternatives = append(alternatives, &alternative)
	}
	return encode(&document{Schema: draft7, AnyOf: alternatives})
}

// AllowsUnknownRootProperties reports whether the generated root object can
// accept a property name without a fixed template reference.
func AllowsUnknownRootProperties(defaults map[string]any, usage *analyze.Usage) bool {
	if usage == nil {
		return false
	}
	return allowsUnnamedProperties(defaults, usage, usage.Open)
}

// encode writes one compact schema with a final newline. Compact output avoids
// Helm's chart-file size limit for schemas with many nested properties.
func encode(root *document) ([]byte, error) {
	var output bytes.Buffer
	encoder := json.NewEncoder(&output)
	encoder.SetEscapeHTML(false)
	if err := encoder.Encode(root); err != nil {
		return nil, fmt.Errorf("encode schema: %w", err)
	}
	return output.Bytes(), nil
}

// permitNullAtPath adds null to one fixed property path. Object alternatives
// are searched because template evidence can give a value more than one shape.
func permitNullAtPath(current *document, valuePath []string) {
	if current == nil {
		return
	}
	if len(valuePath) == 0 {
		permitNull(current)
		return
	}
	if current.Properties != nil {
		if child := (*current.Properties)[valuePath[0]]; child != nil {
			permitNullAtPath(child, valuePath[1:])
		}
	}
	for _, alternative := range current.AnyOf {
		permitNullAtPath(alternative, valuePath)
	}
}

// permitNull wraps a schema in a null alternative when it does not already
// accept null. It keeps annotations on the outer schema.
func permitNull(target *document) {
	if documentAllowsNull(target) {
		return
	}
	nullValue := json.RawMessage("null")
	original := *target
	description := original.Description
	defaultValue := original.Default
	original.Description = ""
	original.Default = nil
	*target = document{
		Description: description,
		Default:     defaultValue,
		AnyOf: []*document{
			{Const: &nullValue},
			&original,
		},
	}
}

// documentAllowsNull reports whether a schema has a direct null type,
// constant, or alternative.
func documentAllowsNull(value *document) bool {
	if value == nil {
		return false
	}
	if value.Const != nil && string(*value.Const) == "null" {
		return true
	}
	switch typed := value.Type.(type) {
	case string:
		if typed == "null" {
			return true
		}
	case []string:
		for _, name := range typed {
			if name == "null" {
				return true
			}
		}
	}
	for _, alternative := range value.AnyOf {
		if documentAllowsNull(alternative) {
			return true
		}
	}
	return false
}

// buildValue combines one default node with its usage node. It selects fixed,
// configurable, open, or shape-alternative schema rules.
func (b *builder) buildValue(value any, exists bool, usage *analyze.Usage, pointer string, inheritedUsed, inheritedOpen bool) (*document, error) {
	directUsage := usage != nil
	if usage == nil && !inheritedUsed && !inheritedOpen {
		if !exists {
			return &document{}, nil
		}
		kind, _, _, err := inspectValue(value, true)
		if err != nil {
			return nil, pathError(pointer, "invalid default", err)
		}
		if kind != kindObject || !b.hasExplicitNullDescendant(pointer) {
			constant, err := rawValue(value)
			if err != nil {
				return nil, pathError(pointer, "default cannot be represented as JSON", err)
			}
			return &document{Const: constant}, nil
		}
	}
	if usage == nil {
		usage = &analyze.Usage{}
	}

	result := &document{Description: b.descriptions[pointer]}
	open := inheritedOpen || usage.Open
	used := inheritedUsed || open
	wantsObject := len(usage.Properties) > 0 || usage.Additional != nil
	wantsArray := usage.Items != nil
	hasElements := usage.Elements != nil || usage.Iterated

	kind, object, items, err := inspectValue(value, exists)
	if err != nil {
		return nil, pathError(pointer, "invalid default", err)
	}
	// Complete use of a value with no default provides no type evidence. It
	// can validly be a scalar, object, array, or null.
	if kind == kindMissing && open {
		return result, nil
	}
	if hasElements {
		if err := b.buildElementAlternatives(result, value, exists, kind, object, items, usage, pointer, used, inheritedOpen); err != nil {
			return nil, err
		}
		return result, nil
	}
	if wantsObject && wantsArray ||
		kind == kindArray && wantsObject ||
		kind == kindObject && wantsArray ||
		kind == kindScalar && (wantsObject || wantsArray) {
		if err := b.buildShapeAlternatives(result, value, exists, kind, object, items, usage, pointer, used, inheritedOpen); err != nil {
			return nil, err
		}
		return result, nil
	}

	switch kind {
	case kindMissing:
		switch {
		case wantsObject:
			result.Type = []string{"object", "null"}
			if err := b.buildObject(result, map[string]any{}, usage, pointer, used, open); err != nil {
				return nil, err
			}
		case wantsArray:
			result.Type = []string{"array", "null"}
			result.Items, err = b.buildUniformSchema(nil, usage.Items, pointer)
			if err != nil {
				return nil, err
			}
		}
	case kindNull:
		if configurable(usage, used) {
			defaultValue, err := rawValue(nil)
			if err != nil {
				return nil, pathError(pointer, "default cannot be represented as JSON", err)
			}
			result.Default = defaultValue
		}
		switch {
		case wantsObject:
			result.Type = []string{"object", "null"}
			if err := b.buildObject(result, map[string]any{}, usage, pointer, used, open); err != nil {
				return nil, err
			}
		case wantsArray:
			result.Type = []string{"array", "null"}
			result.Items, err = b.buildUniformSchema(nil, usage.Items, pointer)
			if err != nil {
				return nil, err
			}
		}
	case kindObject:
		if wantsArray {
			return nil, pathError(pointer, "default is an object but template usage requires an array", nil)
		}
		result.Type = "object"
		if configurable(usage, used) {
			defaultValue, err := rawValue(value)
			if err != nil {
				return nil, pathError(pointer, "default cannot be represented as JSON", err)
			}
			result.Default = defaultValue
		}
		if err := b.buildObject(result, object, usage, pointer, used, open); err != nil {
			return nil, err
		}
	case kindArray:
		if inheritedOpen && !directUsage {
			if exists {
				defaultValue, err := rawValue(value)
				if err != nil {
					return nil, pathError(pointer, "default cannot be represented as JSON", err)
				}
				result.Default = defaultValue
			}
			return result, nil
		}
		if wantsObject {
			return nil, pathError(pointer, "default is an array but "+objectEvidence(usage), nil)
		}
		if configurable(usage, used) {
			defaultValue, err := rawValue(value)
			if err != nil {
				return nil, pathError(pointer, "default cannot be represented as JSON", err)
			}
			result.Default = defaultValue
		}
		strictItems := wantsArray && !open
		if strictItems {
			itemSchema, err := b.buildUniformSchema(items, usage.Items, pointer)
			if err != nil {
				return nil, err
			}
			if err := setReplacementArray(result, value, itemSchema, pointer); err != nil {
				return nil, err
			}
		} else if open {
			result.Type = "array"
			result.Items = &document{}
		} else {
			result.Type = "array"
		}
	case kindScalar:
		if wantsObject {
			return nil, pathError(pointer, "default is a scalar but template usage requires an object", nil)
		}
		if wantsArray {
			return nil, pathError(pointer, "default is a scalar but template usage requires an array", nil)
		}
		if !inheritedOpen || directUsage {
			if scalarType := scalarTypeEvidence(value); scalarType != "" {
				result.Type = scalarType
			}
		}
		if configurable(usage, used) {
			defaultValue, err := rawValue(value)
			if err != nil {
				return nil, pathError(pointer, "default cannot be represented as JSON", err)
			}
			result.Default = defaultValue
		}
	}

	return result, nil
}

// hasExplicitNullDescendant reports whether a raw null default exists below
// one object. Such objects need property schemas for both Helm value forms.
func (b *builder) hasExplicitNullDescendant(pointer string) bool {
	prefix := pointer + "/"
	for _, nullPointer := range b.explicitNullPointers {
		if strings.HasPrefix(nullPointer, prefix) {
			return true
		}
	}
	return false
}

// objectEvidence describes why template use requires an object shape.
func objectEvidence(usage *analyze.Usage) string {
	if usage == nil {
		return "template usage requires an object"
	}
	if len(usage.Properties) > 0 {
		return "templates select object fields " + strings.Join(sortedMapKeys(usage.Properties), ", ")
	}
	return "templates use dynamically named object fields"
}

// buildElementAlternatives emits object and array choices for shape-neutral
// element use from range or dynamic index operations.
func (b *builder) buildElementAlternatives(
	result *document,
	value any,
	exists bool,
	kind inspectedKind,
	objectDefaults map[string]any,
	itemDefaults []any,
	usage *analyze.Usage,
	pointer string,
	inheritedUsed bool,
	inheritedOpen bool,
) error {
	if exists && configurable(usage, inheritedUsed) {
		defaultValue, err := rawValue(value)
		if err != nil {
			return pathError(pointer, "default cannot be represented as JSON", err)
		}
		result.Default = defaultValue
	}

	object, err := b.buildObjectAlternative(kind, objectDefaults, usage, pointer, inheritedUsed, inheritedOpen)
	if err != nil {
		return err
	}

	array := &document{Type: "array"}
	elementUsage := replacementElementUsage(usage)
	arrayOpen := inheritedOpen || usage.Open
	if arrayOpen {
		array.Items = &document{}
	} else {
		if kind != kindArray {
			itemDefaults = nil
		}
		items, err := b.buildUniformSchema(itemDefaults, elementUsage, pointer)
		if err != nil {
			return err
		}
		array.Items = items
	}

	alternatives := make([]*document, 0, 3)
	if !exists {
		nullValue := json.RawMessage("null")
		alternatives = append(alternatives, &document{Const: &nullValue})
	}
	if exists && kind != kindObject {
		if kind == kindScalar && usage.Open {
			alternatives = append(alternatives, scalarEvidenceDocument(value))
		} else {
			original, err := rawValue(value)
			if err != nil {
				return pathError(pointer, "default cannot be represented as JSON", err)
			}
			alternatives = append(alternatives, &document{Const: original})
		}
	}
	result.AnyOf = append(alternatives, object, array)
	return nil
}

// buildShapeAlternatives emits all concrete shapes required by usage evidence.
// It can retain an incompatible default as an exact constant choice.
func (b *builder) buildShapeAlternatives(
	result *document,
	value any,
	exists bool,
	kind inspectedKind,
	objectDefaults map[string]any,
	itemDefaults []any,
	usage *analyze.Usage,
	pointer string,
	inheritedUsed bool,
	inheritedOpen bool,
) error {
	if exists && configurable(usage, inheritedUsed) {
		defaultValue, err := rawValue(value)
		if err != nil {
			return pathError(pointer, "default cannot be represented as JSON", err)
		}
		result.Default = defaultValue
	}

	wantsObject := len(usage.Properties) > 0 || usage.Additional != nil
	wantsArray := usage.Items != nil
	alternatives := make([]*document, 0, 3)
	defaultShapeRequested := kind == kindObject && wantsObject || kind == kindArray && wantsArray
	if exists && !defaultShapeRequested {
		fallback, err := defaultShapeSchema(value, kind, configurable(usage, inheritedUsed))
		if err != nil {
			return pathError(pointer, "default cannot be represented as JSON", err)
		}
		alternatives = append(alternatives, fallback)
	}

	if wantsObject {
		object, err := b.buildObjectAlternative(kind, objectDefaults, usage, pointer, inheritedUsed, inheritedOpen)
		if err != nil {
			return err
		}
		alternatives = append(alternatives, object)
	}

	if wantsArray {
		array := &document{Type: "array"}
		arrayOpen := inheritedOpen || usage.Open
		strictItems := !arrayOpen && hasStructuralUsage(usage.Items)
		if arrayOpen || usage.Items.Empty() {
			array.Items = &document{}
		} else {
			if kind != kindArray {
				itemDefaults = nil
			}
			items, err := b.buildUniformSchema(itemDefaults, usage.Items, pointer)
			if err != nil {
				return err
			}
			array.Items = items
		}
		if kind == kindArray && (!arrayOpen || strictItems) {
			if err := setReplacementArray(array, value, array.Items, pointer); err != nil {
				return err
			}
		}
		alternatives = append(alternatives, array)
	}

	result.AnyOf = alternatives
	return nil
}

// buildObjectAlternative creates the object branch of a multi-shape schema.
// Item-only evidence does not apply to this branch.
func (b *builder) buildObjectAlternative(
	kind inspectedKind,
	defaults map[string]any,
	usage *analyze.Usage,
	pointer string,
	inheritedUsed bool,
	inheritedOpen bool,
) (*document, error) {
	if kind != kindObject {
		defaults = map[string]any{}
	}
	objectUsage := &analyze.Usage{
		Read:         usage.Read,
		Exact:        usage.Exact,
		AllowUnknown: usage.AllowUnknown,
		Open:         usage.Open,
		Iterated:     usage.Iterated,
		Properties:   usage.Properties,
		Additional:   usage.Additional,
		Elements:     usage.Elements,
	}
	open := inheritedOpen || usage.Open
	result := &document{Type: "object"}
	if err := b.buildObject(result, defaults, objectUsage, pointer, inheritedUsed || open, open); err != nil {
		return nil, err
	}
	return result, nil
}

// setReplacementArray keeps the complete default list as one alternative and
// applies the inferred item contract to replacement lists.
func setReplacementArray(result *document, value any, items *document, pointer string) error {
	original, err := rawValue(value)
	if err != nil {
		return pathError(pointer, "default cannot be represented as JSON", err)
	}
	result.Type = "array"
	result.Items = nil
	result.AnyOf = []*document{
		{Const: original},
		{Type: "array", Items: items},
	}
	return nil
}

// defaultShapeSchema returns a configurable type or an exact default constant.
func defaultShapeSchema(value any, kind inspectedKind, configurable bool) (*document, error) {
	if configurable {
		switch kind {
		case kindObject:
			return &document{Type: "object", AdditionalProperties: true}, nil
		case kindArray:
			return &document{Type: "array", Items: &document{}}, nil
		case kindScalar:
			return scalarEvidenceDocument(value), nil
		}
	}
	constant, err := rawValue(value)
	if err != nil {
		return nil, err
	}
	return &document{Const: constant}, nil
}

// buildObject creates named properties and the correct additionalProperties
// rule for fixed, dynamic, iterated, or fully open object use.
func (b *builder) buildObject(result *document, defaults map[string]any, usage *analyze.Usage, pointer string, used, open bool) error {
	properties := make(map[string]*document)
	result.Properties = &properties

	keys := make(map[string]struct{}, len(defaults)+len(usage.Properties))
	for key := range defaults {
		keys[key] = struct{}{}
	}
	for key := range usage.Properties {
		keys[key] = struct{}{}
	}

	dynamicValueUsage := mergeUsage(usage.Additional, usage.Elements)
	for _, key := range sortedMapKeys(keys) {
		value, exists := defaults[key]
		namedUsage := usage.Properties[key]
		childUsage := namedUsage
		if dynamicUsageMatchesKnownProperty(value, namedUsage, dynamicValueUsage) {
			childUsage = mergeUsage(childUsage, dynamicValueUsage)
		}
		childPointer := joinPointer(pointer, key)
		childOpen := open
		var child *document
		var err error
		if namedUsage == nil && dynamicValueUsage != nil && dynamicValueUsage.Open {
			examples := []any(nil)
			if exists {
				examples = []any{value}
			}
			child, err = b.buildUniformSchema(examples, dynamicValueUsage, childPointer)
			if err == nil {
				child.Description = b.descriptions[childPointer]
				if exists {
					child.Default, err = rawValue(value)
				}
			}
		} else {
			child, err = b.buildValue(value, exists, childUsage, childPointer, used || open, childOpen)
		}
		if err != nil {
			return err
		}
		if namedUsage == nil && dynamicValueUsage != nil && dynamicValueUsage.Read && hasStructuralUsage(dynamicValueUsage) {
			// A guarded dynamic entry may be null before the template selects
			// fields from it.
			permitNull(child)
		}
		properties[key] = child
	}

	switch {
	case open:
		result.AdditionalProperties = true
	case dynamicValueUsage != nil:
		// A dynamic key has no literal RFC 6901 pointer from which to take a
		// description. Existing named defaults still use their exact pointers.
		examples := make([]any, 0, len(defaults))
		for _, key := range sortedMapKeys(defaults) {
			examples = append(examples, defaults[key])
		}
		anonymous := builder{}
		additional, err := anonymous.buildUniformSchema(examples, dynamicValueUsage, pointer)
		if err != nil {
			return err
		}
		result.AdditionalProperties = additional
	case allowsUnnamedProperties(defaults, usage, open):
		// Dynamic context use and iteration can depend on new object members. A
		// truth test without a field contract needs new keys only when the
		// default object is empty.
		result.AdditionalProperties = true
	default:
		result.AdditionalProperties = false
	}
	return nil
}

// dynamicUsageMatchesKnownProperty reports whether a dynamic selector's
// structural contract can apply to a property that also has static usage. A
// structurally unrelated dynamic selector must not open an otherwise precise
// known subtree.
func dynamicUsageMatchesKnownProperty(value any, named, dynamic *analyze.Usage) bool {
	if dynamic == nil || named == nil || !hasStructuralUsage(named) || len(dynamic.Properties) == 0 {
		return true
	}
	_, defaults, _, err := inspectValue(value, true)
	if err != nil {
		return true
	}
	for key := range dynamic.Properties {
		if _, exists := defaults[key]; exists {
			return true
		}
		if _, exists := named.Properties[key]; exists {
			return true
		}
	}
	return false
}

// allowsUnnamedProperties reports whether one object boundary accepts names
// without fixed template references.
func allowsUnnamedProperties(defaults map[string]any, usage *analyze.Usage, open bool) bool {
	return open || usage.AllowUnknown || usage.Iterated || usage.Additional != nil ||
		usage.Elements != nil || usage.Read && !hasStructuralUsage(usage) && defaultObjectIsEmpty(defaults)
}

// defaultObjectIsEmpty reports whether Helm removes every direct default
// member during value coalescing. The JSON-null forms include typed nil
// pointers, maps, and slices stored in an interface.
func defaultObjectIsEmpty(defaults map[string]any) bool {
	for _, value := range defaults {
		kind, _, _, err := inspectValue(value, true)
		if err != nil || kind != kindNull {
			return false
		}
	}
	return true
}

// buildUniformSchema builds a schema for values that do not have a fixed key
// or index, such as entries selected from a map or items in a replacement
// list. Defaults are examples for type inference only. Complete dynamic use
// accepts heterogeneous values instead of copying one example's type.
func (b *builder) buildUniformSchema(examples []any, usage *analyze.Usage, pointer string) (*document, error) {
	if usage != nil && (usage.Open || !hasStructuralUsage(usage) && usage.Read) {
		return &document{}, nil
	}
	if len(examples) == 0 {
		return b.buildValue(nil, false, usage, pointer, false, false)
	}

	var uniform *document
	for _, example := range examples {
		projected, projectedExists, err := projectUsedDefault(example, true, usage)
		if err != nil {
			return nil, pathError(pointer, "invalid default example", err)
		}
		// A dynamic selector can inspect only objects even when its candidate
		// defaults also contain scalars or arrays. Such values do not describe
		// the selected entry and therefore provide no schema evidence.
		if !projectedExists {
			continue
		}
		candidate, err := b.buildValue(projected, projectedExists, usage, pointer, false, false)
		if err != nil {
			return nil, err
		}
		removeAnnotations(candidate)
		if uniform == nil {
			uniform = candidate
			continue
		}
		merged, compatible := mergeInferredDocuments(uniform, candidate)
		if !compatible {
			// Conflicting examples prove alternatives, not an unrestricted
			// contract. Preserve each supported shape so unrelated values still
			// fail validation.
			uniform = joinInferredAlternatives(uniform, candidate)
			continue
		}
		uniform = merged
	}
	if uniform == nil {
		return b.buildValue(nil, false, usage, pointer, false, false)
	}
	if usage != nil && usage.Read && hasStructuralUsage(usage) {
		// A guarded dynamic entry can be null: the template reads the entry to
		// decide whether to render it before selecting any fields below it.
		permitNull(uniform)
	}
	return uniform, nil
}

// joinInferredAlternatives returns the union of incompatible example
// contracts. It flattens unions created by earlier examples and removes exact
// duplicates, which keeps generated schemas stable and readable.
func joinInferredAlternatives(left, right *document) *document {
	alternatives := make([]*document, 0, 4)
	appendAlternative := func(candidate *document) {
		for _, existing := range alternatives {
			if reflect.DeepEqual(existing, candidate) {
				return
			}
		}
		alternatives = append(alternatives, candidate)
	}
	for _, candidate := range []*document{left, right} {
		if candidate != nil && candidate.Type == nil && candidate.Const == nil &&
			candidate.Properties == nil && candidate.Items == nil &&
			candidate.AdditionalProperties == nil && len(candidate.AnyOf) > 0 {
			for _, alternative := range candidate.AnyOf {
				appendAlternative(alternative)
			}
			continue
		}
		appendAlternative(candidate)
	}
	return &document{AnyOf: alternatives}
}

// mergeInferredDocuments combines type evidence from two default examples.
// An empty document carries no type evidence, so another example can provide
// it. Conflicting concrete evidence makes the uniform schema unsafe.
func mergeInferredDocuments(left, right *document) (*document, bool) {
	if emptyDocument(left) {
		return right, true
	}
	if emptyDocument(right) {
		return left, true
	}
	if reflect.DeepEqual(left, right) {
		return left, true
	}
	if left == nil || right == nil || left.Schema != right.Schema ||
		left.Description != right.Description || !reflect.DeepEqual(left.Type, right.Type) ||
		!reflect.DeepEqual(left.Default, right.Default) || !reflect.DeepEqual(left.Const, right.Const) ||
		len(left.AnyOf) != len(right.AnyOf) {
		return nil, false
	}

	merged := &document{
		Schema:      left.Schema,
		Type:        left.Type,
		Description: left.Description,
		Default:     left.Default,
		Const:       left.Const,
	}
	if len(left.AnyOf) > 0 {
		merged.AnyOf = make([]*document, len(left.AnyOf))
		for index := range left.AnyOf {
			alternative, ok := mergeInferredDocuments(left.AnyOf[index], right.AnyOf[index])
			if !ok {
				return nil, false
			}
			merged.AnyOf[index] = alternative
		}
	}

	properties, ok := mergeInferredProperties(left.Properties, right.Properties)
	if !ok {
		return nil, false
	}
	merged.Properties = properties
	merged.Items, ok = mergeOptionalInferredDocuments(left.Items, right.Items)
	if !ok {
		return nil, false
	}
	merged.AdditionalProperties, ok = mergeInferredAdditionalProperties(left.AdditionalProperties, right.AdditionalProperties)
	if !ok {
		return nil, false
	}
	return merged, true
}

// mergeInferredProperties combines compatible property evidence by name.
func mergeInferredProperties(left, right *map[string]*document) (*map[string]*document, bool) {
	if left == nil || right == nil {
		if left == nil && right == nil {
			return nil, true
		}
		return nil, false
	}
	merged := maps.Clone(*left)
	for name, rightSchema := range *right {
		leftSchema, exists := merged[name]
		if !exists {
			merged[name] = rightSchema
			continue
		}
		schema, ok := mergeInferredDocuments(leftSchema, rightSchema)
		if !ok {
			return nil, false
		}
		merged[name] = schema
	}
	return &merged, true
}

// mergeOptionalInferredDocuments combines item schemas when both sides exist.
func mergeOptionalInferredDocuments(left, right *document) (*document, bool) {
	if left == nil || right == nil {
		if left == nil && right == nil {
			return nil, true
		}
		return nil, false
	}
	return mergeInferredDocuments(left, right)
}

// mergeInferredAdditionalProperties combines equal booleans or document rules.
func mergeInferredAdditionalProperties(left, right any) (any, bool) {
	if reflect.DeepEqual(left, right) {
		return left, true
	}
	leftSchema, leftIsSchema := left.(*document)
	rightSchema, rightIsSchema := right.(*document)
	if !leftIsSchema || !rightIsSchema {
		return nil, false
	}
	return mergeInferredDocuments(leftSchema, rightSchema)
}

// projectUsedDefault removes unused fields from a type-inference example.
// This prevents default-only fields from entering replacement item schemas.
func projectUsedDefault(value any, exists bool, usage *analyze.Usage) (any, bool, error) {
	if usage == nil || !exists {
		return nil, false, nil
	}
	kind, object, items, err := inspectValue(value, exists)
	if err != nil {
		return nil, false, err
	}
	switch kind {
	case kindObject:
		if usage.Items != nil && len(usage.Properties) == 0 && usage.Additional == nil {
			return nil, false, nil
		}
		if usage.Open {
			return value, true, nil
		}
		projected := make(map[string]any)
		for name, childUsage := range usage.Properties {
			child, found := object[name]
			child, keep, err := projectUsedDefault(child, found, childUsage)
			if err != nil {
				return nil, false, err
			}
			if keep {
				projected[name] = child
			}
		}
		dynamicValueUsage := mergeUsage(usage.Additional, usage.Elements)
		if dynamicValueUsage != nil {
			for name, child := range object {
				if _, named := usage.Properties[name]; named {
					continue
				}
				child, keep, err := projectUsedDefault(child, true, dynamicValueUsage)
				if err != nil {
					return nil, false, err
				}
				if keep {
					projected[name] = child
				}
			}
		}
		return projected, true, nil
	case kindArray:
		if (len(usage.Properties) > 0 || usage.Additional != nil) && usage.Items == nil {
			return nil, false, nil
		}
		if usage.Open {
			return value, true, nil
		}
		itemUsage := mergeUsage(usage.Items, usage.Elements)
		if itemUsage == nil {
			return []any{}, true, nil
		}
		projected := make([]any, 0, len(items))
		for _, item := range items {
			item, keep, err := projectUsedDefault(item, true, itemUsage)
			if err != nil {
				return nil, false, err
			}
			if keep {
				projected = append(projected, item)
			}
		}
		return projected, true, nil
	case kindScalar, kindNull:
		if len(usage.Properties) > 0 || usage.Additional != nil || usage.Items != nil {
			return nil, false, nil
		}
		return value, true, nil
	default:
		return value, true, nil
	}
}

// removeAnnotations removes example-specific defaults, constants, and
// descriptions from a reusable item schema.
func removeAnnotations(schema *document) {
	if schema == nil {
		return
	}
	schema.Description = ""
	schema.Default = nil
	schema.Const = nil
	filtered := schema.AnyOf[:0]
	for _, alternative := range schema.AnyOf {
		hadConst := alternative != nil && alternative.Const != nil
		removeAnnotations(alternative)
		if hadConst && emptyDocument(alternative) {
			continue
		}
		filtered = append(filtered, alternative)
	}
	schema.AnyOf = filtered
	if schema.Properties != nil {
		for _, property := range *schema.Properties {
			removeAnnotations(property)
		}
	}
	removeAnnotations(schema.Items)
	if additional, ok := schema.AdditionalProperties.(*document); ok {
		removeAnnotations(additional)
	}
}

// emptyDocument reports whether a document has no schema keywords.
func emptyDocument(schema *document) bool {
	return schema != nil && schema.Schema == "" && schema.Type == nil && schema.Description == "" &&
		schema.Default == nil && schema.Const == nil && len(schema.AnyOf) == 0 &&
		schema.Properties == nil && schema.Items == nil && schema.AdditionalProperties == nil
}

// mergeUsage creates a union of two usage subtrees without changing either
// input.
func mergeUsage(left, right *analyze.Usage) *analyze.Usage {
	if left == nil {
		return right
	}
	if right == nil {
		return left
	}

	merged := &analyze.Usage{
		Read:         left.Read || right.Read,
		Exact:        left.Exact || right.Exact,
		AllowUnknown: left.AllowUnknown || right.AllowUnknown,
		Open:         left.Open || right.Open,
		Iterated:     left.Iterated || right.Iterated,
		Properties:   maps.Clone(left.Properties),
		Additional:   mergeUsage(left.Additional, right.Additional),
		Items:        mergeUsage(left.Items, right.Items),
		Elements:     mergeUsage(left.Elements, right.Elements),
	}
	if merged.Properties == nil {
		merged.Properties = make(map[string]*analyze.Usage)
	}
	for key, child := range right.Properties {
		merged.Properties[key] = mergeUsage(merged.Properties[key], child)
	}
	return merged
}

// hasStructuralUsage reports whether templates define fields or items below a
// value. This evidence can define a strict contract without complete use.
func hasStructuralUsage(usage *analyze.Usage) bool {
	return usage != nil && (len(usage.Properties) > 0 || usage.Additional != nil || usage.Items != nil || usage.Elements != nil)
}

// replacementElementUsage returns the rule for each replacement list item.
// Iteration without item reads permits values of all JSON shapes.
func replacementElementUsage(usage *analyze.Usage) *analyze.Usage {
	result := mergeUsage(usage.Items, usage.Elements)
	if result == nil && usage.Iterated {
		// The collection membership affects rendering even when the body does
		// not consume an element value. A replacement can contain values of any
		// JSON shape.
		return &analyze.Usage{Read: true}
	}
	return result
}

// configurable reports whether one node can differ from its default.
func configurable(usage *analyze.Usage, inheritedUsed bool) bool {
	return inheritedUsed || usage.Read || usage.Exact || usage.AllowUnknown || usage.Open || usage.Iterated
}

// inspectedKind identifies the JSON shape of one Go value.
type inspectedKind uint8

// These kinds distinguish absent, null, object, array, and scalar values.
const (
	kindMissing inspectedKind = iota
	kindNull
	kindObject
	kindArray
	kindScalar
)

// inspectValue classifies a Go value and converts maps and arrays into generic
// containers for recursive schema construction.
func inspectValue(value any, exists bool) (inspectedKind, map[string]any, []any, error) {
	if !exists {
		return kindMissing, nil, nil, nil
	}
	if value == nil {
		return kindNull, nil, nil, nil
	}

	rv := reflect.ValueOf(value)
	for rv.Kind() == reflect.Interface || rv.Kind() == reflect.Pointer {
		if rv.IsNil() {
			return kindNull, nil, nil, nil
		}
		rv = rv.Elem()
	}

	switch rv.Kind() {
	case reflect.Map:
		if rv.IsNil() {
			return kindNull, nil, nil, nil
		}
		object := make(map[string]any, rv.Len())
		iterator := rv.MapRange()
		for iterator.Next() {
			key := iterator.Key()
			for key.Kind() == reflect.Interface {
				key = key.Elem()
			}
			if key.Kind() != reflect.String {
				return 0, nil, nil, fmt.Errorf("object key %v is not a string", iterator.Key().Interface())
			}
			object[key.String()] = iterator.Value().Interface()
		}
		return kindObject, object, nil, nil
	case reflect.Slice, reflect.Array:
		if rv.Kind() == reflect.Slice && rv.IsNil() {
			return kindNull, nil, nil, nil
		}
		items := make([]any, rv.Len())
		for index := range rv.Len() {
			items[index] = rv.Index(index).Interface()
		}
		return kindArray, nil, items, nil
	default:
		return kindScalar, nil, nil, nil
	}
}

// inferScalarType maps a noncontainer Go value to a JSON Schema scalar type.
func inferScalarType(value any) string {
	if value == nil {
		return ""
	}
	if number, ok := value.(json.Number); ok {
		if strings.ContainsAny(number.String(), ".eE") {
			return "number"
		}
		return "integer"
	}
	rv := reflect.ValueOf(value)
	for rv.Kind() == reflect.Interface || rv.Kind() == reflect.Pointer {
		if rv.IsNil() {
			return ""
		}
		rv = rv.Elem()
	}
	switch rv.Kind() {
	case reflect.String:
		return "string"
	case reflect.Bool:
		return "boolean"
	case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64,
		reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64:
		return "integer"
	case reflect.Float32, reflect.Float64:
		return "number"
	default:
		return ""
	}
}

// scalarTypeEvidence returns a scalar type only when the default supplies
// stable override evidence. A string containing a template marker can render
// a value of another JSON type, so it does not prove the string type. The
// reflection walk applies the same rule to aliases and pointers.
func scalarTypeEvidence(value any) string {
	if value == nil {
		return ""
	}
	rv := reflect.ValueOf(value)
	for rv.Kind() == reflect.Interface || rv.Kind() == reflect.Pointer {
		if rv.IsNil() {
			return ""
		}
		rv = rv.Elem()
	}
	if rv.Kind() == reflect.String && strings.Contains(rv.String(), "{{") {
		return ""
	}
	return inferScalarType(value)
}

// scalarEvidenceDocument creates an unrestricted document when no stable
// scalar type evidence exists. Assigning an empty string to the interface
// field would otherwise emit the invalid JSON Schema form `"type":""`.
func scalarEvidenceDocument(value any) *document {
	result := &document{}
	if scalarType := scalarTypeEvidence(value); scalarType != "" {
		result.Type = scalarType
	}
	return result
}

// rawValue encodes a default or constant with the standard JSON encoder.
func rawValue(value any) (*json.RawMessage, error) {
	encoded, err := json.Marshal(value)
	if err != nil {
		return nil, err
	}
	raw := json.RawMessage(encoded)
	return &raw, nil
}

// joinPointer appends one escaped property to an RFC 6901 JSON pointer.
func joinPointer(parent, key string) string {
	escaped := strings.ReplaceAll(key, "~", "~0")
	escaped = strings.ReplaceAll(escaped, "/", "~1")
	return parent + "/" + escaped
}

// sortedMapKeys returns map keys in stable lexical order.
func sortedMapKeys[V any](values map[string]V) []string {
	return slices.Sorted(maps.Keys(values))
}

// pathError adds the effective values path to a schema error.
func pathError(pointer, message string, cause error) error {
	if pointer == "" {
		pointer = "/"
	}
	if cause != nil {
		return fmt.Errorf("schema for %s: %s: %w", pointer, message, cause)
	}
	return fmt.Errorf("schema for %s: %s", pointer, message)
}
