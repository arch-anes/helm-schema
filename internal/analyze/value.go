package analyze

// This file defines abstract values and their selection operations. Abstract
// values preserve all possible origins without reading concrete chart values.

import (
	"fmt"
	"maps"
	"slices"
	"strconv"
	"strings"
)

// segmentKind identifies one selection step within a chart-values reference.
type segmentKind uint8

// These segment kinds represent fixed and dynamic collection selections.
const (
	propertySegment segmentKind = iota
	additionalSegment
	itemSegment
	elementSegment
)

// segment stores one reference step and its fixed property name, if present.
type segment struct {
	kind segmentKind
	name string
}

// reference identifies a path that starts at the selected chart's values root.
type reference struct {
	segments  []segment
	scopeRoot bool
}

// referenceForProperties creates a reference from literal property names.
func referenceForProperties(names ...string) reference {
	result := reference{segments: make([]segment, 0, len(names))}
	for _, name := range names {
		result.segments = append(result.segments, segment{kind: propertySegment, name: name})
	}
	return result
}

// referenceForScope creates a reference to one chart's complete values root.
// The marker keeps a dependency root distinct from the same path selected in
// its parent chart.
func referenceForScope(names ...string) reference {
	result := referenceForProperties(names...)
	result.scopeRoot = true
	return result
}

// append returns a copied reference with one additional segment.
func (r reference) append(part segment) reference {
	segments := slices.Clone(r.segments)
	segments = append(segments, part)
	return reference{segments: segments}
}

// belowRoot reports whether the reference selects a value below its current
// chart root instead of the complete values object.
func (r reference) belowRoot() bool {
	return !r.scopeRoot
}

// atomKind identifies one possible abstract value representation.
type atomKind uint8

// These atom kinds represent unknowns, constants, origins, objects, and lists.
const (
	unknownAtom atomKind = iota
	constantAtom
	referenceAtom
	objectAtom
	listAtom
)

// atom stores one possible constant, origin, object, or list representation.
type atom struct {
	kind       atomKind
	serialized bool
	constant   any
	reference  reference
	fields     map[string]value
	fallback   *value
	dynamic    *value
	excluded   map[string]bool
	elements   []value
	item       *value
}

// serializedValue marks a conversion that accepts every JSON-compatible value
// shape. Later string transforms retain this marker until output consumes it.
func serializeValue(input value) value {
	for index := range input.atoms {
		input.atoms[index].serialized = true
	}
	return input
}

// value stores every abstract alternative that an expression can produce.
// Copied is true after deepCopy so changes to a copied root context can be
// tracked without treating the original chart root as mutable helper data.
type value struct {
	atoms  []atom
	copied bool
}

// unknownValue creates a value with no known constant or value origin.
func unknownValue() value {
	return value{atoms: []atom{{kind: unknownAtom}}}
}

// constantValue creates a value with one immutable constant.
func constantValue(constant any) value {
	return value{atoms: []atom{{kind: constantAtom, constant: constant}}}
}

// referenceValue creates a value that points to one values path.
func referenceValue(reference reference) value {
	return value{atoms: []atom{{kind: referenceAtom, reference: reference}}}
}

// objectValue creates an object with fixed abstract fields.
func objectValue(fields map[string]value) value {
	return value{atoms: []atom{{kind: objectAtom, fields: fields}}}
}

// overlayValue applies fixed additions and removals above a fallback object.
func overlayValue(fields map[string]value, fallback value, excluded map[string]bool) value {
	fallbackCopy := fallback
	return value{atoms: []atom{{
		kind:     objectAtom,
		fields:   fields,
		fallback: &fallbackCopy,
		excluded: excluded,
	}}, copied: fallback.copied}
}

// dynamicObjectValue creates an object whose unknown direct keys all have one
// possible abstract value.
func dynamicObjectValue(field value) value {
	fieldCopy := field
	return value{atoms: []atom{{kind: objectAtom, dynamic: &fieldCopy}}, copied: field.copied}
}

// listValue creates a list with fixed abstract elements.
func listValue(elements []value) value {
	return value{atoms: []atom{{kind: listAtom, elements: elements}}}
}

// itemListValue creates a list with one uniform item origin.
func itemListValue(item value) value {
	itemCopy := item
	return value{atoms: []atom{{kind: listAtom, item: &itemCopy}}}
}

// union combines alternatives and removes duplicate atoms.
func union(values ...value) value {
	result := value{}
	seen := make(map[string]struct{})
	for _, candidate := range values {
		result.copied = result.copied || candidate.copied
		for _, candidateAtom := range candidate.atoms {
			key := atomFingerprint(candidateAtom)
			if _, exists := seen[key]; exists {
				continue
			}
			seen[key] = struct{}{}
			result.atoms = append(result.atoms, candidateAtom)
		}
	}
	if len(result.atoms) == 0 {
		return unknownValue()
	}
	return result
}

// hasOrigins reports whether a value contains a reference to chart values.
func hasOrigins(input value) bool {
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			return true
		case objectAtom:
			for _, field := range inputAtom.fields {
				if hasOrigins(field) {
					return true
				}
			}
			if inputAtom.fallback != nil && hasOrigins(*inputAtom.fallback) {
				return true
			}
			if inputAtom.dynamic != nil && hasOrigins(*inputAtom.dynamic) {
				return true
			}
		case listAtom:
			for _, element := range inputAtom.elements {
				if hasOrigins(element) {
					return true
				}
			}
			if inputAtom.item != nil && hasOrigins(*inputAtom.item) {
				return true
			}
		}
	}
	return false
}

// selectField selects one literal object field from every input alternative.
func selectField(input value, name string) value {
	selected := make([]value, 0, len(input.atoms))
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			selected = append(selected, referenceValue(inputAtom.reference.append(segment{kind: propertySegment, name: name})))
		case objectAtom:
			if field, exists := inputAtom.fields[name]; exists {
				selected = append(selected, field)
				continue
			}
			if inputAtom.excluded[name] {
				selected = append(selected, unknownValue())
				continue
			}
			if inputAtom.fallback != nil {
				selected = append(selected, selectField(*inputAtom.fallback, name))
			}
			if inputAtom.dynamic != nil {
				selected = append(selected, *inputAtom.dynamic)
			}
			if inputAtom.fallback == nil && inputAtom.dynamic == nil {
				selected = append(selected, unknownValue())
			}
		case unknownAtom, constantAtom, listAtom:
			selected = append(selected, unknownValue())
		}
	}
	result := union(selected...)
	result.copied = result.copied || input.copied
	return result
}

// selectProperty selects a literal or dynamically named object property.
func selectProperty(input value, key value) value {
	if stringKeys, ok := stringConstants(key); ok {
		selected := make([]value, 0, len(stringKeys))
		for _, stringKey := range stringKeys {
			selected = append(selected, selectField(input, stringKey))
		}
		result := union(selected...)
		result.copied = result.copied || input.copied
		return result
	}
	selected := make([]value, 0, len(input.atoms))
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			selected = append(selected, referenceValue(inputAtom.reference.append(segment{kind: additionalSegment})))
		case objectAtom:
			for name, field := range inputAtom.fields {
				if !inputAtom.excluded[name] {
					selected = append(selected, field)
				}
			}
			if inputAtom.fallback != nil {
				selected = append(selected, selectProperty(*inputAtom.fallback, key))
			}
			if inputAtom.dynamic != nil {
				selected = append(selected, *inputAtom.dynamic)
			}
		default:
			selected = append(selected, unknownValue())
		}
	}
	result := union(selected...)
	result.copied = result.copied || input.copied
	return result
}

// selectIndex selects a literal property, a list item, or a neutral element.
func selectIndex(input value, key value) value {
	if names, ok := stringConstants(key); ok {
		selected := make([]value, 0, len(names))
		for _, name := range names {
			selected = append(selected, selectField(input, name))
		}
		result := union(selected...)
		result.copied = result.copied || input.copied
		return result
	}
	if index, ok := singleIntegerConstant(key); ok {
		selected := make([]value, 0, len(input.atoms))
		for _, inputAtom := range input.atoms {
			switch inputAtom.kind {
			case referenceAtom:
				selected = append(selected, referenceValue(inputAtom.reference.append(segment{kind: itemSegment})))
			case listAtom:
				if index >= 0 && index < len(inputAtom.elements) {
					selected = append(selected, inputAtom.elements[index])
				} else if inputAtom.item != nil {
					selected = append(selected, *inputAtom.item)
				} else {
					selected = append(selected, unknownValue())
				}
			default:
				selected = append(selected, unknownValue())
			}
		}
		result := union(selected...)
		result.copied = result.copied || input.copied
		return result
	}
	return selectElement(input)
}

// selectElement returns possible map values and list items without assuming a
// collection shape.
func selectElement(input value) value {
	selected := make([]value, 0, len(input.atoms))
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			selected = append(selected, referenceValue(inputAtom.reference.append(segment{kind: elementSegment})))
		case objectAtom:
			for name, field := range inputAtom.fields {
				if !inputAtom.excluded[name] {
					selected = append(selected, field)
				}
			}
			if inputAtom.fallback != nil {
				selected = append(selected, selectElement(*inputAtom.fallback))
			}
			if inputAtom.dynamic != nil {
				selected = append(selected, *inputAtom.dynamic)
			}
		case listAtom:
			selected = append(selected, inputAtom.elements...)
			if inputAtom.item != nil {
				selected = append(selected, *inputAtom.item)
			}
		default:
			selected = append(selected, unknownValue())
		}
	}
	result := union(selected...)
	result.copied = result.copied || input.copied
	return result
}

// rangeItem returns the possible value bound to a range item variable.
func rangeItem(input value) value {
	items := make([]value, 0, len(input.atoms)*2)
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			items = append(items, referenceValue(inputAtom.reference.append(segment{kind: elementSegment})))
		case objectAtom:
			for name, field := range inputAtom.fields {
				if !inputAtom.excluded[name] {
					items = append(items, field)
				}
			}
			if inputAtom.fallback != nil {
				items = append(items, rangeItem(*inputAtom.fallback))
			}
			if inputAtom.dynamic != nil {
				items = append(items, *inputAtom.dynamic)
			}
		case listAtom:
			items = append(items, inputAtom.elements...)
			if inputAtom.item != nil {
				items = append(items, *inputAtom.item)
			}
		default:
			items = append(items, unknownValue())
		}
	}
	result := union(items...)
	result.copied = result.copied || input.copied
	return result
}

// rangeKey returns known map keys and list indexes when they are available.
func rangeKey(input value) value {
	keys := make([]value, 0, len(input.atoms)*2)
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			// The collection observation records that keys or indexes affect the
			// loop. A dynamic key is derived data, not the entry value itself.
			keys = append(keys, unknownValue())
		case objectAtom:
			for name := range inputAtom.fields {
				if !inputAtom.excluded[name] {
					keys = append(keys, constantValue(name))
				}
			}
			if inputAtom.fallback != nil {
				keys = append(keys, rangeKey(*inputAtom.fallback))
			}
		case listAtom:
			for index := range inputAtom.elements {
				keys = append(keys, constantValue(int64(index)))
			}
			if inputAtom.item != nil {
				keys = append(keys, unknownValue())
			}
		default:
			keys = append(keys, unknownValue())
		}
	}
	return union(keys...)
}

// constants returns all alternatives when each atom is a constant.
func constants(input value) ([]any, bool) {
	if len(input.atoms) == 0 {
		return nil, false
	}
	result := make([]any, 0, len(input.atoms))
	for _, inputAtom := range input.atoms {
		if inputAtom.kind != constantAtom {
			return nil, false
		}
		result = append(result, inputAtom.constant)
	}
	return result, true
}

// singleStringConstant returns one string only when it is the sole alternative.
func singleStringConstant(input value) (string, bool) {
	values, ok := constants(input)
	if !ok || len(values) != 1 {
		return "", false
	}
	result, ok := values[0].(string)
	return result, ok
}

// singleIntegerConstant returns one platform int without numeric truncation.
func singleIntegerConstant(input value) (int, bool) {
	values, ok := constants(input)
	if !ok || len(values) != 1 {
		return 0, false
	}
	switch typed := values[0].(type) {
	case int:
		return typed, true
	case int64:
		return int(typed), int64(int(typed)) == typed
	case uint64:
		return int(typed), uint64(int(typed)) == typed
	default:
		return 0, false
	}
}

// valueFingerprint returns a stable identity for all atoms in a value.
func valueFingerprint(input value) string {
	parts := make([]string, 0, len(input.atoms))
	for _, inputAtom := range input.atoms {
		parts = append(parts, atomFingerprint(inputAtom))
	}
	slices.Sort(parts)
	result := strings.Join(parts, "|")
	if input.copied {
		result += "|copy"
	}
	return result
}

// atomFingerprint returns a stable structural identity for one atom.
func atomFingerprint(input atom) string {
	prefix := ""
	if input.serialized {
		prefix = "serialized:"
	}
	switch input.kind {
	case unknownAtom:
		return prefix + "?"
	case constantAtom:
		return prefix + "c:" + fmt.Sprintf("%T:%v", input.constant, input.constant)
	case referenceAtom:
		var result strings.Builder
		result.WriteString(prefix + "r:")
		if input.reference.scopeRoot {
			result.WriteString("root:")
		}
		for _, part := range input.reference.segments {
			switch part.kind {
			case propertySegment:
				result.WriteString(".")
				result.WriteString(strconv.Quote(part.name))
			case additionalSegment:
				result.WriteString(".*")
			case itemSegment:
				result.WriteString(".[]")
			case elementSegment:
				result.WriteString(".[*]")
			}
		}
		return result.String()
	case objectAtom:
		names := slices.Sorted(maps.Keys(input.fields))
		var result strings.Builder
		result.WriteString(prefix + "o:{")
		for _, name := range names {
			result.WriteString(strconv.Quote(name))
			result.WriteString(":")
			result.WriteString(valueFingerprint(input.fields[name]))
			result.WriteString(",")
		}
		if input.fallback != nil {
			result.WriteString("...:")
			result.WriteString(valueFingerprint(*input.fallback))
		}
		if input.dynamic != nil {
			result.WriteString("*:")
			result.WriteString(valueFingerprint(*input.dynamic))
		}
		if len(input.excluded) > 0 {
			excluded := slices.Sorted(maps.Keys(input.excluded))
			result.WriteString("-:")
			result.WriteString(strings.Join(excluded, ","))
		}
		result.WriteString("}")
		return result.String()
	case listAtom:
		var result strings.Builder
		result.WriteString(prefix + "l:[")
		for _, element := range input.elements {
			result.WriteString(valueFingerprint(element))
			result.WriteString(",")
		}
		if input.item != nil {
			result.WriteString("...:")
			result.WriteString(valueFingerprint(*input.item))
		}
		result.WriteString("]")
		return result.String()
	default:
		return "?"
	}
}
