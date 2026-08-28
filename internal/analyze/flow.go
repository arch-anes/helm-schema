package analyze

// This file maps usage through value copies created by dependency imports and
// global values.

import (
	"fmt"
	"slices"
	"strconv"
	"strings"
)

// maximumFlowStates limits work when metadata contains many or cyclic copies.
const maximumFlowStates = 1_000_000

// ValueFlow states that Helm can copy a value subtree from Source to
// Destination. Both paths need compatible schema rules because one source
// value can appear at either validation path.
type ValueFlow struct {
	Source      []string
	Destination []string
}

// MarkPath records a fixed non-template values path, such as a dependency
// condition.
func (u *Usage) MarkPath(path ...string) {
	if u == nil {
		return
	}
	u.record(referenceForProperties(path...), readValue)
}

// ApplyValueFlows shares usage between both ends of every value copy. Each
// flow is used at most once along one evidence path. This permits transitive
// copies while making cyclic metadata finite.
func ApplyValueFlows(usage *Usage, flows []ValueFlow) error {
	if usage == nil || len(flows) == 0 {
		return nil
	}

	evidence := collectEvidence(usage)
	words := (len(flows) + 63) / 64
	states := 0
	for _, fact := range evidence {
		queue := []flowState{{reference: fact.reference, mode: fact.mode, used: make([]uint64, words)}}
		seen := make(map[string]struct{})
		for len(queue) > 0 {
			state := queue[0]
			queue = queue[1:]
			stateKey := flowStateKey(state)
			if _, exists := seen[stateKey]; exists {
				continue
			}
			seen[stateKey] = struct{}{}
			states++
			if states > maximumFlowStates {
				return fmt.Errorf("value-flow analysis exceeded %d states", maximumFlowStates)
			}

			for index, flow := range flows {
				if flowUsed(state.used, index) {
					continue
				}
				mappings := [][2][]string{
					{flow.Destination, flow.Source},
					{flow.Source, flow.Destination},
				}
				for _, mapping := range mappings {
					mapped, matches := remapPropertyPrefix(state.reference, mapping[0], mapping[1])
					if !matches {
						continue
					}
					usage.record(mapped, state.mode)

					used := slices.Clone(state.used)
					used[index/64] |= uint64(1) << uint(index%64)
					queue = append(queue, flowState{reference: mapped, mode: state.mode, used: used})
				}
			}
		}
	}
	return nil
}

// remapPropertyPrefix replaces one fixed property prefix with another.
func remapPropertyPrefix(input reference, from, to []string) (reference, bool) {
	suffix, matches := stripPropertyPrefix(input.segments, from)
	if !matches {
		return reference{}, false
	}
	mapped := reference{segments: make([]segment, 0, len(to)+len(suffix))}
	for _, name := range to {
		mapped.segments = append(mapped.segments, segment{kind: propertySegment, name: name})
	}
	mapped.segments = append(mapped.segments, suffix...)
	return mapped, true
}

// usageEvidence pairs one value path with one observed use.
type usageEvidence struct {
	reference reference
	mode      observation
}

// collectEvidence flattens a usage tree into observations with value paths.
func collectEvidence(usage *Usage) []usageEvidence {
	result := make([]usageEvidence, 0)
	var walk func(*Usage, []segment)
	walk = func(current *Usage, path []segment) {
		if current == nil {
			return
		}
		if current.Open {
			result = append(result, usageEvidence{reference: reference{segments: slices.Clone(path)}, mode: openValue})
		} else if current.Read {
			result = append(result, usageEvidence{reference: reference{segments: slices.Clone(path)}, mode: readValue})
		} else if current.Exact {
			result = append(result, usageEvidence{reference: reference{segments: slices.Clone(path)}, mode: exactValue})
		}
		if current.AllowUnknown && !current.Open {
			result = append(result, usageEvidence{reference: reference{segments: slices.Clone(path)}, mode: contextValue})
		}
		if current.Iterated {
			result = append(result, usageEvidence{reference: reference{segments: slices.Clone(path)}, mode: iterateValue})
		}
		for _, name := range sortedPropertyNames(current.Properties) {
			walk(current.Properties[name], appendSegment(path, segment{kind: propertySegment, name: name}))
		}
		walk(current.Additional, appendSegment(path, segment{kind: additionalSegment}))
		walk(current.Items, appendSegment(path, segment{kind: itemSegment}))
		walk(current.Elements, appendSegment(path, segment{kind: elementSegment}))
	}
	walk(usage, nil)
	return result
}

// appendSegment returns a copied path with one additional reference segment.
func appendSegment(path []segment, next segment) []segment {
	if next.kind != propertySegment && next.name != "" {
		panic("non-property usage segment has a name")
	}
	return append(slices.Clone(path), next)
}

// stripPropertyPrefix removes an exact property prefix from a reference path.
func stripPropertyPrefix(path []segment, prefix []string) ([]segment, bool) {
	if len(path) < len(prefix) {
		return nil, false
	}
	for index, name := range prefix {
		if path[index].kind != propertySegment || path[index].name != name {
			return nil, false
		}
	}
	return slices.Clone(path[len(prefix):]), true
}

// flowState tracks one observation and the value flows already applied to it.
type flowState struct {
	reference reference
	mode      observation
	used      []uint64
}

// flowUsed reports whether one flow is present in a compact bit set.
func flowUsed(words []uint64, index int) bool {
	return words[index/64]&(uint64(1)<<uint(index%64)) != 0
}

// flowStateKey returns a stable identity for cycle and duplicate detection.
func flowStateKey(state flowState) string {
	var result strings.Builder
	result.WriteString(atomFingerprint(atom{kind: referenceAtom, reference: state.reference}))
	result.WriteByte(':')
	result.WriteString(strconv.Itoa(int(state.mode)))
	for _, word := range state.used {
		result.WriteByte(':')
		result.WriteString(strconv.FormatUint(word, 16))
	}
	return result.String()
}
