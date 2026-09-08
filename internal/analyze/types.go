package analyze

// This file defines the analyzer inputs, diagnostics, value flows, and usage
// tree. Other analyzer files operate on these types.

import (
	"fmt"
	"maps"
	"slices"
)

// Template is one Helm template source file.
//
// Name identifies the source and its parsed tree. Chart files use Helm's
// template name. Deferred values use a synthetic source name. Entry reports
// whether Helm executes the top-level body. ValuesPrefix maps .Values into the
// selected root chart. Context contains immutable root fields. BasePath
// supplies .Template.BasePath. DeferredValuePath identifies template text
// from a values default. The analyzer parses that text only after it reaches
// tpl.
type Template struct {
	Name              string
	Content           []byte
	Entry             bool
	DeferredValuePath []ValuePathStep
	ValuesPrefix      []string
	BasePath          string
	Context           map[string]any
	Subcharts         map[string]Scope
}

// ValuePathStep describes one part of a path through chart values. Property is
// set for a map key. CollectionItem is set for an element of a list.
type ValuePathStep struct {
	Property       string
	CollectionItem bool
}

// Scope describes a chart context exposed through Helm's .Subcharts object.
// ValuesPrefix maps its .Values object into the selected root chart. Context
// contains immutable fields, and Subcharts contains nested dependency scopes.
type Scope struct {
	ValuesPrefix []string
	Context      map[string]any
	Subcharts    map[string]Scope
}

// Diagnostic describes a place where analysis had to use a less precise,
// conservative result.
type Diagnostic struct {
	Template string
	Line     int
	Column   int
	Message  string
}

// String formats a diagnostic with its available source location.
func (d Diagnostic) String() string {
	if d.Template == "" {
		return d.Message
	}
	if d.Line <= 0 {
		return fmt.Sprintf("%s: %s", d.Template, d.Message)
	}
	if d.Column <= 0 {
		return fmt.Sprintf("%s:%d: %s", d.Template, d.Line, d.Message)
	}
	return fmt.Sprintf("%s:%d:%d: %s", d.Template, d.Line, d.Column, d.Message)
}

// Usage describes how templates consume one value node.
//
// Properties holds literal object keys. Additional describes dynamically named
// object properties. Items describes list items. Elements describes values
// selected from a collection whose map-or-list shape is not yet known.
// Iterated means collection membership affects execution. Read means the value
// itself affects output or control flow. Exact means the selected value affects
// output without making unsupported descendants valid. AllowUnknown means new
// direct properties can affect the result. Open means that an operation
// consumes the complete selected value. Structural evidence below that value
// also consumes all descendants below that value. Serialized means the complete
// value is converted without requiring a particular JSON shape.
type Usage struct {
	Read         bool
	Exact        bool
	AllowUnknown bool
	Open         bool
	Serialized   bool
	Iterated     bool
	Properties   map[string]*Usage
	Additional   *Usage
	Items        *Usage
	Elements     *Usage
}

// NewUsage creates an empty usage node with an initialized property map.
func NewUsage() *Usage {
	return &Usage{Properties: make(map[string]*Usage)}
}

// Empty reports whether a node contains no usage evidence.
func (u *Usage) Empty() bool {
	return u == nil || (!u.Read && !u.Exact && !u.AllowUnknown && !u.Open && !u.Serialized && !u.Iterated && len(u.Properties) == 0 && u.Additional == nil && u.Items == nil && u.Elements == nil)
}

// Merge adds all evidence from other to u. Merge is monotonic: it never clears
// evidence already present in u.
func (u *Usage) Merge(other *Usage) {
	if u == nil || other == nil {
		return
	}
	u.Read = u.Read || other.Read
	u.Exact = u.Exact || other.Exact
	u.AllowUnknown = u.AllowUnknown || other.AllowUnknown
	u.Open = u.Open || other.Open
	u.Serialized = u.Serialized || other.Serialized
	u.Iterated = u.Iterated || other.Iterated
	if u.Properties == nil {
		u.Properties = make(map[string]*Usage)
	}
	for name, child := range other.Properties {
		destination := u.Properties[name]
		if destination == nil {
			destination = NewUsage()
			u.Properties[name] = destination
		}
		destination.Merge(child)
	}
	if other.Additional != nil {
		if u.Additional == nil {
			u.Additional = NewUsage()
		}
		u.Additional.Merge(other.Additional)
	}
	if other.Items != nil {
		if u.Items == nil {
			u.Items = NewUsage()
		}
		u.Items.Merge(other.Items)
	}
	if other.Elements != nil {
		if u.Elements == nil {
			u.Elements = NewUsage()
		}
		u.Elements.Merge(other.Elements)
	}
}

// AtPath returns the usage node below a sequence of fixed properties. It
// returns an empty node when the path has no usage evidence.
func (u *Usage) AtPath(path ...string) *Usage {
	for _, name := range path {
		if u == nil {
			return &Usage{}
		}
		u = u.Properties[name]
	}
	if u == nil {
		return &Usage{}
	}
	return u
}

// sortedPropertyNames returns property names in stable lexical order.
func sortedPropertyNames(properties map[string]*Usage) []string {
	return slices.Sorted(maps.Keys(properties))
}
