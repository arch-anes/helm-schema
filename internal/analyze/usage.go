package analyze

// This file converts observations on abstract values into nodes in the usage
// tree.

// observation identifies how an operation uses a chart value.
type observation uint8

// These observations range from direct reads to collection iteration.
const (
	readValue observation = iota
	exactValue
	openValue
	contextValue
	iterateValue
)

// record adds one observation at a referenced value path.
func (u *Usage) record(reference reference, mode observation) {
	current := u
	for _, part := range reference.segments {
		switch part.kind {
		case propertySegment:
			if current.Properties == nil {
				current.Properties = make(map[string]*Usage)
			}
			next := current.Properties[part.name]
			if next == nil {
				next = NewUsage()
				current.Properties[part.name] = next
			}
			current = next
		case additionalSegment:
			if current.Additional == nil {
				current.Additional = NewUsage()
			}
			current = current.Additional
		case itemSegment:
			if current.Items == nil {
				current.Items = NewUsage()
			}
			current = current.Items
		case elementSegment:
			if current.Elements == nil {
				current.Elements = NewUsage()
			}
			current = current.Elements
		}
	}
	switch mode {
	case readValue:
		current.Read = true
	case exactValue:
		current.Exact = true
	case openValue:
		current.Read = true
		current.Open = true
	case contextValue:
		current.AllowUnknown = true
	case iterateValue:
		current.Iterated = true
	}
}

// observe applies an observation to every value origin in an abstract value.
func (a *analyzer) observe(input value, mode observation) {
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			a.usage.record(inputAtom.reference, mode)
		case objectAtom:
			if mode == openValue || mode == contextValue {
				for _, field := range inputAtom.fields {
					a.observe(field, mode)
				}
			}
			if inputAtom.fallback != nil {
				a.observe(*inputAtom.fallback, mode)
			}
			if inputAtom.dynamic != nil && (mode == openValue || mode == contextValue) {
				a.observe(*inputAtom.dynamic, mode)
			}
		case listAtom:
			if mode == openValue || mode == contextValue {
				for _, element := range inputAtom.elements {
					a.observe(element, mode)
				}
				if inputAtom.item != nil {
					a.observe(*inputAtom.item, mode)
				}
			}
		}
	}
}
