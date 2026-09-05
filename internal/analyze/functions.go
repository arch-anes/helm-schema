package analyze

// This file defines transfer rules for Helm, Go template, and Sprig functions.
// Each rule preserves value origins or records how the function consumes them.

import (
	"fmt"
	"maps"
	"strings"
	"text/template/parse"
)

// wholeConsumerFunctions pass complete collection values or entries to their
// result. Unsupported descendants can therefore affect rendered output.
var wholeConsumerFunctions = stringSet(
	"append", "chunk", "concat", "initial", "mustAppend", "mustChunk",
	"mustInitial", "mustPrepend", "mustRest", "mustReverse", "mustSlice",
	"mustUniq", "mustWithout", "pick", "prepend", "rest", "reverse", "slice",
	"sortAlpha", "uniq", "values", "without",
)

// exactConsumerFunctions inspect complete scalar representations without
// establishing valid fields below an object. This includes text produced by a
// prior toYaml or JSON conversion.
var exactConsumerFunctions = stringSet(
	"abbrev", "abbrevboth", "adler32sum", "ago", "b32dec", "b32enc", "b64dec", "b64enc",
	"base", "bcrypt", "buildCustomCert",
	"camelcase", "cat", "contains", "date", "dateInZone", "dateModify",
	"clean", "date_in_zone", "date_modify", "decryptAES", "derivePassword", "dir",
	"duration", "durationRound", "encryptAES", "ext", "genCA", "genCAWithKey",
	"genPrivateKey", "genSelfSignedCertWithKey", "genSignedCert", "genSignedCertWithKey",
	"getHostByName",
	"htmlDate", "htmlDateInZone", "initials", "join", "kebabcase", "lower",
	"htpasswd", "isAbs",
	"mustDateModify", "must_date_modify", "mustRegexFind", "mustRegexFindAll", "mustRegexMatch",
	"mustRegexReplaceAll", "mustRegexReplaceAllLiteral", "mustRegexSplit",
	"mustToDate", "nospace", "plural", "regexFind", "regexFindAll",
	"regexMatch", "regexQuoteMeta", "regexReplaceAll", "regexReplaceAllLiteral",
	"regexSplit", "repeat", "sha1sum", "sha256sum", "shuffle",
	"osBase", "osClean", "osDir", "osExt", "osIsAbs", "sha512sum", "snakecase",
	"split", "splitList", "splitn", "substr", "swapcase", "toDate",
	"toDecimal", "trunc",
	"unixEpoch", "upper", "urlJoin", "urlParse", "wrap", "wrapWith",
	"genSelfSignedCert", "semver",
)

// keyConsumerFunctions inspect collection membership without consuming the
// values stored below each direct key.
var keyConsumerFunctions = stringSet("keys", "len")

// readConsumerFunctions use an argument value without using its descendants.
var readConsumerFunctions = stringSet(
	"add", "add1", "add1f", "addf", "all", "and", "any", "atoi", "biggest",
	"ceil", "compact", "deepEqual", "div", "divf", "eq", "float64",
	"floor", "ge", "gt", "int", "int64", "kindIs", "kindOf", "le", "lt",
	"max", "maxf", "min", "minf", "mod", "mul", "mulf", "ne", "not",
	"or", "randAlpha", "randAlphaNum", "randAscii", "randBytes",
	"randInt", "randNumeric", "round", "semverCompare", "sub", "subf",
	"typeIs", "typeIsLike", "typeOf", "fail", "has", "mustCompact", "mustHas",
	"hasPrefix", "hasSuffix", "seq", "until", "untilStep",
)

// harmlessFunctions return values without consuming chart-value arguments.
var harmlessFunctions = stringSet(
	"hello", "now", "uuidv4",
)

// originPreservingFunctions transform a value without choosing fields from it.
// The caller that consumes the result determines how much usage evidence the
// input creates.
var originPreservingFunctions = stringSet(
	"fromJson", "fromJsonArray", "fromYaml", "fromYamlArray",
	"fromToml", "html", "indent", "js", "nindent", "quote", "squote",
	"mustFromJson", "mustToJson", "mustToPrettyJson", "mustToRawJson",
	"mustToToml", "mustToYaml", "toJson", "toPrettyJson", "toRawJson",
	"toString", "toStrings", "toToml", "toYaml", "toYamlPretty", "replace",
	"title", "trim", "trimAll", "trimPrefix", "trimSuffix", "trimall", "untitle",
	"urlquery",
)

// stringSet creates a lookup set for a function behavior class.
func stringSet(names ...string) map[string]struct{} {
	result := make(map[string]struct{}, len(names))
	for _, name := range names {
		result[name] = struct{}{}
	}
	return result
}

// callFunction applies a named transfer rule. Unknown functions consume only
// arguments that contain chart-value origins.
func (a *analyzer) callFunction(name string, arguments []value, node parse.Node) value {
	if folded, ok := foldPureStringFunction(name, arguments); ok {
		return folded
	}
	switch name {
	case "index":
		return a.callIndex(arguments)
	case "get":
		return a.callGet(arguments)
	case "dig":
		return a.callDig(arguments)
	case "hasKey":
		return a.callHasKey(arguments)
	case "pluck":
		return a.callPluck(arguments)
	case "dict":
		return a.callDict(arguments, node)
	case "list", "tuple":
		return listValue(arguments)
	case "default":
		return a.callDefault(arguments)
	case "coalesce":
		return a.callCoalesce(arguments)
	case "required":
		return a.callRequired(arguments)
	case "empty":
		if len(arguments) > 0 {
			a.observe(arguments[len(arguments)-1], readValue)
		}
		return unknownValue()
	case "ternary":
		if len(arguments) >= 3 {
			a.observe(arguments[2], readValue)
			return union(arguments[0], arguments[1])
		}
		return unknownValue()
	case "deepCopy", "mustDeepCopy":
		if len(arguments) == 0 {
			return unknownValue()
		}
		result := arguments[len(arguments)-1]
		result.copied = true
		return result
	case "merge", "mustMerge", "mergeOverwrite", "mustMergeOverwrite":
		return union(arguments...)
	case "set":
		return a.callSet(arguments, node)
	case "unset":
		return a.callUnset(arguments, node)
	case "omit":
		return a.callOmit(arguments, node)
	case "first", "mustFirst":
		if len(arguments) == 0 {
			return unknownValue()
		}
		return selectIndex(arguments[len(arguments)-1], constantValue(int64(0)))
	case "last", "mustLast":
		if len(arguments) == 0 {
			return unknownValue()
		}
		return selectElement(arguments[len(arguments)-1])
	case "print", "println":
		return a.callPrint(arguments)
	case "printf":
		return a.callPrintf(arguments)
	case "include":
		return a.callInclude(arguments, node)
	case "tpl":
		return a.callTPL(arguments, node)
	case "lookup":
		for _, argument := range arguments {
			a.observe(argument, openValue)
		}
		return unknownValue()
	}

	if _, exists := originPreservingFunctions[name]; exists {
		return union(arguments...)
	}
	if _, exists := exactConsumerFunctions[name]; exists {
		for _, argument := range arguments {
			a.observe(argument, exactValue)
		}
		return unknownValue()
	}
	if _, exists := keyConsumerFunctions[name]; exists {
		for _, argument := range arguments {
			a.observe(argument, contextValue)
		}
		return unknownValue()
	}
	if _, exists := wholeConsumerFunctions[name]; exists {
		for _, argument := range arguments {
			a.observe(argument, openValue)
		}
		return unknownValue()
	}
	if _, exists := readConsumerFunctions[name]; exists {
		for _, argument := range arguments {
			a.observe(argument, readValue)
		}
		if name == "and" || name == "or" {
			return union(arguments...)
		}
		return unknownValue()
	}
	if _, exists := harmlessFunctions[name]; exists {
		return unknownValue()
	}
	if _, exists := knownConservativeFunctions[name]; exists {
		for _, argument := range arguments {
			a.observe(argument, openValue)
		}
		a.addDiagnostic(node, fmt.Sprintf(
			"function %q uses conservative complete-value analysis", name,
		))
		return unknownValue()
	}

	hasValueOrigin := false
	for _, argument := range arguments {
		hasValueOrigin = hasValueOrigin || hasOrigins(argument)
		a.observe(argument, openValue)
	}
	if hasValueOrigin {
		a.addDiagnostic(node, fmt.Sprintf("unknown function %q consumed its complete value arguments", name))
	}
	return unknownValue()
}

// foldPureStringFunction evaluates deterministic standard string operations
// when every argument is a known string. Keeping constant alternatives intact
// lets later get and index calls resolve calculated property names precisely.
func foldPureStringFunction(name string, arguments []value) (value, bool) {
	argumentAlternatives := make([][]string, len(arguments))
	for index, argument := range arguments {
		constants, ok := stringConstants(argument)
		if !ok {
			return value{}, false
		}
		argumentAlternatives[index] = constants
	}

	var apply func([]string) (string, bool)
	switch name {
	case "lower":
		apply = func(values []string) (string, bool) {
			if len(values) != 1 {
				return "", false
			}
			return strings.ToLower(values[0]), true
		}
	case "upper":
		apply = func(values []string) (string, bool) {
			if len(values) != 1 {
				return "", false
			}
			return strings.ToUpper(values[0]), true
		}
	case "trimPrefix":
		apply = func(values []string) (string, bool) {
			if len(values) != 2 {
				return "", false
			}
			return strings.TrimPrefix(values[1], values[0]), true
		}
	case "trimSuffix":
		apply = func(values []string) (string, bool) {
			if len(values) != 2 {
				return "", false
			}
			return strings.TrimSuffix(values[1], values[0]), true
		}
	default:
		return value{}, false
	}

	results := make([]value, 0)
	var visit func(int, []string) bool
	visit = func(index int, selected []string) bool {
		if len(results) > 256 {
			return false
		}
		if index == len(argumentAlternatives) {
			result, ok := apply(selected)
			if !ok {
				return false
			}
			results = append(results, constantValue(result))
			return true
		}
		for _, alternative := range argumentAlternatives[index] {
			if !visit(index+1, append(selected, alternative)) {
				return false
			}
		}
		return true
	}
	if !visit(0, nil) {
		return value{}, false
	}
	return union(results...), true
}

// callIndex applies each key to the preceding abstract value.
func (a *analyzer) callIndex(arguments []value) value {
	if len(arguments) == 0 {
		return unknownValue()
	}
	result := arguments[0]
	for _, key := range arguments[1:] {
		a.observe(key, readValue)
		result = selectIndex(result, key)
	}
	return result
}

// callGet selects one literal or dynamic map property.
func (a *analyzer) callGet(arguments []value) value {
	if len(arguments) < 2 {
		return unknownValue()
	}
	a.observe(arguments[1], readValue)
	return selectProperty(arguments[0], arguments[1])
}

// callDig follows a list of map keys and retains the fallback origin.
func (a *analyzer) callDig(arguments []value) value {
	if len(arguments) < 3 {
		return unknownValue()
	}
	result := arguments[len(arguments)-1]
	for _, key := range arguments[:len(arguments)-2] {
		a.observe(key, readValue)
		result = selectProperty(result, key)
	}
	a.observe(result, readValue)
	return union(result, arguments[len(arguments)-2])
}

// callHasKey records that the selected property affects control flow.
func (a *analyzer) callHasKey(arguments []value) value {
	if len(arguments) < 2 {
		return unknownValue()
	}
	a.observe(arguments[1], readValue)
	selected := selectProperty(arguments[0], arguments[1])
	a.observe(selected, readValue)
	return unknownValue()
}

// callPluck returns a list whose items come from one property in each map.
func (a *analyzer) callPluck(arguments []value) value {
	if len(arguments) < 2 {
		return listValue(nil)
	}
	a.observe(arguments[0], readValue)
	selected := make([]value, 0, len(arguments)-1)
	for _, input := range arguments[1:] {
		selected = append(selected, selectProperty(input, arguments[0]))
	}
	return itemListValue(union(selected...))
}

// callDict creates an abstract object from alternating key and value arguments.
func (a *analyzer) callDict(arguments []value, node parse.Node) value {
	if len(arguments)%2 != 0 {
		for _, argument := range arguments {
			a.observe(argument, openValue)
		}
		a.addDiagnostic(node, "dict with an unmatched argument consumed its complete values")
		return unknownValue()
	}
	fields := make(map[string]value, len(arguments)/2)
	for index := 0; index < len(arguments); index += 2 {
		name, ok := singleStringConstant(arguments[index])
		if !ok {
			for _, argument := range arguments {
				a.observe(argument, contextValue)
			}
			a.addDiagnostic(node, "dict with a dynamic key permits unknown direct properties in its values")
			return unknownValue()
		}
		fields[name] = arguments[index+1]
	}
	return objectValue(fields)
}

// callDefault returns both possible origins and records the selection inputs.
func (a *analyzer) callDefault(arguments []value) value {
	if len(arguments) < 2 {
		return unknownValue()
	}
	fallback := arguments[0]
	candidate := arguments[len(arguments)-1]
	a.observe(fallback, readValue)
	a.observe(candidate, readValue)
	return union(fallback, candidate)
}

// callCoalesce returns all possible selected origins.
func (a *analyzer) callCoalesce(arguments []value) value {
	for _, argument := range arguments {
		a.observe(argument, readValue)
	}
	return union(arguments...)
}

// callRequired records its message and candidate, then returns the candidate.
func (a *analyzer) callRequired(arguments []value) value {
	if len(arguments) < 2 {
		return unknownValue()
	}
	message := arguments[len(arguments)-2]
	candidate := arguments[len(arguments)-1]
	a.observe(message, openValue)
	a.observe(candidate, readValue)
	return candidate
}

// callSet overlays a fixed property. A dynamic key permits unknown direct
// keys and keeps the assigned value as a possible dynamic field.
func (a *analyzer) callSet(arguments []value, node parse.Node) value {
	if len(arguments) < 3 {
		return unknownValue()
	}
	target := arguments[0]
	key := arguments[1]
	assigned := arguments[2]
	a.observe(key, readValue)
	if name, ok := singleStringConstant(key); ok {
		return overlayValue(map[string]value{name: assigned}, target, nil)
	}
	a.observe(target, contextValue)
	a.addDiagnostic(node, "set with a dynamic key permits unknown direct keys on its target")
	dynamicField := dynamicObjectValue(assigned)
	return union(target, dynamicField)
}

// callUnset excludes a fixed property. A dynamic key permits unknown direct
// keys on the target.
func (a *analyzer) callUnset(arguments []value, node parse.Node) value {
	if len(arguments) < 2 {
		return unknownValue()
	}
	target := arguments[0]
	key := arguments[1]
	a.observe(key, readValue)
	if name, ok := singleStringConstant(key); ok {
		return overlayValue(nil, target, map[string]bool{name: true})
	}
	a.observe(target, contextValue)
	a.addDiagnostic(node, "unset with a dynamic key permits unknown direct keys on its target")
	return target
}

// callOmit excludes fixed property names while it preserves other origins.
func (a *analyzer) callOmit(arguments []value, node parse.Node) value {
	if len(arguments) == 0 {
		return objectValue(nil)
	}
	target := arguments[0]
	excluded := make(map[string]bool, len(arguments)-1)
	for _, key := range arguments[1:] {
		a.observe(key, readValue)
		name, fixed := singleStringConstant(key)
		if !fixed {
			a.observe(target, contextValue)
			a.addDiagnostic(node, "omit with a dynamic key permits unknown direct keys on its target")
			return target
		}
		excluded[name] = true
	}
	return overlayValue(nil, target, excluded)
}

// callPrint folds constants or preserves the origins of nonconstant arguments.
func (a *analyzer) callPrint(arguments []value) value {
	constants, ok := oneConstantEach(arguments)
	if ok {
		return constantValue(fmt.Sprint(constants...))
	}
	return union(arguments...)
}

// callPrintf folds a constant format call or preserves argument origins.
func (a *analyzer) callPrintf(arguments []value) value {
	if len(arguments) == 0 {
		return constantValue("")
	}
	constants, ok := oneConstantEach(arguments)
	if ok {
		format, isString := constants[0].(string)
		if isString {
			return constantValue(fmt.Sprintf(format, constants[1:]...))
		}
	}
	return union(arguments...)
}

// oneConstantEach extracts exactly one constant from every argument.
func oneConstantEach(arguments []value) ([]any, bool) {
	result := make([]any, 0, len(arguments))
	for _, argument := range arguments {
		constants, ok := constants(argument)
		if !ok || len(constants) != 1 {
			return nil, false
		}
		result = append(result, constants[0])
	}
	return result, true
}

// callInclude follows each fixed template name with the supplied context.
func (a *analyzer) callInclude(arguments []value, node parse.Node) value {
	if len(arguments) < 2 {
		a.addDiagnostic(node, "include without a name and context could not be analyzed")
		return unknownValue()
	}
	names, fixed := stringConstants(arguments[0])
	context := arguments[1]
	if !fixed {
		a.observe(arguments[0], openValue)
		a.observe(context, contextValue)
		a.addDiagnostic(node, "dynamic include name permits additional properties in its context")
		return unknownValue()
	}
	results := make([]value, 0, len(names))
	for _, name := range names {
		results = append(results, a.callNamed(name, context, node))
	}
	return union(results...)
}

// stringConstants extracts all alternatives when each one is a string.
func stringConstants(input value) ([]string, bool) {
	constants, ok := constants(input)
	if !ok || len(constants) == 0 {
		return nil, false
	}
	result := make([]string, 0, len(constants))
	for _, constant := range constants {
		text, ok := constant.(string)
		if !ok {
			return nil, false
		}
		result = append(result, text)
	}
	return result, true
}

// callTPL parses fixed text. Dynamic text opens its source and permits unknown
// properties in a specific values context, but it does not open the root.
func (a *analyzer) callTPL(arguments []value, node parse.Node) value {
	if len(arguments) < 2 {
		a.addDiagnostic(node, "tpl without text and context could not be analyzed")
		return unknownValue()
	}
	textValue := arguments[0]
	context := arguments[1]
	a.observe(textValue, openValue)
	texts, fixed := stringConstants(textValue)
	if !fixed {
		deferred := a.analyzeDeferredTPLText(textValue, context, node)
		a.observe(context, subtreeContextValue)
		a.addDiagnostic(node, "dynamic tpl text has references that static analysis cannot identify")
		return union(deferred, unknownValue())
	}
	results := make([]value, 0, len(texts))
	for _, text := range texts {
		results = append(results, a.analyzeTPLText(text, context, node))
	}
	return union(results...)
}

// analyzeDeferredTPLText analyzes chart defaults only when the value that
// contains the text reaches tpl. User overrides remain dynamic, so callTPL
// opens their specific values context when one exists.
func (a *analyzer) analyzeDeferredTPLText(textValue, context value, node parse.Node) value {
	results := make([]value, 0)
	for _, textReference := range valueReferences(textValue) {
		for _, source := range a.deferredTemplates {
			if !matchesValuePath(textReference, source.DeferredValuePath) {
				continue
			}
			key := source.Name + "\x00" + valueFingerprint(context)
			if _, finished := a.finishedTPL[key]; finished {
				continue
			}
			a.finishedTPL[key] = struct{}{}
			results = append(results, a.analyzeTPLText(string(source.Content), context, node))
			if a.err != nil {
				return unknownValue()
			}
		}
	}
	return union(results...)
}

// valueReferences returns every chart-values origin contained in an abstract
// value, including origins stored inside constructed objects and lists.
func valueReferences(input value) []reference {
	var references []reference
	for _, inputAtom := range input.atoms {
		switch inputAtom.kind {
		case referenceAtom:
			references = append(references, inputAtom.reference)
		case objectAtom:
			for _, field := range inputAtom.fields {
				references = append(references, valueReferences(field)...)
			}
			if inputAtom.fallback != nil {
				references = append(references, valueReferences(*inputAtom.fallback)...)
			}
			if inputAtom.dynamic != nil {
				references = append(references, valueReferences(*inputAtom.dynamic)...)
			}
		case listAtom:
			for _, element := range inputAtom.elements {
				references = append(references, valueReferences(element)...)
			}
			if inputAtom.item != nil {
				references = append(references, valueReferences(*inputAtom.item)...)
			}
		}
	}
	return references
}

// matchesValuePath reports whether an abstract reference can contain one
// concrete default. Dynamic collection segments match any concrete map key or
// list item at the same level. A reference to a complete parent object also
// matches template text stored below that object.
func matchesValuePath(valueReference reference, valuePath []ValuePathStep) bool {
	if len(valueReference.segments) > len(valuePath) {
		return false
	}
	for index, part := range valueReference.segments {
		step := valuePath[index]
		switch part.kind {
		case propertySegment:
			if step.CollectionItem || part.name != step.Property {
				return false
			}
		case itemSegment:
			if !step.CollectionItem {
				return false
			}
		case additionalSegment, elementSegment:
			// A dynamic selection can identify either a map property or a list
			// item, so every concrete default at this level is a candidate.
		default:
			return false
		}
	}
	return true
}

// analyzeTPLText parses fixed template text and evaluates its entry tree.
func (a *analyzer) analyzeTPLText(text string, context value, node parse.Node) value {
	name := "tpl"
	if a.currentTree != nil {
		name = fmt.Sprintf("%s:tpl:%d", a.currentTree.ParseName, node.Position())
	}
	parsed, err := parseTemplate(name, []byte(text))
	if err != nil {
		a.err = fmt.Errorf("parse fixed tpl text at %s: %w", name, err)
		return unknownValue()
	}
	definitions := maps.Clone(a.trees)
	for definitionName, tree := range parsed {
		if old := definitions[definitionName]; old != nil && parse.IsEmptyTree(tree.Root) {
			continue
		}
		definitions[definitionName] = tree
	}
	oldDefinitions := a.trees
	a.trees = definitions
	result := a.executeTree(parsed[name], context, false, true)
	a.trees = oldDefinitions
	return result
}
