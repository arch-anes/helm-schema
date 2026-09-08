package analyze

// This file is the production function-to-formal-operation registry. It gives
// every Helm, Go template, and Sprig function one stable behavior class. The
// evaluator remains responsible for argument positions and abstract values.

import "slices"

// functionOperationClass names the formal behavior used for one function.
type functionOperationClass string

const (
	functionSemanticTransfer     functionOperationClass = "semantic-transfer"
	functionOriginPreserving     functionOperationClass = "origin-preserving"
	functionExactConsumer        functionOperationClass = "exact"
	functionKeyConsumer          functionOperationClass = "allow-unknown"
	functionCompleteConsumer     functionOperationClass = "complete"
	functionReadConsumer         functionOperationClass = "read"
	functionHarmless             functionOperationClass = "none"
	functionConservativeComplete functionOperationClass = "conservative-complete"
)

// specialFunctionOperations lists functions with argument-sensitive transfer
// rules in callFunction. They do not lower to one unconditional observation.
var specialFunctionOperations = stringSet(
	"index", "get", "dig", "hasKey", "pluck", "dict", "list", "tuple",
	"default", "coalesce", "required", "empty", "ternary", "deepCopy",
	"mustDeepCopy", "merge", "mustMerge", "mergeOverwrite",
	"mustMergeOverwrite", "set", "unset", "omit", "first", "mustFirst",
	"last", "mustLast", "print", "println", "printf", "include", "tpl",
	"lookup",
)

// knownConservativeFunctions contains functions exposed by Helm 4.2.4 for
// which the analyzer intentionally uses its complete-consumption fallback.
// Keeping these names explicit distinguishes a reviewed conservative rule
// from a function added by a later Helm or Sprig release.
var knownConservativeFunctions = stringSet("call")

// functionOperationGroups is the complete, disjoint production registry.
// Group order has no semantic effect. The matrix test rejects duplicate names.
var functionOperationGroups = []struct {
	class     functionOperationClass
	functions map[string]struct{}
}{
	{functionSemanticTransfer, specialFunctionOperations},
	{functionOriginPreserving, originPreservingFunctions},
	{functionOriginPreserving, yamlSerializationFunctions},
	{functionExactConsumer, exactConsumerFunctions},
	{functionKeyConsumer, keyConsumerFunctions},
	{functionCompleteConsumer, wholeConsumerFunctions},
	{functionReadConsumer, readConsumerFunctions},
	{functionHarmless, harmlessFunctions},
	{functionConservativeComplete, knownConservativeFunctions},
}

// functionOperation reports the reviewed formal class for a production
// function. The Boolean is false only for a name absent from the pinned Helm
// function surface.
func functionOperation(name string) (functionOperationClass, bool) {
	for _, group := range functionOperationGroups {
		if _, exists := group.functions[name]; exists {
			return group.class, true
		}
	}
	return functionConservativeComplete, false
}

// reviewedFunctionNames returns the complete explicit registry in stable
// order. Tests compare this list with Helm's pinned function map.
func reviewedFunctionNames() []string {
	seen := make(map[string]struct{})
	for _, group := range functionOperationGroups {
		for name := range group.functions {
			seen[name] = struct{}{}
		}
	}
	result := make([]string, 0, len(seen))
	for name := range seen {
		result = append(result, name)
	}
	slices.Sort(result)
	return result
}

// FormalFunctionOperation is one checked row in the production-to-formal
// function matrix. Lowering is the path-independent operation name; custom
// transfers and origin-preserving functions defer observation to consumers.
type FormalFunctionOperation struct {
	Name     string
	Class    string
	Lowering string
}

// FormalFunctionOperations returns every reviewed row in stable name order.
func FormalFunctionOperations() []FormalFunctionOperation {
	names := reviewedFunctionNames()
	result := make([]FormalFunctionOperation, 0, len(names))
	for _, name := range names {
		class, reviewed := functionOperation(name)
		if !reviewed {
			continue
		}
		lowering := "deferred"
		switch class {
		case functionExactConsumer:
			lowering = "exact"
		case functionKeyConsumer:
			lowering = "allowUnknown"
		case functionCompleteConsumer:
			lowering = "complete"
		case functionReadConsumer:
			lowering = "read"
		case functionConservativeComplete:
			lowering = "unsupported:open:externalOperation"
		}
		result = append(result, FormalFunctionOperation{
			Name: name, Class: string(class), Lowering: lowering,
		})
	}
	return result
}
