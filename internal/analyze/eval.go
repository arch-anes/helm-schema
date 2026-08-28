package analyze

// This file evaluates Go template parse trees with abstract values. It models
// scopes, variables, pipelines, branches, and loops without rendering text.

import (
	"fmt"
	"maps"
	"slices"
	"strings"
	"text/template/parse"
)

// environment stores the current dot value and template variable bindings.
// MutableRoot permits synthetic fields on a context created by deepCopy.
type environment struct {
	dot         value
	vars        map[string]value
	mutableRoot bool
}

// newEnvironment creates the initial dot and root variable for one tree call.
func newEnvironment(root value) *environment {
	return &environment{
		dot:         root,
		vars:        map[string]value{"$": root},
		mutableRoot: root.copied,
	}
}

// clone copies variable bindings for a branch or nested control scope.
func (e *environment) clone() *environment {
	return &environment{dot: e.dot, vars: maps.Clone(e.vars), mutableRoot: e.mutableRoot}
}

// executeTree evaluates one parse tree with an abstract root. Memoize reuses a
// named-template result for the same context. Capture returns action output to
// an include or template caller instead of consuming it immediately.
func (a *analyzer) executeTree(tree *parse.Tree, root value, memoize, capture bool) value {
	if tree == nil || tree.Root == nil || a.err != nil {
		return unknownValue()
	}
	key := tree.Name + "\x00" + valueFingerprint(root)
	if memoize {
		if _, done := a.finished[key]; done {
			return a.outputs[key]
		}
		if a.activeTrees[tree.Name] > 0 {
			a.observe(root, openValue)
			a.addDiagnostic(nil, fmt.Sprintf("recursive template %q consumed its complete argument", tree.Name))
			return unknownValue()
		}
		if a.callDepth >= maximumCallDepth {
			a.observe(root, openValue)
			a.addDiagnostic(nil, fmt.Sprintf("template call depth exceeded %d; complete argument was consumed", maximumCallDepth))
			return unknownValue()
		}
		a.activeTrees[tree.Name]++
		a.callDepth++
		defer func() {
			a.callDepth--
			a.activeTrees[tree.Name]--
		}()
	}

	previousTree := a.currentTree
	a.currentTree = tree
	defer func() { a.currentTree = previousTree }()
	if capture {
		a.outputFrames = append(a.outputFrames, outputFrame{})
	}
	a.walkList(tree.Root, newEnvironment(root))
	result := unknownValue()
	if capture {
		frame := a.outputFrames[len(a.outputFrames)-1]
		a.outputFrames = a.outputFrames[:len(a.outputFrames)-1]
		if frame.opaque {
			for _, output := range frame.values {
				a.observe(output, openValue)
			}
		} else if len(frame.values) > 0 {
			result = union(frame.values...)
		}
	}
	if memoize {
		a.finished[key] = struct{}{}
		a.outputs[key] = result
	}
	return result
}

// callNamed evaluates a named template and returns the abstract values written
// by its actions. An undefined template consumes its complete argument.
func (a *analyzer) callNamed(name string, root value, node parse.Node) value {
	tree := a.trees[name]
	if tree == nil {
		a.observe(root, openValue)
		a.addDiagnostic(node, fmt.Sprintf("template %q is not defined; complete argument was consumed", name))
		return unknownValue()
	}
	return a.executeTree(tree, root, true, true)
}

// emit records a value written by an action. Named templates collect output
// for include or template callers. Entry templates write directly to the
// rendered manifest.
func (a *analyzer) emit(output value) {
	if len(a.outputFrames) == 0 {
		a.observe(output, openValue)
		return
	}
	index := len(a.outputFrames) - 1
	a.outputFrames[index].values = append(a.outputFrames[index].values, output)
}

// emitLiteral records non-whitespace text from a visited named-template
// branch. The complete rendered result is then opaque to its caller.
func (a *analyzer) emitLiteral(text []byte) {
	if len(a.outputFrames) == 0 || strings.TrimSpace(string(text)) == "" {
		return
	}
	a.outputFrames[len(a.outputFrames)-1].opaque = true
}

// walkList evaluates nodes in source order within one environment.
func (a *analyzer) walkList(list *parse.ListNode, env *environment) {
	if list == nil || a.err != nil {
		return
	}
	for _, node := range list.Nodes {
		if a.err != nil {
			return
		}
		switch typed := node.(type) {
		case *parse.ActionNode:
			result := a.evalPipe(typed.Pipe, env, true)
			if len(typed.Pipe.Decl) == 0 {
				a.emit(result)
			}
		case *parse.IfNode:
			a.walkIf(typed, env)
		case *parse.WithNode:
			a.walkWith(typed, env)
		case *parse.RangeNode:
			a.walkRange(typed, env)
		case *parse.TemplateNode:
			root := constantValue(nil)
			if typed.Pipe != nil {
				root = a.evalPipe(typed.Pipe, env, true)
			}
			a.emit(a.callNamed(typed.Name, root, typed))
		case *parse.ListNode:
			a.walkList(typed, env)
		case *parse.TextNode:
			a.emitLiteral(typed.Text)
		case *parse.CommentNode, *parse.BreakNode, *parse.ContinueNode:
			// These nodes do not read values directly.
		default:
			a.addDiagnostic(node, fmt.Sprintf("unsupported template node %T", node))
		}
	}
}

// walkIf evaluates reachable branches and joins outer variable bindings.
func (a *analyzer) walkIf(node *parse.IfNode, env *environment) {
	outerNames := variableNames(env)
	scope := env.clone()
	condition := a.evalPipe(node.Pipe, scope, true)
	a.observe(condition, readValue)

	known, truth := knownTruth(condition)
	thenEnv := scope.clone()
	elseEnv := scope.clone()
	if !known || truth {
		a.walkList(node.List, thenEnv)
	}
	if !known || !truth {
		a.walkList(node.ElseList, elseEnv)
	}
	if known && truth {
		joinEnvironment(env, outerNames, thenEnv)
	} else if known {
		joinEnvironment(env, outerNames, elseEnv)
	} else {
		joinEnvironment(env, outerNames, thenEnv, elseEnv)
	}
}

// walkWith evaluates reachable branches and sets dot for the main branch.
func (a *analyzer) walkWith(node *parse.WithNode, env *environment) {
	outerNames := variableNames(env)
	scope := env.clone()
	condition := a.evalPipe(node.Pipe, scope, true)
	a.observe(condition, readValue)

	known, truth := knownTruth(condition)
	thenEnv := scope.clone()
	thenEnv.dot = condition
	elseEnv := scope.clone()
	elseEnv.dot = env.dot
	if !known || truth {
		a.walkList(node.List, thenEnv)
	}
	if !known || !truth {
		a.walkList(node.ElseList, elseEnv)
	}
	if known && truth {
		joinEnvironment(env, outerNames, thenEnv)
	} else if known {
		joinEnvironment(env, outerNames, elseEnv)
	} else {
		joinEnvironment(env, outerNames, thenEnv, elseEnv)
	}
}

// walkRange evaluates one abstract iteration and the possible empty branch.
func (a *analyzer) walkRange(node *parse.RangeNode, env *environment) {
	outerNames := variableNames(env)
	scope := env.clone()
	collection := a.evalPipe(node.Pipe, scope, false)
	a.observe(collection, iterateValue)
	known, nonempty := knownTruth(collection)
	element := rangeItem(collection)

	bodyEnv := scope.clone()
	bodyEnv.dot = element
	if len(node.Pipe.Decl) == 1 {
		bindRangeVariable(bodyEnv, node.Pipe.Decl[0], element, node.Pipe.IsAssign)
	} else if len(node.Pipe.Decl) >= 2 {
		bindRangeVariable(bodyEnv, node.Pipe.Decl[0], rangeKey(collection), node.Pipe.IsAssign)
		bindRangeVariable(bodyEnv, node.Pipe.Decl[1], element, node.Pipe.IsAssign)
	}
	if !known || nonempty {
		a.walkList(node.List, bodyEnv)
	}

	elseEnv := scope.clone()
	elseEnv.dot = env.dot
	if !known || !nonempty {
		a.walkList(node.ElseList, elseEnv)
	}

	// An unknown range can execute zero times or repeatedly. One abstract
	// iteration plus the zero-iteration state gives a safe monotonic join.
	if known && nonempty {
		joinEnvironment(env, outerNames, bodyEnv)
	} else if known {
		joinEnvironment(env, outerNames, scope, elseEnv)
	} else {
		joinEnvironment(env, outerNames, scope, bodyEnv, elseEnv)
	}
}

// bindRangeVariable applies range declaration and assignment rules.
func bindRangeVariable(env *environment, declaration *parse.VariableNode, result value, assign bool) {
	if declaration == nil || len(declaration.Ident) == 0 {
		return
	}
	name := declaration.Ident[0]
	if assign {
		if _, exists := env.vars[name]; !exists {
			return
		}
	}
	env.vars[name] = result
}

// variableNames returns the variable names that exist before a nested scope.
func variableNames(env *environment) []string {
	return slices.Sorted(maps.Keys(env.vars))
}

// joinEnvironment unions selected outer variable bindings from control paths.
func joinEnvironment(destination *environment, names []string, sources ...*environment) {
	for _, name := range names {
		values := make([]value, 0, len(sources))
		for _, source := range sources {
			if variable, exists := source.vars[name]; exists {
				values = append(values, variable)
			}
		}
		if len(values) > 0 {
			destination.vars[name] = union(values...)
		}
	}
}

// evalPipe passes each command result to the next command. It can also bind the
// final result to declared variables.
func (a *analyzer) evalPipe(pipe *parse.PipeNode, env *environment, bind bool) value {
	if pipe == nil {
		return constantValue(nil)
	}
	var result value
	for index, command := range pipe.Cmds {
		var piped *value
		if index > 0 {
			previous := result
			piped = &previous
		}
		result = a.evalCommand(command, env, piped)
	}
	if len(pipe.Cmds) == 0 {
		result = unknownValue()
	}
	if bind {
		for _, declaration := range pipe.Decl {
			if declaration == nil || len(declaration.Ident) == 0 {
				continue
			}
			name := declaration.Ident[0]
			if pipe.IsAssign {
				if _, exists := env.vars[name]; !exists {
					continue
				}
			}
			env.vars[name] = result
		}
	}
	return result
}

// evalCommand evaluates a function call, a simple value, or a dynamic command.
func (a *analyzer) evalCommand(command *parse.CommandNode, env *environment, piped *value) value {
	if command == nil || len(command.Args) == 0 {
		return unknownValue()
	}
	if identifier, ok := command.Args[0].(*parse.IdentifierNode); ok {
		arguments := make([]value, 0, len(command.Args))
		for _, argument := range command.Args[1:] {
			arguments = append(arguments, a.evalNode(argument, env))
		}
		if piped != nil {
			arguments = append(arguments, *piped)
		}
		result := a.callFunction(identifier.Ident, arguments, command)
		if mutatesFirstArgument(identifier.Ident) && len(command.Args) > 1 {
			assignExpression(env, command.Args[1], result)
		}
		return result
	}

	if len(command.Args) == 1 && piped == nil {
		return a.evalNode(command.Args[0], env)
	}

	arguments := make([]value, 0, len(command.Args)+1)
	for _, argument := range command.Args {
		arguments = append(arguments, a.evalNode(argument, env))
	}
	if piped != nil {
		arguments = append(arguments, *piped)
	}
	hasValueOrigin := false
	for _, argument := range arguments {
		hasValueOrigin = hasValueOrigin || hasOrigins(argument)
		a.observe(argument, openValue)
	}
	if hasValueOrigin {
		a.addDiagnostic(command, fmt.Sprintf("dynamic command %q consumed its complete value arguments", command.String()))
	}
	return unknownValue()
}

// mutatesFirstArgument reports functions whose documented Helm behavior
// changes their destination object in addition to returning it.
func mutatesFirstArgument(name string) bool {
	switch name {
	case "merge", "mustMerge", "mergeOverwrite", "mustMergeOverwrite", "set", "unset":
		return true
	default:
		return false
	}
}

// assignExpression updates a named variable used as a mutation target. Values
// are immutable abstract objects, so this creates a new object along the
// selected path and leaves deep-copied source contexts unchanged.
func assignExpression(env *environment, node parse.Node, assigned value) {
	switch typed := node.(type) {
	case *parse.VariableNode:
		if len(typed.Ident) == 0 {
			return
		}
		// A set on $ can add a synthetic field to the template context. A set
		// below $.Values changes the chart's actual values object and must not
		// turn generated helper data into user-configurable values.
		if typed.Ident[0] == "$" && len(typed.Ident) > 1 && !env.mutableRoot {
			return
		}
		base, exists := env.vars[typed.Ident[0]]
		if !exists {
			return
		}
		env.vars[typed.Ident[0]] = replaceFields(base, typed.Ident[1:], assigned)
		if typed.Ident[0] == "$" {
			env.dot = env.vars[typed.Ident[0]]
		}
	case *parse.FieldNode:
		if env.mutableRoot {
			env.dot = replaceFields(env.dot, typed.Ident, assigned)
			env.vars["$"] = env.dot
		}
	case *parse.ChainNode:
		if variable, ok := typed.Node.(*parse.VariableNode); ok && len(variable.Ident) > 0 && (variable.Ident[0] != "$" || env.mutableRoot) {
			base, exists := env.vars[variable.Ident[0]]
			if !exists {
				return
			}
			path := append(slices.Clone(variable.Ident[1:]), typed.Field...)
			env.vars[variable.Ident[0]] = replaceFields(base, path, assigned)
			if variable.Ident[0] == "$" {
				env.dot = env.vars[variable.Ident[0]]
			}
		}
	}
}

// replaceFields returns input with one fixed object path replaced.
func replaceFields(input value, path []string, assigned value) value {
	if len(path) == 0 {
		return assigned
	}
	updated := make([]value, 0, len(input.atoms))
	for _, inputAtom := range input.atoms {
		if inputAtom.kind != objectAtom {
			fallback := value{atoms: []atom{inputAtom}}
			field := assigned
			if len(path) > 1 {
				field = replaceFields(objectValue(nil), path[1:], assigned)
			}
			updated = append(updated, overlayValue(map[string]value{path[0]: field}, fallback, nil))
			continue
		}
		fields := maps.Clone(inputAtom.fields)
		if fields == nil {
			fields = make(map[string]value)
		}
		current, exists := fields[path[0]]
		if !exists {
			current = objectValue(nil)
		}
		fields[path[0]] = replaceFields(current, path[1:], assigned)
		updated = append(updated, value{atoms: []atom{{
			kind:     objectAtom,
			fields:   fields,
			fallback: inputAtom.fallback,
			dynamic:  inputAtom.dynamic,
			excluded: maps.Clone(inputAtom.excluded),
		}}})
	}
	result := union(updated...)
	result.copied = result.copied || input.copied
	return result
}

// evalNode converts one expression node into an abstract value.
func (a *analyzer) evalNode(node parse.Node, env *environment) value {
	if node == nil {
		return unknownValue()
	}
	switch typed := node.(type) {
	case *parse.DotNode:
		return env.dot
	case *parse.FieldNode:
		result := env.dot
		for _, field := range typed.Ident {
			result = selectField(result, field)
		}
		return result
	case *parse.VariableNode:
		if len(typed.Ident) == 0 {
			return unknownValue()
		}
		result, exists := env.vars[typed.Ident[0]]
		if !exists {
			return unknownValue()
		}
		for _, field := range typed.Ident[1:] {
			result = selectField(result, field)
		}
		return result
	case *parse.ChainNode:
		result := a.evalNode(typed.Node, env)
		for _, field := range typed.Field {
			result = selectField(result, field)
		}
		return result
	case *parse.PipeNode:
		return a.evalPipe(typed, env, true)
	case *parse.StringNode:
		return constantValue(typed.Text)
	case *parse.BoolNode:
		return constantValue(typed.True)
	case *parse.NumberNode:
		if typed.IsInt {
			return constantValue(typed.Int64)
		}
		if typed.IsUint {
			return constantValue(typed.Uint64)
		}
		if typed.IsFloat {
			return constantValue(typed.Float64)
		}
		return unknownValue()
	case *parse.NilNode:
		return constantValue(nil)
	case *parse.IdentifierNode:
		// An identifier in argument position invokes a niladic template
		// function. Helm charts commonly use this form with dict and list.
		return a.callFunction(typed.Ident, nil, typed)
	default:
		a.addDiagnostic(node, fmt.Sprintf("unsupported expression node %T", node))
		return unknownValue()
	}
}

// knownTruth evaluates truth for one fixed scalar, object, or list value.
func knownTruth(input value) (known bool, truth bool) {
	if len(input.atoms) != 1 {
		return false, false
	}
	inputAtom := input.atoms[0]
	switch inputAtom.kind {
	case constantAtom:
		switch typed := inputAtom.constant.(type) {
		case nil:
			return true, false
		case bool:
			return true, typed
		case string:
			return true, typed != ""
		case int:
			return true, typed != 0
		case int64:
			return true, typed != 0
		case uint64:
			return true, typed != 0
		case float64:
			return true, typed != 0
		default:
			return false, false
		}
	case objectAtom:
		if inputAtom.fallback != nil || inputAtom.dynamic != nil {
			return false, false
		}
		return true, len(inputAtom.fields) > 0
	case listAtom:
		if inputAtom.item != nil {
			return false, false
		}
		return true, len(inputAtom.elements) > 0
	default:
		return false, false
	}
}
