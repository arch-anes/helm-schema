# Formal feature matrix

This file records the production behavior that the Go-to-Lean suite compares. It also records the limits of each comparison.

The Go template parser remains trusted. The function registry also remains trusted for the meaning of each assigned class.

## Analyzer fixtures

The suite compares 11 concrete templates with the Lean analyzer.

| Production behavior | Concrete template form | Formal operation | Compared result |
|---|---|---|---|
| Scalar truth test | `if .Values.feature.enabled` | `read` | A read at the scalar path. |
| Complete root consumer | `toYaml .Values` in output | `complete` | Read and open facts at the root. |
| Fixed property selection | `index .Values.settings "name"` in output | `complete` at the fixed path | Use at `settings.name`. |
| Unused fixed selection | Assign a literal `index` result without consuming it | `selectFixed` | No usage node. |
| Unused unbounded selection | Assign `get` with a values-derived key without consuming it | `read` and `selectDynamic` | Only the key input is read. |
| Finite calculated selection | `get` with a `ternary` of two constant names | `selectFinite` and two `complete` operations | Both fixed properties are used. |
| Direct-key consumer | `keys .Values.settings` | `allowUnknown` | Unknown direct keys are relevant at `settings`. |
| Unbounded property selection | `get .Values.services .Values.selected` | `read`, `selectDynamic`, and `complete` | The key is read and the selected entry is open. |
| Exact consumer | `toJson` followed by `sha256sum` | `exact` | Exact use does not open descendants. |
| Collection iteration | `range .Values.items` and `.name` | `iterate` and `complete` | Membership and the selected element field are used. |
| Unknown function | An unregistered function consumes `.Values.payload` | `unsupported` with `unknownFunction` | The affected value uses a named conservative result. |

Theorems cover `sequence` and `branch` composition for every formal operation. The protocol uses a flat operation list because Go returns merged usage.

Go does not export its internal evidence reasons. Thus, the suite compares exported usage nodes and flags, but not internal reason values.

## Production function registry

The production registry contains all 238 functions in the pinned function surface. This surface combines Helm 4.2.4, Sprig 3.3.0, and Go template functions.

[`function_contracts_test.go`](../internal/analyze/function_contracts_test.go) stores the pinned name list separately from the production classes. The test rejects missing, extra, or duplicate class entries.

[`function_contracts.go`](../internal/analyze/function_contracts.go) assigns exactly one class to each name. Protocol version 3 sends every row to Lean.

| Production class | Lean lowering | Meaning |
|---|---|---|
| `semantic-transfer` | Deferred | Go applies an argument-sensitive transfer rule. |
| `origin-preserving` | Deferred | A later consumer determines how much of the source value is used. |
| `exact` | `exact` | The function consumes the exact selected value. |
| `allow-unknown` | `allowUnknown` | Direct key membership can affect the result. |
| `complete` | `complete` | Descendant values can affect the result. |
| `read` | `read` | The selected value can affect the result, but descendants do not. |
| `none` | No operation | The function does not consume a chart-value argument. |
| `conservative-complete` | `unsupported`, `open`, `externalOperation` | The reviewed function uses a named conservative rule. |

`call` is the only reviewed conservative function in the pinned surface. A new unregistered function still receives the separate `unknownFunction` fallback.

Lean defines all eight class lowerings. The conformance executable compares each Go row with the corresponding Lean lowering.

This comparison proves the class-to-operation mapping in the formal model. It does not prove that each Helm or Sprig implementation belongs in its assigned class.

## Usage normalization

The protocol sends the complete recursive Go usage tree. Lean does these operations:

- Preserves present empty property, additional-property, item, and element nodes.
- Converts flags into normalized observations.
- Compares nodes and observations as finite sets.
- Rejects duplicate named children at the protocol boundary.

Theorems give exact observation and node results for `TemplateIR`. They also prove that each analyzer observation occurs at a present node.

## Dependency value flow

Six cases compare `ApplyValueFlows` with the executable Lean model:

- An imported dependency value propagates back to its source.
- A global value propagates to a dependency.
- Two distinct edges propagate evidence transitively.
- A cycle terminates because one journey cannot reuse an edge.
- Property remapping retains additional, item, and element suffixes.
- Read, exact, open, key, and iteration modes propagate independently.

The formal relation permits forward and backward movement through each copy edge. Its fuel equals the number of flow edges.

A journey can use each edge identity at most once. Thus, transitive copies terminate when the metadata contains a cycle.

Lean proves that prefix remapping retains the complete suffix. It also proves forward, backward, and two-edge journeys.

Lean proves that the bounded search returns exactly the paths permitted by the journey relation. This result applies to each fuel and used-edge input.

The executable pass records every permitted observation. It retains all original observations and does not create evidence without an original source.

The pass retains each source mode. An open source also records the direct read that the usage model requires.

The conformance cases use the production flow implementation. Thus, they compare actual dependency propagation with the Lean result.

## Object-boundary decisions

The suite compares 1,547 boundary cases:

- Eleven named cases explain the main decisions, including typed nil values.
- The generated matrix covers all combinations of nine usage facts.
- Each combination uses empty, null-only, and non-null defaults.

The nine facts are read, exact, context, open, iteration, named properties, additional properties, items, and shape-neutral elements.

The protocol sends canonical default values. Lean determines whether every direct value is null.

`allowsUnnamed_iff_relevant` connects the Boolean decision to an independent raw relevance relation.

## Structural schema comparison

The suite compares 260 Go and Lean schemas at the compiled `CoreInput` boundary.

The cases cover these forms:

- Fixed scalar, object, and array constants.
- Used Boolean, integer, number, and string defaults.
- Integral floats and decimal or exponent number tokens.
- Missing and explicit-null values.
- Template-containing string defaults.
- Recursive closed objects.
- Nested null paths and nullable objects.
- Root and nested unknown-property decisions.
- Go aliases, pointers, typed nil maps, and canonical JSON conversion.
- Used arrays with strict replacement-item contracts.
- Scalar and object shape alternatives.
- Structured dynamic-entry contracts.

The generated scalar matrix combines ten default forms, six usage forms, root-open state, and explicit-null state.

The three shape cases supply compiled formal inputs. Lean does not yet derive these inputs from raw defaults and usage.

Named theorems state the direct contracts for arrays, alternatives, conjunctions, and structured dynamic entries. These theorems connect each contract to generated validation.

## Helm validator comparison

Forty-three cases compare the Lean validator directly with Helm 4. They cover these rules:

- Mathematical numeric constant equality, including exponent and negative-zero forms.
- Mathematical integer validation.
- Order-independent object constants.
- Closed nested objects and wrong scalar types.
- Nullable object type unions.
- Sibling JSON Schema constraints in `allOf`.
- Arrays without an item restriction.
- Generated structured dynamic entries.
- Generated strict replacement arrays.
- Generated scalar and object shape alternatives.
- Generated missing nullable objects.
- Generated iteration over an object or an array.

The semantic schema parser rejects unsupported validation keywords. It does not convert unsupported syntax into an unrestricted schema.

## Protocol and proof checks

Protocol version 3 includes analyzer cases, value flows, function rows, boundary cases, schemas, and validator cases.

The parser rejects unknown versions, incomplete usage nodes, duplicate names, unknown schema forms, and unknown fallback reasons.

`make verify` does these operations:

- Rejects `sorry`, `admit`, and project `axiom` declarations.
- Builds all Lean modules with warnings as errors.
- Audits every formal declaration with `--trust=0`.
- Runs the executable Lean tests.
- Runs the Go-to-Lean and Helm-to-Lean conformance suite.

The axiom audit permits only Lean's `propext` and `Quot.sound` axioms.

## Version sources

| Component | Version | Source |
|---|---|---|
| Helm SDK | `v4.2.4` | `go.mod` |
| Go language | `go1.26.0` | `go.mod` |
| Sprig | `v3.3.0` | The resolved Go module graph. |
| Lean | `v4.33.1` | `formal/lean-toolchain` |
