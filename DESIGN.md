# Template-aware Helm schema generator

Status: Implemented foundation for the first version. The known precision limits still apply.

## Purpose

`helm-schema` generates `values.schema.json` for a Helm chart.

The generator uses chart templates as the source of value usage. It reads defaults, types, descriptions, and deferred `tpl` text from `values.yaml`.

The generator does not treat each key in `values.yaml` as a configurable value. A value becomes configurable only when a template or Helm uses it.

## Goals

The first version has these goals:

- Provide one command with no configuration file or annotations.
- Find value use through Helm templates and named templates.
- Include values that templates use, even when `values.yaml` does not declare them.
- Reject non-default values for declared keys that no template uses.
- Reject unknown keys unless template behavior can use their names or values.
- Support local chart dependencies and dependency aliases.
- Replace schemas in unpacked dependency charts so that the complete chart passes schema validation.
- Target Helm 4 and its Go SDK.
- Install the compiled program as a Helm 4 CLI plugin.
- Produce stable, compact JSON output that stays within Helm's chart-file limit.
- Produce a schema that works with `helm lint` for the supported chart behavior.
- Parse templates without rendering or executing them.

## Non-goals

The first version does not provide these features:

- User-defined schema rules.
- Comment annotations that change generation.
- Merging with an existing schema.
- Inference of enums, ranges, formats, or Kubernetes resource rules.
- Network access to download missing dependencies.
- Repacking dependency archives.
- Cluster access or execution of the Helm `lookup` function.
- A guarantee that static analysis can model all possible template programs exactly.
- Helm 3 compatibility or the experimental Helm chart v3 format.

## User interface

The command accepts zero or one positional argument:

```text
helm-schema [CHART]
```

`CHART` defaults to the current directory. The command writes `values.schema.json` in the chart directory.

The command has no generation flags. Standard `--help` and `--version` flags are permitted.

The command uses Go's standard `flag` package. The interface has one optional path and no subcommands, so it does not need a command framework.

After successful generation, the command replaces an existing `values.schema.json` with an atomic write.

If an old unpacked schema exceeds Helm's file-size limit, the loader uses a temporary chart copy without unpacked schemas. This lets generation replace the old file. Schemas inside dependency archives remain active because the command cannot replace them.

The command writes one note when a schema permits root names that templates do not name statically. It returns a nonzero status for generation errors.

The command does not run `helm lint`. A normal workflow has two commands:

```text
helm-schema ./charts/example
helm lint ./charts/example
```

The same binary can run as a Helm 4 plugin:

```text
helm schema ./charts/example
helm lint ./charts/example
```

### Helm 4 plugin

Helm 4 is the only compatibility target for the first version. The Go module imports `helm.sh/helm/v4` without a Helm 3 compatibility layer.

The repository contains this Helm 4 plugin contract:

```yaml
apiVersion: v1
type: cli/v1
name: schema
version: 0.1.0
runtime: subprocess
sourceURL: https://github.com/arch-anes/helm-schema
config:
  usage: schema [CHART]
  shortHelp: Generate values.schema.json from Helm template usage
  longHelp: Generate a Helm values schema from values used by chart templates.
  ignoreFlags: false
runtimeConfig:
  platformCommand:
    - os: windows
      command: '${HELM_PLUGIN_DIR}\bin\helm-schema.exe'
    - command: '${HELM_PLUGIN_DIR}/bin/helm-schema'
```

A release plugin package contains `plugin.yaml` and the native binary below `bin`. The package uses the same binary as the standalone command.

Development tests build the binary before they install the local plugin. Release archives contain the matching native binary.

The source tree does not commit compiled binaries.

Helm passes plugin arguments to the binary without a shell. The binary provides its own `--help` and `--version` behavior.

The plugin does not use Helm cluster environment variables. Schema generation remains a local chart operation.

## Core behavior

The generator classifies each value path as one of three categories:

1. Configurable and used.
2. Declared but fixed.
3. Unknown and rejected.

A configurable value has evidence from a template or Helm chart metadata. The schema permits a user to change this value.

A fixed value exists in the effective chart defaults, but no template uses it. The schema permits only its original default value.

An unknown value has no default and no usage evidence. A closed parent object rejects this value.

### Why fixed values are present

Helm validates the merged values during `helm lint`. The merged values contain all defaults from `values.yaml`.

If the schema omits an unused default, a closed object rejects the chart's own default. The unchanged chart then fails `helm lint`.

The schema uses `const` for each unused default subtree:

```json
{
  "internalDefault": {
    "const": "unchanged"
  }
}
```

This rule gives these results after Helm merges values:

- The unchanged chart passes.
- An override with the same value passes and has no effect.
- A present override with a different value fails.
- A new child in a fixed map fails.

The JSON file contains the unused key for Helm compatibility. The key is fixed and is not a configurable value.

Fixed properties stay optional because Helm validates both partial and fully merged dependency values. A `null` override can remove an unused key before validation.

The removed key then passes because `const` does not apply to an absent property. This case has no template effect because the key is unused.

### Evidence rule

The generator never marks a value as configurable only because `values.yaml` declares it.

A literal selector creates evidence for one fixed value path. A dynamic selector permits new names at the selected collection boundary. It keeps a strict entry schema when field use provides one.

A reachable template must provide the evidence. Comments, dead helpers, and unused dependency defaults do not provide evidence.

A value is also not configurable when template processing supersedes it before
it affects control flow or rendered output. For example, a library can derive a
security boolean from a user and group ID, or derive an environment variable
from a pod security setting. The schema preserves an unchanged default for Helm
compatibility but rejects a changed override of the superseded field.

If exact analysis is not possible, the analyzer records the location. It either permits a less precise known boundary or stops generation.

## Generic implementation rules

Production code does not contain chart names, known chart paths, or rules for one external chart.

Before adding general utility code, check the Go standard library and the Helm SDK. Add custom code only when those packages do not provide the required behavior.

The analyzer uses one abstract value model for fields, variables, functions, helpers, lists, maps, and dependency scopes.

Function behavior uses a small set of semantic classes. Examples include selectors, constructors, unions, complete consumers, and template calls.

A table maps Helm and Sprig functions to those semantic classes. A new function usually adds table data instead of new control flow.

The schema builder combines the usage tree and the default tree with one recursive operation. The same operation handles root and dependency scopes.

Dependency aliases and imports use path transformations from `Chart.yaml`. Production code does not know specific dependency names.

If a generic rule cannot keep an exact result, the analyzer uses a less precise abstract value. The same operation creates an internal diagnostic.

Real charts provide acceptance coverage only. Small original fixtures define the permanent behavior and prevent chart-specific code.

The chart adapter converts Helm scopes and metadata into generic entry contexts, path prefixes, and value-flow edges.

The template analyzer does not import Helm chart types.

## Processing steps

The generator uses this sequence:

1. Load the selected chart and all local dependencies.
2. Retain YAML syntax trees for comments and source locations.
3. Build the effective default values with Helm merge rules.
4. Parse all Helm templates into Go template syntax trees.
5. Find executable template entry points.
6. Follow calls to reachable named templates.
7. Record each value path that can affect template output or control flow.
8. Parse a default string as template text when that value reaches `tpl`.
9. Add value paths that Helm consumes from chart metadata.
10. Build a Draft 7 JSON Schema for each unpacked chart scope.
11. Validate all prepared schemas against Helm's complete values tree.
12. Write deterministic JSON to each `values.schema.json`.

The generator never renders a template. It does not need release values, Kubernetes capabilities, or a cluster connection.

## Chart loading

The first implementation pins `helm.sh/helm/v4` at `v4.2.4`. It uses `pkg/chart/v2/loader` with the public Helm 4 value utilities.

This loader supports `Chart.yaml` API versions v1 and v2. The implementation does not use Helm internal chart v3 packages.

Compatibility tests use the matching Helm 4 command and the supported Helm 4 plugin API.

The implementation also parses each `values.yaml` with `yaml.v3`. This second representation retains comments, YAML shapes, and source locations.

The loader accepts unpacked chart directories. It also accepts dependency archives that Helm can load from the `charts` directory.

Generation fails when a declared dependency is missing. The error tells the user to make the dependency available before generation.

The generator reads these chart inputs:

- `Chart.yaml` for chart type, dependencies, aliases, conditions, tags, and imported values.
- `values.yaml` for default values, plain descriptions, and template text passed to `tpl`.
- Files under `templates` for value usage.
- Local dependency charts for their defaults and templates.
- `.helmignore` through Helm's normal chart loader behavior.

The generator does not use rules from an existing `values.schema.json`. Successful generation replaces that file.

## Template analysis

### Parser

The analyzer uses the Go template parser. It does not use regular expressions to find `.Values` text.

The parser accepts function names without executing those functions. The syntax tree preserves source positions for diagnostics.

This parsing mode does not prove that a function exists in Helm. `helm lint` reports an undefined function after schema generation.

### Entry points and named templates

Normal template files are entry points because Helm renders their top-level content. Files whose base name starts with `_` are helper files.

Helper definitions do not create usage evidence by themselves. The analyzer follows a helper only when an entry point can call it.

This rule prevents an unused helper from adding unused values to the schema. The analyzer also prevents infinite recursion between helpers.

The analyzer follows these calls:

- The built-in `template` action with its static name.
- The Helm `include` function with a static or calculated name.
- Statically selected named templates.

The evaluator carries immutable scalar values in the same way that it carries value references.

Generic pure operations return a constant when all required inputs are constant. Common examples include `print` and `printf`.

Helm context fields are ordinary immutable inputs. Production code does not contain a helper name, chart name, or chart path.

If an `include` name resolves to one constant, the analyzer follows that definition.

The analyzer captures values written by actions inside a named template. An action-only helper can therefore return a value origin to `include`, `template`, or `tpl` callers.

Literal text makes the rendered helper result opaque. The analyzer then records each action value as complete output. It does not treat a field parsed from the rendered YAML as a field on every source value.

Only visited branches contribute literal output. Literal text in a statically unreachable branch does not reduce precision.

If the name remains unknown, the analyzer records usage from its expression. It permits unknown direct properties in the passed context.

The analyzer reproduces the definition order of the pinned Helm release. Later non-empty definitions replace earlier definitions.

Tests cover duplicate names across parents, siblings, and nested dependencies. Compatibility tests compare the result with the pinned Helm engine.

### Abstract value references

The analyzer does not calculate runtime values. It tracks where each expression gets its data.

A tracked reference can identify:

- The root template context.
- A chart-scoped `.Values` object.
- A known value path.
- A list item.
- A dynamically selected map value.
- A dictionary with known fields.
- A union of possible references.
- An unknown value.

This model preserves value origins through variables, pipelines, conditions, `with`, and `range` blocks.

The analyzer joins variable origins after each branch. It also joins the zero-iteration and repeated-iteration paths after each loop.

For example, the analyzer keeps the origin of `$image` in this template:

```gotemplate
{{- $image := .Values.image -}}
image: {{ $image.repository }}:{{ $image.tag }}
```

The result records `image.repository` and `image.tag` as used paths.

### Static selectors

Field chains record exact path segments. A key that contains a dot remains one segment when a literal selector accesses it.

The analyzer understands common selector functions:

- `index` and `get`.
- `dig`.
- `hasKey`.
- `pluck`.

The first version also defines transfer behavior for these common functions:

- `default` and `coalesce`.
- `dict`, `list`, and `tuple`.
- `deepCopy`.
- `merge` and `mergeOverwrite`.
- `set` and `unset`.
- `include` and `tpl`.
- `empty` and `required`.
- Boolean, comparison, conversion, formatting, and encoding functions.

A literal key adds an exact path. A dynamic key adds a dynamic map element at the nearest known parent.

For example, this expression permits arbitrary port names but only records `port` inside each selected entry:

```gotemplate
{{ (index .Values.ports .Values.selectedPort).port }}
```

The analyzer records `selectedPort` as used. It also records `port` for each dynamically selected entry under `ports`.

### Control flow

A value used by `if`, `with`, `range`, `and`, `or`, or a comparison can affect template behavior. The analyzer records that use.

A truth test on a map or list can depend on collection membership. When no field contract exists, the analyzer permits entries or items that can change that result.

A non-empty default map stays closed when a truth test is its only evidence. New properties cannot change its truth result.

An empty map permits new direct properties when the template does not also access specific fields. Structural field usage keeps the object closed so misspelled sibling fields fail. A map with only explicit null members is empty because Helm removes those members during value merging.

The analyzer folds literal conditions and fixed non-value fields when possible. Other branches remain syntactically reachable and contribute usage evidence.

For a ranged list, the analyzer tracks fields that the body reads from each item. For a ranged map, it tracks keys and map values separately.

A variable declaration keeps the origin of its expression. A variable assignment replaces the old origin in the applicable scope.

The analyzer distinguishes reads from writes by `set` and `unset`. A write does not make the previous user value configurable.

The analyzer applies object changes from `merge`, `mergeOverwrite`, `set`, and `unset` to named variable targets.

This rule keeps source origins when a chart changes a copied root context before it calls a library template.

If a mutation key is dynamic, the analyzer permits unknown direct keys on the target. For `set`, it also tracks the assigned value as the possible value of each dynamic key. It records an internal diagnostic for the precision loss.

### Complete value use

Some operations consume a complete value instead of a known child. These operations mark the nearest known subtree as open.

Examples include:

- `toYaml` and JSON conversion functions when their result reaches output.
- String formatting of a complete map or list.
- `values` on a map.
- A direct output action such as `{{ .Values.payload }}`.

An open map permits arbitrary direct child names because each child can affect the operation result. Complete use also opens all descendants of declared children.

JSON and YAML conversion preserve value origins until another operation consumes the result. This permits direct serialized output without prematurely opening a value that is converted only as an intermediate step.

A checksum or encoding operation records exact use of its input. It does not make unknown object fields valid. This rule prevents rollout checksums from disabling field validation for a complete configuration tree.

The `keys` and `len` functions permit unknown direct keys because membership affects their result. They do not consume the values or descendants below those keys.

### Object closure rules

An object is closed when its schema uses `additionalProperties: false`. A closed object accepts only names listed in `properties`.

An unrestricted open object uses `additionalProperties: true`. It accepts unnamed direct properties with values of any JSON shape.

A typed dynamic object uses a schema in `additionalProperties`. It accepts unnamed direct properties, but each property value must follow the entry schema.

The analyzer distinguishes complete use from permission for unknown context fields.

Complete use propagates through each declared child. New descendants can change the serialized output, encoded output, or direct output.

Static field selection does not create complete use. Dynamic entry fields and list-item fields can define a strict contract without complete use.

For example, dynamic service selection can permit new service names. Static port-field selection can still reject an unsupported `enablede` field.

A specific values subtree used as a dynamic `tpl` context permits unnamed direct properties. The complete values root stays closed. The context does not make declared properties configurable without separate evidence.

Exact use makes the selected value configurable. It keeps object and item boundaries closed unless other evidence opens them.

These rules produce different schemas for different evidence:

| Evidence | Direct unnamed properties | Declared descendants | Known nested contract |
|---|---|---|---|
| Static child selection | Rejected | Only used descendants are configurable | Closed |
| Complete value use | Permitted | Configurable | Open |
| Dynamic map selection | Permitted through an entry schema | Configurable when selected | Closed by the entry schema |
| Specific dynamic `tpl` context | Permitted | Governed by separate evidence | Closed |
| Root dynamic `tpl` context | Rejected | Governed by separate evidence | Closed |
| Checksum or other exact use | Rejected | Configurable only as the selected exact value | Closed |

The command reports root precision once for the complete chart tree. This note means that a generated root schema permits names without static references.

The note does not describe nested objects. A root can permit dynamic names while a known nested object rejects unsupported fields.

### Dictionaries and helper contexts

The analyzer models dictionaries with literal keys. This model supports common helper calls with a constructed context.

For example, this call keeps the origin of the `settings` field:

```gotemplate
{{ include "example.helper" (dict "settings" .Values.settings "root" $) }}
```

Inside the helper, `.settings.name` maps back to `settings.name` in the caller's values.

### `tpl` and dynamic behavior

The `tpl` function can parse text that user values provide. That text can contain new `.Values` references at runtime.

If the text is a fixed chart string, the analyzer parses that string as another template.

A literal or immutable chart file is fixed. A default from `values.yaml` can be replaced, but its known text still represents the unchanged chart. The analyzer parses that default only when the corresponding value reaches `tpl`. An unused template-looking default does not create usage evidence.

If the text can change, the analyzer records its source as open. A specific values subtree used as the context permits unknown direct properties at that boundary.

The complete root context does not permit arbitrary root values. For example, `tpl .Values.prometheus.prometheusSpec.externalUrl $` keeps the values root closed.

The `prometheusSpec` object also stays closed against misspelled sibling names.

If a dynamic operation has a known context, the analyzer permits unknown direct properties only at that boundary. It does not open the complete root without evidence.

If the analyzer cannot find a safe parent, generation fails. A silent omission can create a schema that rejects a valid chart value.

### Unknown functions

The analyzer includes explicit behavior for common Go, Helm, and Sprig functions. It does not execute function code.

For an unknown function, each argument can affect the result. The analyzer marks value arguments as complete uses.

This behavior favors valid Helm charts over narrow schemas. An internal diagnostic records where the schema became less precise.

## Usage model

The usage tree stores path segments, not dotted strings. Helm keys can contain dots and other punctuation.

Each usage node records these facts:

- Whether the value itself is read.
- Whether the selected value has exact use without permission for unsupported descendants.
- Whether unnamed direct properties can affect the result.
- Whether the complete subtree can affect the result.
- Which named object properties are read.
- How dynamically named map values are read.
- How list items are read.
- Which container kinds template operations require.
- Which template locations provide the evidence.

A parent can exist only to contain a used child. Such a structural parent is not independently configurable.

The analyzer merges evidence from all reachable template paths. The merge never removes evidence.

## Schema generation

### Schema version and root

The output uses JSON Schema Draft 7:

```json
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "type": "object",
  "properties": {},
  "additionalProperties": false
}
```

The root is always an object. The schema does not add `required` rules in the first version.

### Used values

A used default provides its initial JSON type. A YAML comment can provide its description.

The first version treats a non-null default type as the chart's type contract. Template operations can add other supported shapes when evidence requires them.

A configurable default string that contains a Go template expression does not prove the override type. A chart can pass that default to `tpl` or test whether the override is already a Boolean, number, or object.

This rule can reject an override that Helm happens to render with another type. Without annotations, the default is the only stable type declaration.

The generator supports these type mappings:

- A YAML string becomes a JSON string.
- A YAML Boolean becomes a JSON Boolean.
- A YAML integer becomes a JSON integer.
- A YAML decimal becomes a JSON number.
- A YAML mapping becomes a JSON object.
- A YAML sequence becomes a JSON array.

A null default does not prove a useful type. Helm lint checks raw values before coalescing and effective values after coalescing.

An otherwise fixed object with null children uses closed property rules instead of one object-level `const`. This accepts both Helm value forms while keeping non-null children fixed.

If template evidence requires a container, the schema permits both null and each supported container shape.

A used path can be absent from `values.yaml`. The schema includes that path without a default or an assumed leaf type.

A template selector can still prove a missing parent's object type. A list operation can prove an array or object container type.

### Used objects

An object with only static child usage is closed. It contains schemas for used children and fixed constants for unused defaults.

An object with complete use permits arbitrary direct children. A dynamically indexed object uses `additionalProperties` with an entry schema when possible.

Complete use keeps declared descendants configurable. It also permits new fields below those descendants.

Known default entries use named property schemas. These schemas keep unused fields fixed while their used fields remain configurable.

New dynamic entries use the strict `additionalProperties` schema. This schema contains only fields supported by usage evidence.

For example, a dynamic port map can produce this shape:

```json
{
  "ports": {
    "type": "object",
    "additionalProperties": {
      "type": "object",
      "properties": {
        "port": { "type": "integer" }
      },
      "additionalProperties": false
    }
  }
}
```

This schema permits new port names. It rejects unused fields in new port entries.

An existing default port can also contain fixed fields. The full generated schema represents that port as a named property.

### Used lists

Helm replaces a list when a user supplies an override. Helm does not recursively merge list entries.

A complete list use permits open item contents. A ranged list can provide a strict replacement-item contract without complete list use.

Default list entries can contain fields that the template does not use. The unchanged default must still pass Helm validation.

The schema uses two alternatives when only ranged item fields provide evidence:

1. The complete original list as a `const`.
2. A configurable list with strict item schemas.

This rule lets the original chart pass. The strict replacement list can contain only fields that template usage supports.

Literal indexes and heterogeneous item usage do not always produce one safe item schema. The analyzer uses an open item schema when a uniform rule is not sound.

A copied default list can fail if it changes a used field and retains unused fields. This result applies only to strict replacement lists.

### Fixed values

The generator uses the nearest completely unused subtree as one `const`. It does not produce a separate constant for each descendant.

The fixed constant uses the effective default after Helm applies dependency and parent merge rules.

### Descriptions and defaults

The generator copies plain YAML comments into `description` for configurable values. It ignores special annotation syntax and commented-out YAML.

The generator adds `default` only to configurable values. A structural parent does not receive an unrelated default annotation.

The `default` keyword documents a value. Helm still gets the actual default from `values.yaml`.

### Multiple shapes and invalid values

A chart can use one path with more than one shape. For example, a false default can enable an object override.

The schema uses `anyOf` when template evidence supports multiple shapes. It can also keep an incompatible default as an exact `const` alternative.

Helm template evaluation remains responsible for errors that depend on runtime control flow.

Generation fails for input that cannot have a JSON Schema representation. Examples include non-string map keys, alias cycles, and non-JSON numbers.

An invalid default error includes its JSON pointer. A template parse or analysis error includes its template name and source location when available.

## Dependencies

The generator writes a schema for the selected chart and each unpacked dependency chart. It replaces existing schemas after every schema passes generation and full-tree validation.

Helm also validates dependency values against dependency schemas. Generating only the selected chart schema is not sufficient.

The generator does not modify a packaged dependency archive. Generation stops if such an archive contains an active schema. The error tells the user to unpack the dependency.

An application dependency receives a value scope below its dependency name or alias. Nested dependencies add more scope segments.

The analyzer maps a child template's `.Values` reference back to this root path. Parent overrides use the same effective scope.

Dependency conditions and tags are real uses because Helm reads them. The analyzer adds those metadata paths to the usage tree.

The analyzer examines a dependency even when its condition is false by default. A user can enable that dependency with an override.

The chart adapter emits directed value-flow edges for Helm metadata copies. An edge identifies one source path and one destination path.

Helm `import-values` and global propagation use the same edge type.

Usage evidence propagates between both copy paths. Both schemas need compatible rules because the source value can appear at the destination during validation.

Named templates remain globally visible, as they are in Helm. The passed helper context determines which value scope a helper reads.

For a library dependency, only helpers reached by the caller create usage. The helper context maps usage back to the caller's values.

Helm copies root `global` values into dependency scopes. A child can also receive values from its alias-local `global` path.

Alias scopes are path prefixes. The analyzer does not contain conditions for specific dependency names.

Draft 7 cannot require a child copy to equal the root value. Helm remains responsible for the copy operation.

The command rejects a library chart as the selected root. Its true value scope depends on a calling chart.

### Helm validation phases

Helm can validate the root schema before and after dependency defaults are merged. The same schema must accept both value shapes.

Helm removes explicit nulls while it merges values. The chart adapter records those raw null paths before merging. The generated schema accepts both the raw null and any non-null value supplied by dependency merging.

Dependency properties remain optional for the partial phase. Nested schemas accept partial parent overrides and fully merged dependency defaults.

Tests cover absent, partial, aliased, disabled, nested, imported, and global-bearing dependencies.

## Diagnostics

Diagnostics use this information when it is available:

- Template file.
- Line and column.
- A direct explanation.

Internal diagnostics describe conservative analysis. Errors describe invalid input or a case with no safe schema result.

The analyzer sorts diagnostics by file and location. Tests and library callers can examine these diagnostics.

## Deterministic and safe output

The JSON encoder uses compact output and one final newline. Object keys have a stable lexical order. Compact output prevents whitespace from exceeding Helm's chart-file limit.

Repeated generation from unchanged chart files produces identical bytes. Stable output prevents unrelated version-control changes.

The command writes a temporary file in the chart directory. It replaces `values.schema.json` only after generation succeeds.

If the generated bytes match the existing file, the command does not replace it.

## Internal structure

The Go module uses small packages with one responsibility:

```text
cmd/helm-schema          Argument handling and diagnostics
internal/helmchart       Helm 4 loading, scopes, defaults, and metadata flows
internal/analyze         Parse trees, abstract values, usage tree, and evaluation
internal/schema          Draft 7 construction and deterministic JSON
plugin.yaml              Helm 4 CLI plugin definition
```

The packages do not expose customization interfaces in the first version.

The Helm adapter computes physical schema targets during the initial chart load. The command does not reload the chart to find dependency scopes.

The schema builder owns shared description state and object-closure rules. The analyzer does not depend on JSON Schema policy.

The core analyzer does not depend on the command package. Tests can pass parsed chart fixtures directly to the analyzer.

## Test plan

### Unit tests

Unit tests cover these cases:

- Direct field chains.
- Variables and assignments.
- `if`, `with`, and `range` scopes.
- Literal and dynamic selectors.
- Dictionaries passed to helpers.
- Reachable and unreachable named templates.
- Action-only and opaque rendered output from named templates.
- Literal helper output in unreachable branches.
- Recursive helper calls.
- Complete value functions.
- Conversion and formatting followed by a checksum.
- An unused conversion or formatting pipeline.
- Recursive openness for complete object use.
- Open replacement items for complete list use.
- Dynamic `tpl` context.
- Exact references in default text passed to `tpl`.
- Default template text that never reaches `tpl`.
- Root properties rejected when dynamic `tpl` receives the complete root context.
- Dynamic root entry names with a strict inferred entry contract.
- Incompatible scalar examples that do not weaken an object entry contract.
- Missing defaults.
- Missing structured values set to null.
- Null defaults.
- Unused null defaults.
- Truth tests on empty, non-empty, and null-only objects.
- Truth-tested objects with known fields remain closed.
- Removal of an unused default with a null override.
- Dotted and hyphenated keys.
- Object, list, and scalar conflicts.
- Literal indexes and heterogeneous lists.
- Fixed unused subtrees.
- Calculated `include` names.
- Configurable template-expression defaults with a different scalar type.
- Duplicate template definitions.
- Nested dependency aliases and defaults.
- Invalid `values.yaml` input.
- Stable JSON output.

### End-to-end fixtures

Small charts test the generator with `helm lint`. Each chart focuses on one behavior.

The end-to-end suite proves these results:

1. The unchanged chart passes.
2. An override of a used value passes.
3. A change to an unused default fails.
4. An unknown key fails.
5. A new entry in a consumed open map passes.
6. A used path missing from `values.yaml` passes.
7. An unused helper does not add schema properties.
8. A dependency alias maps to the correct root path.
9. A partial dependency override passes both Helm validation phases.
10. An imported child value maps to its parent destination.
11. A dynamic root `tpl` call rejects an unrelated root key and does not emit a root-precision note.
12. A known nested object remains closed during dynamic root `tpl` use, so a misspelled `retentionSize` fails lint.
13. References in default text passed to `tpl` are accepted, while unused default template text provides no evidence.
14. Dynamic service and port names pass while an unsupported port field such as `enablede` fails.
15. Dynamic root image names pass without an image-specific analyzer rule, while an unsupported image field fails.
16. A key declared only in a YAML comment fails without separate usage evidence.
17. A truth test treats a root with only null defaults as empty.
18. Generation replaces existing root and unpacked dependency schemas.
19. A generation error leaves existing schemas byte-for-byte unchanged.
20. A fixed object with null-only children passes raw and coalesced Helm validation.
21. Generation replaces an existing schema that exceeds Helm's chart-file limit.

### Helm 4 plugin test

The test builds the native binary and prepares a temporary plugin package. It installs that package with a temporary Helm plugin directory.

The test runs `helm schema` against a fixture. It also examines `helm plugin list` for the `cli/v1` plugin type.

### Real-chart acceptance tests

Development acceptance uses charts with these patterns:

- A declared default that templates never use.
- A dynamically indexed map with arbitrary entry names.
- A whole object passed to `toYaml`.
- A value path that templates use but defaults omit.
- A dynamic `tpl` value beside a strict `retentionSize` field, as used by kube-prometheus-stack 88.2.0.
- Dynamic service and port maps behind a library chart, as used by OctoPrint with TrueCharts common 29.7.1.
- An application dependency with nested overrides.
- A calculated `include` name derived from immutable template context fields.
- Child values imported into a parent path.

The repository does not copy those external charts. The permanent test suite uses small original fixtures with the same language constructs.

Real-chart assertions must measure strictness, not only successful generation. Dynamic maps must accept supported new entries and reject unsupported entry fields.

Paths used by `dig` must pass when only their parent map exists in defaults.

If a real chart has an upstream schema, the acceptance test uses a temporary chart copy. Generation replaces the schema in that copy.

## Security and operational limits

The generator parses untrusted chart text but does not execute it. It does not contact a cluster or evaluate template functions.

The parser and analyzer must limit recursive helper analysis. They must also report template cycles without an unbounded loop.

Large charts can contain many shared helpers. The analyzer caches helper results by template name and abstract context.

## Known precision limits

Exact static inference is not possible for every Helm template. The analyzer keeps detailed diagnostics for tests and internal package use.

The command prints one note when a generated schema permits root names that templates do not name statically.

A dynamic `tpl` call with the root context does not permit unknown root keys. This rule keeps the root schema useful for typo detection.

A specific values subtree passed as the `tpl` context permits unknown direct properties in that subtree. Known child objects follow their separate usage evidence.

An unresolved dynamic `include` permits unknown direct properties in its passed context. Known nested properties follow separate usage evidence.

A null override can remove an optional fixed default before schema validation. The absent unused value passes and cannot affect template output.

The generator replaces existing schemas in unpacked charts. Rules that exist only in those schemas are not present in the generated result.

A schema inside a dependency archive remains active. The command stops before writing files when it cannot replace that schema.

## Acceptance criteria for the first implementation

The first implementation is complete when all these statements are true for the documented supported behavior:

- One command generates or replaces schemas for a supported application chart and its unpacked dependencies.
- The generated schema passes `helm lint` with unchanged defaults.
- Used values are configurable.
- Present unused defaults are fixed with `const`.
- Unknown properties fail outside proven open subtrees.
- Static helper and variable paths remain precise.
- Dynamic operations permit unknown properties only at the smallest proven context and record internal diagnostics.
- Local application and library dependencies use the correct value scopes.
- Repeated generation produces identical output.
- The standalone binary installs and runs as a Helm 4 CLI plugin.
- Unit, fixture, and real-chart acceptance tests pass.

## Implementation order

The implementation used this order:

1. Create the module, standalone command, and Helm 4 plugin definition.
2. Load one Helm chart and retain default YAML nodes.
3. Parse direct executable templates and generate a strict root schema.
4. Add abstract variables, scopes, and static helpers.
5. Add generic function transfers and conservative fallback.
6. Add dependency scopes and value-flow edges.
7. Add plugin, Helm lint, dependency, and real-chart tests.
8. Document supported constructs and known limits.
