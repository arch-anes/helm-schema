# helm-schema

`helm-schema` generates `values.schema.json` from values that Helm templates use.

It reads `values.yaml` for defaults, types, descriptions, and default text passed to `tpl`. A declaration alone does not make a value configurable.

This project targets Helm 4 only. The current Go module uses Helm 4.2.4.

## Current behavior

The generator:

- Parses templates without rendering them.
- Follows reachable named templates and common Helm and Sprig functions.
- Tracks values through variables, pipelines, conditions, maps, and lists.
- Separates collection membership from fields used inside each element.
- Resolves literal selectors, calculated string keys, and helper names built from immutable chart fields.
- Tracks object changes from `merge`, `mergeOverwrite`, `set`, and `unset` through copied template contexts.
- Supports local dependencies, aliases, `.Subcharts`, conditions, tags, imports, and global values.
- Generates schemas for the selected chart and each unpacked dependency chart.
- Keeps unused defaults valid with exact `const` rules.
- Rejects unknown properties unless template behavior can use their names or values.
- Analyzes template expressions in defaults only when that value reaches `tpl`.
- Keeps inferred fields strict inside dynamic maps that templates inspect by field.
- Treats rollout checksums as exact use instead of permission for unknown fields.
- Ignores commented-out keys because comments do not prove runtime use.
- Writes stable, compact Draft 7 JSON to stay within Helm's chart-file limit.
- Replaces existing schemas in the selected chart and its unpacked dependencies after successful generation.
- Replaces an oversized unpacked schema even when Helm refuses to load that old file.

The command stays quiet for local precision limits.

If a generated schema permits root names that templates do not name statically, the command writes one note.

Argument parsing uses Go's standard `flag` package. This command has no subcommands or generation options, so a larger command framework is not needed.

## Open and closed objects

The terms *open* and *closed* describe which property names an object schema permits.

| Schema rule | Permitted property names | Permitted property values |
|---|---|---|
| `additionalProperties: false` | Only names in `properties` | Each named property follows its schema. |
| `additionalProperties: true` | Names in `properties` and all other names | An unnamed property can contain any JSON value. |
| `additionalProperties: { ... }` | Names in `properties` and all other names | Each unnamed property follows the given entry schema. |

A closed object uses `additionalProperties: false`. It rejects a misspelled or unsupported child name.

An open object uses one of the other two rules. The entry schema can still be closed.

Complete use, such as direct YAML output, makes all declared descendants configurable. It also permits new descendants because they affect the output.

A dynamic field selection is narrower than complete use. It can permit arbitrary service names while each service entry rejects an unsupported `enablede` field.

A dynamic map uses an entry schema when analysis can infer one. The map then permits arbitrary entry names but keeps every entry closed.

Dynamic `tpl` context has a narrower rule. It permits new direct context properties. Known properties follow their own usage evidence.

A truth test permits new direct properties in an empty object. It does not make their descendants configurable. Helm removes null members, so a null-only object is empty.

A checksum is exact use, not open use. A checksum makes the selected value configurable but does not permit unsupported descendants.

The same distinction applies to `keys` and `len`. These functions can depend on direct property names. They do not use the values below those names.

The root precision note means that at least one schema permits a root name without a static template reference. It does not mean that all nested objects are open.

## Build

Install Go 1.26 or later. Install Helm 4 to run the integration tests or use the Helm plugin.

```sh
make build
```

The binary is written to `bin/helm-schema`.

## Use the command

```sh
bin/helm-schema ./path/to/chart
helm lint ./path/to/chart
```

The chart path defaults to the current directory:

```sh
cd ./path/to/chart
/path/to/helm-schema
```

Generation uses only local chart files. It does not download dependencies or contact a Kubernetes cluster.

## Use the Helm 4 plugin

Prepare and install a local development plugin:

```sh
make plugin-dir
helm plugin install ./.dist/schema
helm schema ./path/to/chart
```

Installing directly from the Git repository also works when Go is installed:

```sh
helm plugin install https://github.com/arch-anes/helm-schema.git --verify=false
```

The install hook builds the native executable in the plugin directory. A
release package is preferred for users who do not have Go installed.

Create an unsigned package for local testing:

```sh
make plugin-package
```

Release packages must contain a native binary for their target platform.

## Development

Run all unit, plugin, and Helm lint tests:

```sh
make test
```

The [design document](DESIGN.md) defines the intended behavior and known limits.

Dynamic `tpl` text can refer to an unknown direct property of its context. The generator permits those direct properties but keeps known nested objects closed. It also analyzes the chart's default template text when the corresponding value reaches `tpl`.

An override can make dynamic `tpl` text refer to a new property inside a known nested object. Static analysis cannot identify that property. The generated schema rejects it unless another chart template or default template expression provides evidence for it.

The generator does not merge rules from existing schemas. A successful run replaces schemas in the selected chart and its unpacked dependencies.

Commented-out YAML can document a possible value, but it does not prove that Helm or a template reads that value. The schema rejects it without other evidence.

## Code map

Each production file has one primary responsibility:

| File | Responsibility |
|---|---|
| `cmd/helm-schema/main.go` | Parses arguments, prepares all schemas, validates the chart tree, and replaces schema files. |
| `internal/helmchart/load.go` | Loads Helm 4 charts, dependencies, defaults, scopes, and metadata value flows. |
| `internal/helmchart/descriptions.go` | Reads descriptions from comments in root and dependency `values.yaml` files. |
| `internal/helmchart/templates.go` | Converts chart templates, contexts, and deferred `tpl` text into analyzer inputs. |
| `internal/helmchart/validation.go` | Validates generated root and dependency schemas with Helm value processing. |
| `internal/analyze/types.go` | Defines analyzer inputs, diagnostics, value flows, and the usage tree. |
| `internal/analyze/analyze.go` | Parses template files, creates entry contexts, and starts analysis. |
| `internal/analyze/eval.go` | Evaluates control flow, variables, pipelines, and named-template output. |
| `internal/analyze/functions.go` | Defines generic behavior for Helm, Go template, and Sprig functions. |
| `internal/analyze/value.go` | Defines abstract values and field, item, and collection selection. |
| `internal/analyze/usage.go` | Converts abstract value observations into usage-tree evidence. |
| `internal/analyze/flow.go` | Maps usage through imported and global dependency values. |
| `internal/schema/schema.go` | Combines defaults and usage evidence into a Draft 7 schema with inferred property rules. |
| `plugin.yaml` | Defines the Helm 4 `cli/v1` plugin. |

## Test data

The `testdata` directory contains small charts created for this project. Each chart isolates behavior that the tests assert.

Full third-party charts are acceptance inputs, not permanent fixtures. This keeps tests stable and prevents large licensed copies in the repository.

Acceptance runs use temporary chart copies because generation replaces `values.schema.json`.
