// Command helm-schema generates values.schema.json files from values that
// Helm charts use.
package main

// This file defines argument parsing, tree-wide generation, concise output,
// and atomic replacement of each schema file.

import (
	"bytes"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"

	"github.com/arch-anes/helm-schema/internal/analyze"
	"github.com/arch-anes/helm-schema/internal/helmchart"
	"github.com/arch-anes/helm-schema/internal/schema"
	chartarchive "helm.sh/helm/v4/pkg/chart/loader/archive"
	chartv2loader "helm.sh/helm/v4/pkg/chart/v2/loader"
)

// version contains the build version printed by the --version flag.
var version = "dev"

// main prints a command error and exits with a nonzero process status.
func main() {
	if err := run(os.Args[1:], os.Stdout, os.Stderr); err != nil {
		fmt.Fprintf(os.Stderr, "helm-schema: %v\n", err)
		os.Exit(1)
	}
}

// run parses the command arguments, prepares and validates every schema, then
// writes the results. Writer arguments let tests capture output safely.
func run(args []string, stdout, stderr io.Writer) error {
	return runWithInput(args, os.Stdin, stdout, stderr)
}

// runWithInput selects generation or schema validation. The separate input
// parameter keeps command tests independent from process standard input.
func runWithInput(args []string, input io.Reader, stdout, stderr io.Writer) error {
	if len(args) > 0 && args[0] == "validate" {
		return validate(args[1:], input, stdout)
	}

	chartPath, done, err := parseArguments(args, stdout)
	if err != nil {
		return err
	}
	if done {
		return nil
	}

	chart, err := helmchart.Load(chartPath)
	if err != nil {
		return fmt.Errorf("load chart: %w", err)
	}
	usage, _, err := analyze.Templates(chart.Templates)
	if err != nil {
		return fmt.Errorf("analyze templates: %w", err)
	}
	usage.Merge(chart.MetadataUsage)
	if err := analyze.ApplyValueFlows(usage, chart.ValueFlows); err != nil {
		return fmt.Errorf("analyze Helm value flows: %w", err)
	}
	generated := make([]generatedSchema, 0, len(chart.Scopes))
	for _, scope := range chart.Scopes {
		result, err := generate(chart, usage, scope)
		if err != nil {
			return err
		}
		generated = append(generated, result)
	}
	schemas := make(map[string][]byte, len(generated))
	for _, result := range generated {
		schemas[filepath.Dir(result.path)] = result.content
	}
	if err := helmchart.ValidateTree(chartPath, schemas); err != nil {
		return fmt.Errorf("generated schemas reject chart tree: %w", err)
	}

	allowsUnknownRoot := false
	changed := 0
	for _, result := range generated {
		allowsUnknownRoot = allowsUnknownRoot || result.allowsUnknownRoot
		replaced, err := replaceFile(result.path, result.content)
		if err != nil {
			return fmt.Errorf("write schema %q: %w", result.path, err)
		}
		if replaced {
			changed++
		}
	}
	writePrecisionNote(stderr, allowsUnknownRoot)
	writeSummary(stdout, generated, changed)
	return nil
}

// validate reads YAML values and validates them with Helm's own schema
// validator. It never renders templates, so deployment-time cluster
// capabilities cannot affect schema validation.
func validate(args []string, input io.Reader, stdout io.Writer) error {
	chartPath, done, err := parseValidationArguments(args, stdout)
	if err != nil || done {
		return err
	}
	values, err := chartv2loader.LoadValues(input)
	if err != nil {
		return fmt.Errorf("parse values YAML: %w", err)
	}
	if err := helmchart.ValidateValues(chartPath, values); err != nil {
		return err
	}
	fmt.Fprintln(stdout, "values match chart schemas")
	return nil
}

// generatedSchema is one prepared file and its root-precision result.
type generatedSchema struct {
	path              string
	content           []byte
	allowsUnknownRoot bool
}

// generate builds one physical chart schema from all values scopes that use
// that directory. It returns bytes without changing the file system.
func generate(chart *helmchart.Data, usage *analyze.Usage, scope helmchart.ChartScope) (generatedSchema, error) {
	schemas := make([][]byte, 0, len(scope.ValuesPrefixes))
	allowsUnknownRoot := false
	for _, valuesPrefix := range scope.ValuesPrefixes {
		scopeData, err := chart.ForScope(valuesPrefix)
		if err != nil {
			return generatedSchema{}, fmt.Errorf("select values for %q: %w", scope.Directory, err)
		}
		scopeUsage := usage.AtPath(valuesPrefix...)
		schemaJSON, err := schema.Generate(
			scopeData.Defaults,
			scopeData.Descriptions,
			scopeUsage,
			scopeData.ExplicitNullDefaults...,
		)
		if err != nil {
			return generatedSchema{}, fmt.Errorf("generate schema for %q: %w", scope.Directory, err)
		}
		if err := helmchart.Validate(scopeData.Defaults, schemaJSON); err != nil {
			return generatedSchema{}, fmt.Errorf("generated schema rejects defaults for %q: %w", scope.Directory, err)
		}
		schemas = append(schemas, schemaJSON)
		allowsUnknownRoot = allowsUnknownRoot || schema.AllowsUnknownRootProperties(scopeData.Defaults, scopeUsage)
	}
	combined, err := schema.Combine(schemas...)
	if err != nil {
		return generatedSchema{}, fmt.Errorf("combine schemas for %q: %w", scope.Directory, err)
	}
	if err := checkGeneratedSchemaSize(scope.Directory, combined); err != nil {
		return generatedSchema{}, err
	}

	return generatedSchema{
		path:              filepath.Join(scope.Directory, "values.schema.json"),
		content:           combined,
		allowsUnknownRoot: allowsUnknownRoot,
	}, nil
}

// checkGeneratedSchemaSize rejects output that Helm's chart loader cannot
// read. It checks bytes after alias schemas have been combined.
func checkGeneratedSchemaSize(directory string, content []byte) error {
	if int64(len(content)) <= chartarchive.MaxDecompressedFileSize {
		return nil
	}
	return fmt.Errorf(
		"generated schema for %q is %d bytes; Helm's chart-file limit is %d bytes",
		directory,
		len(content),
		chartarchive.MaxDecompressedFileSize,
	)
}

// parseArguments uses the standard flag package for help, version, and the
// optional chart path. The done result reports help or version output.
func parseArguments(args []string, stdout io.Writer) (chartPath string, done bool, err error) {
	flags := flag.NewFlagSet("helm-schema", flag.ContinueOnError)
	flags.SetOutput(io.Discard)
	showVersion := flags.Bool("version", false, "show the helm-schema version")
	flags.Usage = func() { writeHelp(stdout) }

	if err := flags.Parse(args); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return "", true, nil
		}
		return "", false, err
	}
	if *showVersion {
		fmt.Fprintf(stdout, "helm-schema %s\n", version)
		return "", true, nil
	}
	if flags.NArg() > 1 {
		return "", false, errors.New("usage: helm-schema [CHART]")
	}
	if flags.NArg() == 1 {
		return flags.Arg(0), false, nil
	}
	return ".", false, nil
}

// parseValidationArguments accepts the optional chart path for the validation
// command. Values always arrive as one YAML document on standard input.
func parseValidationArguments(args []string, stdout io.Writer) (chartPath string, done bool, err error) {
	flags := flag.NewFlagSet("helm-schema validate", flag.ContinueOnError)
	flags.SetOutput(io.Discard)
	flags.Usage = func() { writeValidationHelp(stdout) }

	if err := flags.Parse(args); err != nil {
		if errors.Is(err, flag.ErrHelp) {
			return "", true, nil
		}
		return "", false, err
	}
	if flags.NArg() > 1 {
		return "", false, errors.New("usage: helm-schema validate [CHART]")
	}
	if flags.NArg() == 1 {
		return flags.Arg(0), false, nil
	}
	return ".", false, nil
}

// writePrecisionNote reports one material loss of schema strictness across the
// selected chart and its dependencies.
func writePrecisionNote(w io.Writer, allowsUnknownRoot bool) {
	if !allowsUnknownRoot {
		return
	}
	fmt.Fprintln(w, "note: at least one generated schema permits root properties that templates do not name statically.")
}

// writeSummary reports one result for the complete chart tree.
func writeSummary(w io.Writer, generated []generatedSchema, changed int) {
	if len(generated) == 1 {
		if changed == 1 {
			fmt.Fprintf(w, "wrote %s\n", generated[0].path)
		} else {
			fmt.Fprintf(w, "%s is unchanged\n", generated[0].path)
		}
		return
	}
	if changed == 0 {
		fmt.Fprintf(w, "%d schema files are unchanged\n", len(generated))
		return
	}
	fmt.Fprintf(w, "updated %d of %d schema files\n", changed, len(generated))
}

// writeHelp writes the standalone and Helm plugin command forms.
func writeHelp(w io.Writer) {
	fmt.Fprintln(w, "Generate values.schema.json from values used by Helm templates.")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "Usage:")
	fmt.Fprintln(w, "  helm-schema [CHART]")
	fmt.Fprintln(w, "  helm-schema validate [CHART] < values.yaml")
	fmt.Fprintln(w, "  helm schema [CHART]")
	fmt.Fprintln(w, "  helm schema validate [CHART] < values.yaml")
}

// writeValidationHelp documents the schema-only validation command.
func writeValidationHelp(w io.Writer) {
	fmt.Fprintln(w, "Validate a YAML values document against Helm chart schemas.")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "Usage:")
	fmt.Fprintln(w, "  helm-schema validate [CHART] < values.yaml")
	fmt.Fprintln(w, "  helm schema validate [CHART] < values.yaml")
}

// replaceFile writes content beside the target and renames it into place. It
// does not replace the target when its bytes already match content.
func replaceFile(path string, content []byte) (bool, error) {
	existing, err := os.ReadFile(path)
	if err == nil && bytes.Equal(existing, content) {
		return false, nil
	}
	if err != nil && !errors.Is(err, os.ErrNotExist) {
		return false, err
	}

	temporary, err := os.CreateTemp(filepath.Dir(path), ".values.schema.json-*")
	if err != nil {
		return false, err
	}
	temporaryPath := temporary.Name()
	defer os.Remove(temporaryPath)

	if err := temporary.Chmod(0o644); err != nil {
		temporary.Close()
		return false, err
	}
	if _, err := temporary.Write(content); err != nil {
		temporary.Close()
		return false, err
	}
	if err := temporary.Sync(); err != nil {
		temporary.Close()
		return false, err
	}
	if err := temporary.Close(); err != nil {
		return false, err
	}
	if err := os.Rename(temporaryPath, path); err != nil {
		return false, err
	}
	return true, nil
}
