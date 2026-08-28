package helmchart

// This file reads plain descriptions from values.yaml comments. It maps child
// chart comments into their dependency paths.

import (
	"bytes"
	"fmt"
	"io"
	"strconv"
	"strings"

	"gopkg.in/yaml.v3"
	chartv2 "helm.sh/helm/v4/pkg/chart/v2"
)

// loadDescriptions collects descriptions from the root chart and dependencies.
func loadDescriptions(ch *chartv2.Chart) (map[string]string, error) {
	descriptions := make(map[string]string)
	if err := appendChartDescriptions(ch, nil, descriptions); err != nil {
		return nil, err
	}
	return descriptions, nil
}

// appendChartDescriptions visits dependencies first. Parent comments can then
// replace child comments at the same effective values path.
func appendChartDescriptions(ch *chartv2.Chart, valuesPrefix []string, descriptions map[string]string) error {
	dependencies, err := bindDependencies(ch)
	if err != nil {
		return err
	}
	for _, dependency := range dependencies {
		childPrefix := appendValuePath(valuesPrefix, dependency.name)
		if err := appendChartDescriptions(dependency.chart, childPrefix, descriptions); err != nil {
			return err
		}
	}

	// Parent comments replace dependency comments because the parent owns the
	// final values path and can document its override more precisely.
	for _, file := range ch.Raw {
		if file == nil || file.Name != "values.yaml" {
			continue
		}
		if err := decodeDescriptions(file.Data, valuesPrefix, descriptions); err != nil {
			return err
		}
		break
	}
	return nil
}

// decodeDescriptions reads all YAML documents from one values.yaml file.
func decodeDescriptions(data []byte, valuesPrefix []string, descriptions map[string]string) error {
	decoder := yaml.NewDecoder(bytes.NewReader(data))
	for documentNumber := 1; ; documentNumber++ {
		var document yaml.Node
		if err := decoder.Decode(&document); err != nil {
			if err == io.EOF {
				return nil
			}
			return fmt.Errorf("decode YAML document %d: %w", documentNumber, err)
		}
		if len(document.Content) == 0 {
			continue
		}
		root := document.Content[0]
		if description := normalizeComment(document.HeadComment, root.HeadComment, root.LineComment); description != "" {
			descriptions[jsonPointer(valuesPrefix)] = description
		}
		collectDescriptions(root, valuesPrefix, descriptions)
	}
}

// collectDescriptions walks mapping and sequence nodes and records comments by
// RFC 6901 JSON pointer.
func collectDescriptions(node *yaml.Node, valuePath []string, descriptions map[string]string) {
	switch node.Kind {
	case yaml.DocumentNode:
		if len(node.Content) > 0 {
			collectDescriptions(node.Content[0], valuePath, descriptions)
		}
	case yaml.MappingNode:
		for index := 0; index+1 < len(node.Content); index += 2 {
			key := node.Content[index]
			value := node.Content[index+1]
			if key.Value == "<<" {
				continue
			}
			childPath := appendValuePath(valuePath, key.Value)
			if description := normalizeComment(key.HeadComment, key.LineComment, value.LineComment); description != "" {
				descriptions[jsonPointer(childPath)] = description
			}
			collectDescriptions(value, childPath, descriptions)
		}
	case yaml.SequenceNode:
		for index, child := range node.Content {
			childPath := appendValuePath(valuePath, strconv.Itoa(index))
			if description := normalizeComment(child.HeadComment, child.LineComment); description != "" {
				descriptions[jsonPointer(childPath)] = description
			}
			collectDescriptions(child, childPath, descriptions)
		}
	case yaml.AliasNode:
		// Alias comments describe the alias location, not the anchor's original
		// path. Do not copy comments from the target into another value path.
		return
	}
}

// jsonPointer encodes a value path as an RFC 6901 JSON pointer.
func jsonPointer(valuePath []string) string {
	if len(valuePath) == 0 {
		return ""
	}
	escaped := make([]string, len(valuePath))
	for index, part := range valuePath {
		part = strings.ReplaceAll(part, "~", "~0")
		escaped[index] = strings.ReplaceAll(part, "/", "~1")
	}
	return "/" + strings.Join(escaped, "/")
}

// normalizeComment removes YAML and helm-docs markers. It also removes empty
// lines and documentation directives.
func normalizeComment(comments ...string) string {
	lines := make([]string, 0)
	for _, comment := range comments {
		for line := range strings.SplitSeq(comment, "\n") {
			line = strings.TrimSpace(line)
			line = strings.TrimSpace(strings.TrimPrefix(line, "#"))
			if strings.HasPrefix(line, "@") {
				continue
			}
			line = strings.TrimSpace(strings.TrimPrefix(line, "--"))
			if line != "" {
				lines = append(lines, line)
			}
		}
	}
	return strings.Join(lines, "\n")
}
