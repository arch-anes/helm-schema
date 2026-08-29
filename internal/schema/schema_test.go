package schema

// This file tests strict schema output, shape inference, null handling,
// descriptions, stable output, and invalid defaults.

import (
	"bytes"
	"encoding/json"
	"math"
	"strings"
	"testing"

	"github.com/arch-anes/helm-schema/internal/analyze"
)

func TestGenerateUsedFixedAndMissingValues(t *testing.T) {
	t.Parallel()

	defaults := map[string]any{
		"image": map[string]any{
			"repository": "example/service",
			"tag":        "latest",
		},
		"internal": "unchanged",
		"replicas": 2,
	}
	usage := &analyze.Usage{Properties: map[string]*analyze.Usage{
		"image": {
			Properties: map[string]*analyze.Usage{
				"tag": {Read: true},
			},
		},
		"missing":  {Read: true},
		"replicas": {Read: true},
	}}

	got, err := Generate(defaults, map[string]string{
		"/image/tag": "Container image tag.",
		"/replicas":  "Number of replicas.",
	}, usage)
	if err != nil {
		t.Fatal(err)
	}

	wantIndented := `{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "type": "object",
  "properties": {
    "image": {
      "type": "object",
      "properties": {
        "repository": {
          "const": "example/service"
        },
        "tag": {
          "type": "string",
          "description": "Container image tag.",
          "default": "latest"
        }
      },
      "additionalProperties": false
    },
    "internal": {
      "const": "unchanged"
    },
    "missing": {},
    "replicas": {
      "type": "integer",
      "description": "Number of replicas.",
      "default": 2
    }
  },
  "additionalProperties": false
}
`
	var want bytes.Buffer
	if err := json.Compact(&want, []byte(wantIndented)); err != nil {
		t.Fatal(err)
	}
	want.WriteByte('\n')
	if !bytes.Equal(got, want.Bytes()) {
		t.Fatalf("unexpected schema:\n%s\nwant:\n%s", got, want.Bytes())
	}

	again, err := Generate(defaults, map[string]string{
		"/image/tag": "Container image tag.",
		"/replicas":  "Number of replicas.",
	}, usage)
	if err != nil {
		t.Fatal(err)
	}
	if string(got) != string(again) {
		t.Fatal("generation is not deterministic")
	}
}

func TestGenerateOpenObject(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"labels": map[string]any{"app": "example"},
	}, nil, &analyze.Usage{Open: true})
	if err != nil {
		t.Fatal(err)
	}

	root := decodeSchema(t, got)
	if root["additionalProperties"] != true {
		t.Fatalf("root is not open: %#v", root["additionalProperties"])
	}
	labels := property(t, root, "labels")
	if labels["additionalProperties"] != true {
		t.Fatalf("nested object is not open: %#v", labels["additionalProperties"])
	}
	if _, found := property(t, labels, "app")["default"]; !found {
		t.Fatal("complete use did not make the declared child configurable")
	}
}

func TestGenerateOpenParentOpensKnownChildContract(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"settings": map[string]any{
			"nested": map[string]any{"enabled": true, "declared": "value"},
		},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"settings": {
			Open: true,
			Properties: map[string]*analyze.Usage{
				"nested": {Properties: map[string]*analyze.Usage{"enabled": {Read: true}}},
			},
		},
	}})
	if err != nil {
		t.Fatal(err)
	}

	settings := property(t, decodeSchema(t, got), "settings")
	if settings["additionalProperties"] != true {
		t.Fatalf("open parent rejects unknown direct properties: %#v", settings)
	}
	nested := property(t, settings, "nested")
	if nested["additionalProperties"] != true {
		t.Fatalf("complete parent use did not open a known child: %#v", nested)
	}
	if _, configurable := property(t, nested, "declared")["const"]; configurable {
		t.Fatalf("complete parent use left a declared descendant fixed: %#v", nested)
	}
}

func TestGenerateOpenParentDoesNotFixKnownScalarShape(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"settings": map[string]any{"enabled": true},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"settings": {Open: true},
	}})
	if err != nil {
		t.Fatal(err)
	}

	enabled := property(t, property(t, decodeSchema(t, got), "settings"), "enabled")
	if _, constrained := enabled["type"]; constrained {
		t.Fatalf("complete parent use fixed a known scalar shape: %#v", enabled)
	}
}

func TestGenerateOpenParentDoesNotFixKnownArrayShape(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"settings": map[string]any{"rules": []any{"default"}},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"settings": {Open: true},
	}})
	if err != nil {
		t.Fatal(err)
	}

	rules := property(t, property(t, decodeSchema(t, got), "settings"), "rules")
	if _, constrained := rules["type"]; constrained {
		t.Fatalf("complete parent use fixed a known array shape: %#v", rules)
	}
}

func TestGenerateGuardedDynamicEntryAllowsNull(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"ports": map[string]any{
			"http": map[string]any{"port": 80},
		},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"ports": {Elements: &analyze.Usage{
			Read:       true,
			Properties: map[string]*analyze.Usage{"port": {Read: true}},
		}},
	}})
	if err != nil {
		t.Fatal(err)
	}

	ports := property(t, decodeSchema(t, got), "ports")
	object, ok := ports["anyOf"].([]any)[0].(map[string]any)
	if !ok {
		t.Fatalf("dynamic object alternative is missing: %#v", ports)
	}
	entry := property(t, object, "http")
	if !schemaAllowsNull(entry) {
		t.Fatalf("guarded dynamic entry rejects null: %#v", entry)
	}
}

func TestGenerateObjectReadAllowsMembershipChangesOnlyWhenEmpty(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"feature": map[string]any{"fixed": "unchanged"},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"feature": {Read: true},
	}})
	if err != nil {
		t.Fatal(err)
	}
	feature := property(t, decodeSchema(t, got), "feature")
	if feature["additionalProperties"] != false {
		t.Fatalf("a non-empty truth-tested object accepts unknown properties: %#v", feature)
	}
	if property(t, feature, "fixed")["const"] != "unchanged" {
		t.Fatalf("truth testing made an unused member configurable: %#v", feature)
	}

	empty, err := Generate(map[string]any{"feature": map[string]any{}}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"feature": {Read: true},
	}})
	if err != nil {
		t.Fatal(err)
	}
	if got := property(t, decodeSchema(t, empty), "feature")["additionalProperties"]; got != true {
		t.Fatalf("an empty truth-tested object rejects new properties: %#v", got)
	}

	nullOnly, err := Generate(map[string]any{
		"feature": map[string]any{"optional": nil},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"feature": {Read: true},
	}})
	if err != nil {
		t.Fatal(err)
	}
	if got := property(t, decodeSchema(t, nullOnly), "feature")["additionalProperties"]; got != true {
		t.Fatalf("a null-only truth-tested object rejects new properties: %#v", got)
	}
}

func TestGenerateGuardedObjectWithKnownFieldsStaysClosed(t *testing.T) {
	t.Parallel()

	usage := &analyze.Usage{Properties: map[string]*analyze.Usage{
		"probe": {
			Read: true,
			Properties: map[string]*analyze.Usage{
				"enabled": {Read: true},
				"path":    {Read: true},
			},
		},
	}}
	for _, test := range []struct {
		name     string
		defaults map[string]any
	}{
		{name: "missing default", defaults: map[string]any{}},
		{name: "empty default", defaults: map[string]any{"probe": map[string]any{}}},
		{name: "null-only default", defaults: map[string]any{"probe": map[string]any{"optional": nil}}},
	} {
		t.Run(test.name, func(t *testing.T) {
			t.Parallel()

			generated, err := Generate(test.defaults, nil, usage)
			if err != nil {
				t.Fatal(err)
			}
			probe := property(t, decodeSchema(t, generated), "probe")
			if probe["additionalProperties"] != false {
				t.Fatalf("guarded object with known fields is open: %#v", probe)
			}
			property(t, probe, "enabled")
			property(t, probe, "path")
		})
	}
}

func TestGenerateKeyOnlyIterationChangesMembershipNotValues(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"entries": map[string]any{"existing": "unchanged"},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"entries": {Iterated: true},
	}})
	if err != nil {
		t.Fatal(err)
	}

	entries := property(t, decodeSchema(t, got), "entries")
	alternatives, ok := entries["anyOf"].([]any)
	if !ok || len(alternatives) != 2 {
		t.Fatalf("collection alternatives are missing: %#v", entries)
	}
	object := alternatives[0].(map[string]any)
	if property(t, object, "existing")["const"] != "unchanged" {
		t.Fatalf("unused existing value is configurable: %#v", object)
	}
	if object["additionalProperties"] != true {
		t.Fatalf("new map entries are not permitted: %#v", object)
	}
	array := alternatives[1].(map[string]any)
	items, ok := array["items"].(map[string]any)
	if !ok || len(items) != 0 {
		t.Fatalf("key-only iteration constrained replacement items: %#v", array)
	}
}

func TestGenerateGenericNestedWalkAllowsScalarChanges(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"settings": map[string]any{"enabled": true},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"settings": {
			Iterated: true,
			Properties: map[string]*analyze.Usage{
				"enabled": {Read: true},
			},
			Elements: &analyze.Usage{Open: true, Iterated: true},
		},
	}})
	if err != nil {
		t.Fatal(err)
	}

	settings := property(t, decodeSchema(t, got), "settings")
	object := settings["anyOf"].([]any)[0].(map[string]any)
	enabled := property(t, object, "enabled")
	scalar := enabled["anyOf"].([]any)[0].(map[string]any)
	if scalar["const"] != nil || scalar["type"] != "boolean" {
		t.Fatalf("generic nested walk fixed a scalar to its default: %#v", enabled)
	}
}

func TestGenerateDynamicObjectProperties(t *testing.T) {
	t.Parallel()

	portsUsage := &analyze.Usage{
		Additional: &analyze.Usage{Properties: map[string]*analyze.Usage{
			"port": {Read: true},
		}},
	}
	got, err := Generate(map[string]any{
		"ports": map[string]any{
			"http": map[string]any{
				"port":     8080,
				"protocol": "TCP",
			},
		},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{"ports": portsUsage}})
	if err != nil {
		t.Fatal(err)
	}

	root := decodeSchema(t, got)
	ports := property(t, root, "ports")
	http := property(t, ports, "http")
	if property(t, http, "port")["type"] != "integer" {
		t.Fatalf("existing dynamic entry did not infer its used field: %#v", http)
	}
	if property(t, http, "protocol")["const"] != "TCP" {
		t.Fatalf("unused field in existing entry is not fixed: %#v", http)
	}
	additional, ok := ports["additionalProperties"].(map[string]any)
	if !ok {
		t.Fatalf("dynamic property schema is missing: %#v", ports["additionalProperties"])
	}
	if property(t, additional, "port")["type"] != "integer" {
		t.Fatalf("dynamic property field type was not inferred: %#v", additional)
	}
}

func TestGenerateCompleteDynamicValuesDoNotCopyExampleTypes(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"options": map[string]any{"verbosity": 3},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"options": {
			Iterated: true,
			Elements: &analyze.Usage{Open: true},
		},
	}})
	if err != nil {
		t.Fatal(err)
	}

	options := property(t, decodeSchema(t, got), "options")
	alternatives := options["anyOf"].([]any)
	object := alternatives[0].(map[string]any)
	verbosity := property(t, object, "verbosity")
	if _, constrained := verbosity["type"]; constrained {
		t.Fatalf("known dynamic value copied its example type: %#v", verbosity)
	}
	additional, ok := object["additionalProperties"].(map[string]any)
	if !ok || len(additional) != 0 {
		t.Fatalf("complete dynamic values copied an example type: %#v", options)
	}
}

func TestCompleteMissingValueAcceptsEveryJSONShape(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"payload": {
			Open:     true,
			Iterated: true,
			Elements: &analyze.Usage{Properties: map[string]*analyze.Usage{
				"name": {Read: true},
			}},
		},
	}})
	if err != nil {
		t.Fatal(err)
	}

	payload := property(t, decodeSchema(t, got), "payload")
	if len(payload) != 0 {
		t.Fatalf("complete missing value was type-constrained: %#v", payload)
	}
}

func TestConfigurableTemplateStringDoesNotFixScalarType(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"enabled": "{{ .Values.metrics.enabled }}",
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"enabled": {Read: true},
	}})
	if err != nil {
		t.Fatal(err)
	}

	enabled := property(t, decodeSchema(t, got), "enabled")
	if _, constrained := enabled["type"]; constrained {
		t.Fatalf("template string fixed its override type: %#v", enabled)
	}
	if enabled["default"] != "{{ .Values.metrics.enabled }}" {
		t.Fatalf("template string default was lost: %#v", enabled)
	}
}

func TestMissingStructuredPropertyAcceptsNull(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"settings": {Elements: &analyze.Usage{Properties: map[string]*analyze.Usage{
			"enabled": {Read: true},
		}}},
	}})
	if err != nil {
		t.Fatal(err)
	}

	settings := property(t, decodeSchema(t, got), "settings")
	if !schemaAllowsNull(settings) {
		t.Fatalf("configurable property rejected null: %#v", settings)
	}
}

func TestGenerateInfersDynamicFieldFromExamplesWhereItExists(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"ports": map[string]any{
			"withPort":    map[string]any{"port": 8080},
			"withoutPort": map[string]any{"protocol": "TCP"},
		},
	}, nil, &analyze.Usage{Properties: map[string]*analyze.Usage{
		"ports": {Additional: &analyze.Usage{Properties: map[string]*analyze.Usage{
			"port": {Read: true},
		}}},
	}})
	if err != nil {
		t.Fatal(err)
	}

	ports := property(t, decodeSchema(t, got), "ports")
	additional, ok := ports["additionalProperties"].(map[string]any)
	if !ok {
		t.Fatalf("dynamic entry schema is missing: %#v", ports)
	}
	if property(t, additional, "port")["type"] != "integer" {
		t.Fatalf("present example did not provide field type: %#v", additional)
	}
}

func TestGenerateIgnoresIncompatibleDynamicEntryExamples(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"imageSelector": "mainImage",
		"mainImage": map[string]any{
			"repository": "example/application",
		},
	}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"imageSelector": {Read: true},
		},
		Elements: &analyze.Usage{Properties: map[string]*analyze.Usage{
			"repository": {Read: true},
		}},
	})
	if err != nil {
		t.Fatal(err)
	}

	root := decodeSchema(t, got)
	additional, ok := root["additionalProperties"].(map[string]any)
	if !ok {
		t.Fatalf("dynamic root entry schema is missing: %#v", root)
	}
	if additional["additionalProperties"] != false {
		t.Fatalf("incompatible scalar example opened dynamic entries: %#v", additional)
	}
	if property(t, additional, "repository")["type"] != "string" {
		t.Fatalf("compatible object example did not provide field type: %#v", additional)
	}
}

func TestDynamicSelectorDoesNotOpenUnrelatedKnownProperty(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{
		"global": map[string]any{
			"traefik": map[string]any{"commonMiddlewares": []any{}},
		},
		"mainImage": map[string]any{
			"repository": "example/application",
			"tag":        "latest",
		},
	}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"global": {Properties: map[string]*analyze.Usage{
				"traefik": {Properties: map[string]*analyze.Usage{
					"commonMiddlewares": {Read: true},
				}},
			}},
		},
		Additional: &analyze.Usage{
			Open: true,
			Properties: map[string]*analyze.Usage{
				"repository": {Read: true},
				"tag":        {Read: true},
			},
		},
	})
	if err != nil {
		t.Fatal(err)
	}

	root := decodeSchema(t, got)
	global := property(t, root, "global")
	if global["additionalProperties"] != false {
		t.Fatalf("unrelated dynamic selector opened global: %#v", global)
	}
	traefik := property(t, global, "traefik")
	if traefik["additionalProperties"] != false {
		t.Fatalf("unrelated dynamic selector opened global.traefik: %#v", traefik)
	}
	mainImage := property(t, root, "mainImage")
	if _, fixed := mainImage["const"]; fixed || mainImage["default"] == nil {
		t.Fatalf("dynamic image selector did not apply to matching default: %#v", mainImage)
	}
}

func TestGenerateListKeepsOriginalDefaultAndUsesStrictReplacementItems(t *testing.T) {
	t.Parallel()

	items := []any{map[string]any{"name": "first", "unused": true}}
	got, err := Generate(map[string]any{"items": items}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"items": {
				Read: true,
				Items: &analyze.Usage{Properties: map[string]*analyze.Usage{
					"name": {Read: true},
				}},
			},
		},
	})
	if err != nil {
		t.Fatal(err)
	}

	root := decodeSchema(t, got)
	itemList := property(t, root, "items")
	if itemList["type"] != "array" {
		t.Fatalf("list type was not inferred: %#v", itemList)
	}
	alternatives, ok := itemList["anyOf"].([]any)
	if !ok || len(alternatives) != 2 {
		t.Fatalf("list alternatives are missing: %#v", itemList["anyOf"])
	}
	if constant := alternatives[0].(map[string]any)["const"]; !jsonEqual(constant, items) {
		t.Fatalf("original list constant changed: %#v", constant)
	}
	replacement := alternatives[1].(map[string]any)
	itemSchema, ok := replacement["items"].(map[string]any)
	if !ok {
		t.Fatalf("replacement item schema is missing: %#v", replacement)
	}
	if property(t, itemSchema, "name")["type"] != "string" {
		t.Fatalf("used item field type was not inferred: %#v", itemSchema)
	}
	if _, exists := itemSchema["properties"].(map[string]any)["unused"]; exists {
		t.Fatalf("unused item field is configurable: %#v", itemSchema)
	}
	if itemSchema["additionalProperties"] != false {
		t.Fatalf("replacement item is not closed: %#v", itemSchema)
	}
	if !jsonEqual(itemList["default"], items) {
		t.Fatalf("list default changed: %#v", itemList["default"])
	}
}

func TestGenerateCompleteListUseAcceptsCompleteReplacementItems(t *testing.T) {
	t.Parallel()

	items := []any{map[string]any{"name": "first", "unused": true}}
	got, err := Generate(map[string]any{"items": items}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"items": {
				Open: true,
				Items: &analyze.Usage{Properties: map[string]*analyze.Usage{
					"name": {Read: true},
				}},
			},
		},
	})
	if err != nil {
		t.Fatal(err)
	}

	itemList := property(t, decodeSchema(t, got), "items")
	if itemList["type"] != "array" {
		t.Fatalf("complete list use lost its array type: %#v", itemList)
	}
	itemSchema := itemList["items"].(map[string]any)
	if len(itemSchema) != 0 {
		t.Fatalf("complete list use constrained replacement items: %#v", itemSchema)
	}
}

func TestGenerateNullableStructuredValue(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{"settings": nil}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"settings": {
				Read: true,
				Properties: map[string]*analyze.Usage{
					"enabled": {Read: true},
				},
			},
		},
	})
	if err != nil {
		t.Fatal(err)
	}

	settings := property(t, decodeSchema(t, got), "settings")
	types, ok := settings["type"].([]any)
	if !ok || len(types) != 2 || types[0] != "object" || types[1] != "null" {
		t.Fatalf("nullable object type is wrong: %#v", settings["type"])
	}
	if value, found := settings["default"]; !found || value != nil {
		t.Fatalf("explicit null default was lost: %#v", settings)
	}
}

func TestGenerateKeepsUnusedNullDefaultFixed(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{"optional": nil}, nil, nil, []string{"optional"})
	if err != nil {
		t.Fatal(err)
	}
	optional := property(t, decodeSchema(t, got), "optional")
	if constant, exists := optional["const"]; !exists || constant != nil {
		t.Fatalf("unused null default is not fixed: %#v", optional)
	}
}

func TestGenerateAcceptsRawNullAndCoalescedDefault(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{"message": "from-dependency"}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"message": {Read: true},
		},
	}, []string{"message"})
	if err != nil {
		t.Fatal(err)
	}

	message := property(t, decodeSchema(t, got), "message")
	alternatives, ok := message["anyOf"].([]any)
	if !ok || len(alternatives) != 2 {
		t.Fatalf("message alternatives = %#v, want null and string", message["anyOf"])
	}
	if !jsonEqual(alternatives[0], map[string]any{"const": nil}) {
		t.Fatalf("first message alternative = %#v, want null", alternatives[0])
	}
	if message["default"] != "from-dependency" {
		t.Fatalf("message default = %#v, want coalesced value", message["default"])
	}
}

func TestGenerateUsesRFC6901DescriptionPointers(t *testing.T) {
	t.Parallel()

	key := "a/b~c"
	got, err := Generate(map[string]any{key: true}, map[string]string{
		"/a~1b~0c": "Escaped key.",
	}, &analyze.Usage{Properties: map[string]*analyze.Usage{key: {Read: true}}})
	if err != nil {
		t.Fatal(err)
	}
	if property(t, decodeSchema(t, got), key)["description"] != "Escaped key." {
		t.Fatal("description pointer was not decoded by path construction")
	}
}

func TestGenerateUsesAlternativesForShapeConflict(t *testing.T) {
	t.Parallel()

	got, err := Generate(map[string]any{"value": "scalar"}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"value": {Properties: map[string]*analyze.Usage{"child": {Read: true}}},
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	value := property(t, decodeSchema(t, got), "value")
	alternatives, ok := value["anyOf"].([]any)
	if !ok || len(alternatives) != 2 {
		t.Fatalf("shape alternatives = %#v", value["anyOf"])
	}
	if alternatives[0].(map[string]any)["const"] != "scalar" {
		t.Fatalf("scalar default alternative = %#v", alternatives[0])
	}
	object := alternatives[1].(map[string]any)
	if object["type"] != "object" || property(t, object, "child") == nil {
		t.Fatalf("object alternative = %#v", object)
	}
}

func TestGenerateRejectsNonJSONDefault(t *testing.T) {
	t.Parallel()

	_, err := Generate(map[string]any{"invalid": math.Inf(1)}, nil, &analyze.Usage{
		Properties: map[string]*analyze.Usage{"invalid": {Read: true}},
	})
	if err == nil || !strings.Contains(err.Error(), "/invalid") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestGenerateInfersJSONNumberTypes(t *testing.T) {
	t.Parallel()

	usage := &analyze.Usage{
		Properties: map[string]*analyze.Usage{
			"integer": {Read: true},
			"number":  {Read: true},
		},
	}
	got, err := Generate(map[string]any{
		"integer": json.Number("2"),
		"number":  json.Number("2.5"),
	}, nil, usage)
	if err != nil {
		t.Fatal(err)
	}

	root := decodeSchema(t, got)
	if valueType := property(t, root, "integer")["type"]; valueType != "integer" {
		t.Fatalf("integer type = %q, want integer", valueType)
	}
	if valueType := property(t, root, "number")["type"]; valueType != "number" {
		t.Fatalf("number type = %q, want number", valueType)
	}
}

func decodeSchema(t *testing.T, data []byte) map[string]any {
	t.Helper()
	var result map[string]any
	if err := json.Unmarshal(data, &result); err != nil {
		t.Fatal(err)
	}
	return result
}

func property(t *testing.T, schema map[string]any, name string) map[string]any {
	t.Helper()
	properties, ok := schema["properties"].(map[string]any)
	if !ok {
		t.Fatalf("schema has no properties: %#v", schema)
	}
	value, ok := properties[name].(map[string]any)
	if !ok {
		t.Fatalf("schema has no property %q: %#v", name, properties)
	}
	return value
}

func schemaAllowsNull(schema map[string]any) bool {
	if schema["const"] == nil {
		if _, hasConst := schema["const"]; hasConst {
			return true
		}
	}
	switch types := schema["type"].(type) {
	case string:
		if types == "null" {
			return true
		}
	case []any:
		for _, item := range types {
			if item == "null" {
				return true
			}
		}
	}
	alternatives, _ := schema["anyOf"].([]any)
	for _, alternative := range alternatives {
		if schemaAllowsNull(alternative.(map[string]any)) {
			return true
		}
	}
	return false
}

func jsonEqual(left, right any) bool {
	leftJSON, leftErr := json.Marshal(left)
	rightJSON, rightErr := json.Marshal(right)
	return leftErr == nil && rightErr == nil && string(leftJSON) == string(rightJSON)
}
