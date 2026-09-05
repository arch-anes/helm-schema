import HelmSchema

set_option autoImplicit false

open HelmSchema

/-- Print one runtime-test error and retain the combined result. -/
def require (condition : Bool) (message : String) : IO Bool := do
  if condition then
    pure true
  else
    IO.eprintln message
    pure false

/-- Run executable examples for the main semantic branches. The theorem files
    provide universal results; these examples also test compiled evaluation. -/
def main : IO UInt32 := do
  let servicePath := [UsageSegment.property "service"]
  let usage := Usage.empty.record servicePath .open
  let usageOK ← require
    (List.contains usage.observations
        { path := servicePath, mode := .read } &&
      List.contains usage.observations
        { path := servicePath, mode := .open } &&
      List.contains usage.nodes servicePath)
    "open usage did not include both read and open observations"

  let closedPolicy := Policy.object [("enabled", .typed .boolean)] none
  let closedSchema := generate closedPolicy
  let knownValue := JValue.object [("enabled", .bool true)]
  let typoValue := JValue.object [("enablede", .bool true)]
  let closedOK ← require
    (accepts closedSchema knownValue && !accepts closedSchema typoValue)
    "closed generated object accepted a typo or rejected its known property"

  let dynamicPolicy := Policy.object [] (some (.typed .integer))
  let dynamicSchema := generate dynamicPolicy
  let integerEntry := JValue.object [("http", .number (.integer 8080))]
  let stringEntry := JValue.object [("http", .string "8080")]
  let dynamicOK ← require
    (accepts dynamicSchema integerEntry && !accepts dynamicSchema stringEntry)
    "dynamic entry schema did not enforce its child type"

  let dynamicPath := [UsageSegment.property "services"]
  let dynamicResult := analyze (.sequence
    (.operation (.selectDynamic dynamicPath))
    (.operation (.complete (dynamicPath ++ [.additional]))))
  let analyzerOK ← require
    (List.contains dynamicResult.usage.observations
      { path := dynamicPath ++ [.additional], mode := .read } &&
     List.contains dynamicResult.reasons
      { path := dynamicPath, kind := .dynamicSelection })
    "dynamic analysis omitted usage or its evidence reason"

  let unusedSelection := analyze (.operation (.selectFixed dynamicPath "fixed"))
  let unusedSelectionOK ← require
    (unusedSelection.usage == Usage.empty)
    "an unused static selection incorrectly created usage"

  let emptyTruthInput : BoundaryInput :=
    { usage := { isRead := true } }
  let structuralTruthInput : BoundaryInput :=
    { usage := { isRead := true, properties := [("enabled", {})] } }
  let boundaryOK ← require
    (allowsUnnamed emptyTruthInput && !allowsUnnamed structuralTruthInput)
    "truth-test boundary decision ignored its structural field contract"

  let fixed : ValueInput := .fixed (.string "value") false
  let enabled : LeafInput :=
    { defaultValue := .present (.bool true) (some .boolean)
    , directUsage := true
    , inheritedOpen := false
    }
  let missing : LeafInput :=
    { defaultValue := .missing, directUsage := true, inheritedOpen := false }
  let flatInput : CoreInput :=
    { properties :=
        [("fixed", fixed), ("enabled", .leaf enabled),
          ("missing", .leaf missing)] }
  let flatSchema := generate (corePolicy flatInput)
  let flatOK ← require
    (accepts flatSchema (.object
      [("fixed", .string "value"), ("enabled", .bool false),
        ("missing", .string "free")]) &&
     !accepts flatSchema (.object
      [("fixed", .string "changed"), ("enabled", .bool false),
        ("missing", .string "free")]))
    "flat core policy did not keep an unused default constant"

  let nullable : LeafInput :=
    { defaultValue := .present (.string "coalesced") (some .string)
    , directUsage := true
    , inheritedOpen := false
    , explicitNull := true
    }
  let nullableSchema := generate (leafPolicy nullable)
  let explicitNullOK ← require
    (accepts nullableSchema .null &&
      accepts nullableSchema (.string "override") &&
      !accepts nullableSchema (.bool true))
    "explicit null did not preserve the inferred scalar contract"

  let settings : ValueInput := .object
    [("enabled", .leaf enabled)]
    none
    { defaultValues := [.bool true]
    , usage := { properties := [("enabled", { isRead := true })] }
    }
    false
  let objectSchema := generate
    (corePolicy { properties := [("settings", settings)] })
  let objectOK ← require
    (accepts objectSchema
      (.object [("settings", .object [("enabled", .bool false)])]) &&
      !accepts objectSchema
        (.object [("settings", .object [("enablede", .bool false)])]))
    "a closed nested object accepted an unknown direct child"

  let conjunction := Schema.allOf
    [.typed .number, .anyOf [.constant (.number (.integer 2)), .typed .integer]]
  let conjunctionOK ← require
    (accepts conjunction (.number (.ofScientific 20 1)) &&
      !accepts conjunction (.number (.ofScientific 25 1)))
    "schema conjunction did not enforce every constraint"

  let arrayItem : ValueInput := .object
    [("name", .typed .string)] none {} false
  let usedArraySchema := generate (valuePolicy (.array arrayItem))
  let usedArrayOK ← require
    (accepts usedArraySchema
        (.array [.object [("name", .string "one")]]) &&
      !accepts usedArraySchema
        (.array [.object [("name", .number (.integer 1))]]) &&
      !accepts usedArraySchema
        (.array [.object [("name", .string "one"),
          ("unused", .bool true)] ]))
    "used array items did not enforce their recursive object contract"

  let shapeAlternatives : ValueInput := .anyOf
    [.fixed (.string "off") false,
      .object [("enabled", .typed .boolean)] none {} false]
  let shapeSchema := generate (valuePolicy shapeAlternatives)
  let shapeOK ← require
    (accepts shapeSchema (.string "off") &&
      accepts shapeSchema (.object [("enabled", .bool true)]) &&
      !accepts shapeSchema (.string "on") &&
      !accepts shapeSchema (.object [("enablede", .bool true)]))
    "shape alternatives accepted a value outside every alternative"

  let dynamicEntry : ValueInput := .object
    [("enabled", .typed .boolean)] none {} false
  let structuredDynamic : ValueInput := .object [] (some dynamicEntry) {} false
  let structuredSchema := generate (valuePolicy structuredDynamic)
  let structuredOK ← require
    (accepts structuredSchema
        (.object [("first", .object [("enabled", .bool true)])]) &&
      !accepts structuredSchema
        (.object [("first", .object [("enablede", .bool true)])]) &&
      !accepts structuredSchema
        (.object [("first", .string "enabled")]))
    "structured dynamic entries did not enforce their recursive contract"

  let dependencyFlow : ValueFlow :=
    { source := ["global"], destination := ["worker", "global"] }
  let sourceRegion :=
    [UsageSegment.property "global", UsageSegment.property "region"]
  let destinationRegion :=
    [UsageSegment.property "worker", UsageSegment.property "global",
      UsageSegment.property "region"]
  let propagated := applyValueFlows
    (Usage.empty.record sourceRegion .exact) [dependencyFlow]
  let flowOK ← require
    (propagated.observations.contains
      { path := destinationRegion, mode := .exact })
    "dependency flow did not retain the path suffix and usage mode"

  if usageOK && closedOK && dynamicOK && analyzerOK && boundaryOK && flatOK &&
      explicitNullOK && objectOK && unusedSelectionOK && conjunctionOK &&
      usedArrayOK && shapeOK && structuredOK && flowOK then
    pure 0
  else
    pure 1
