import HelmSchema
import Lean.Data.Json

set_option autoImplicit false

open HelmSchema

namespace Verify

/-- Parsing either returns a value or a protocol error message. -/
abbrev ParseM := Except String

/-- Read a required object field. -/
def field (json : Lean.Json) (name : String) : ParseM Lean.Json :=
  json.getObjVal? name

/-- Read a required string field. -/
def stringField (json : Lean.Json) (name : String) : ParseM String := do
  (← field json name).getStr?

/-- Read a required Boolean field. -/
def boolField (json : Lean.Json) (name : String) : ParseM Bool := do
  (← field json name).getBool?

/-- Convert every JSON array element with the supplied parser. -/
def arrayOf {α : Type} (json : Lean.Json)
    (parse : Lean.Json → ParseM α) : ParseM (List α) := do
  let values ← json.getArr?
  values.toList.mapM parse

/-- Reject duplicate labels in one list-backed protocol collection. -/
def requireUniqueLabels {α : Type} (kind : String) :
    List (String × α) → ParseM Unit
  | [] => pure ()
  | (name, _) :: rest => do
      if rest.any fun entry => entry.1 == name then
        throw s!"duplicate {kind} {name}"
      requireUniqueLabels kind rest

/-- Reject duplicate names before list-backed objects enter the formal model. -/
def requireUniqueNames {α : Type} (values : List (String × α)) : ParseM Unit :=
  requireUniqueLabels "object property" values

/-- Parse one path segment from the conformance protocol. -/
def parseSegment (json : Lean.Json) : ParseM UsageSegment := do
  match ← stringField json "kind" with
  | "property" => pure (.property (← stringField json "name"))
  | "additional" => pure .additional
  | "items" => pure .items
  | "elements" => pure .elements
  | kind => throw s!"unknown usage segment {kind}"

/-- Parse one normalized value path. -/
def parsePath (json : Lean.Json) : ParseM (List UsageSegment) :=
  arrayOf json parseSegment

/-- Parse one usage mode. -/
def parseMode (name : String) : ParseM UsageMode :=
  match name with
  | "read" => pure .read
  | "exact" => pure .exact
  | "open" => pure .open
  | "allowUnknown" => pure .allowUnknown
  | "iterate" => pure .iterate
  | _ => throw s!"unknown usage mode {name}"

/-- Parse one conservative-analysis reason. -/
def parseFallbackReason (name : String) : ParseM FallbackReason :=
  match name with
  | "unknownFunction" => pure .unknownFunction
  | "dynamicTemplate" => pure .dynamicTemplate
  | "externalOperation" => pure .externalOperation
  | "analysisLimit" => pure .analysisLimit
  | "unsupportedNode" => pure .unsupportedNode
  | _ => throw s!"unknown fallback reason {name}"

/-- Parse one normalized operation. The protocol intentionally contains only
    behavior classes, not Helm function names. -/
def parseOperation (json : Lean.Json) : ParseM TemplateOperation := do
  let kind ← stringField json "kind"
  let path ← parsePath (← field json "path")
  match kind with
  | "selectFixed" => pure (.selectFixed path (← stringField json "name"))
  | "selectFinite" =>
      let names ← arrayOf (← field json "names") Lean.Json.getStr?
      pure (.selectFinite path names)
  | "selectDynamic" => pure (.selectDynamic path)
  | "read" => pure (.read path)
  | "exact" => pure (.exact path)
  | "complete" => pure (.complete path)
  | "allowUnknown" => pure (.allowUnknown path)
  | "iterate" => pure (.iterate path)
  | "unsupported" => pure (.unsupported path
      (← parseMode (← stringField json "mode"))
      (← parseFallbackReason (← stringField json "reason")))
  | _ => throw s!"unsupported conformance operation {kind}"

/-- Parse one production function behavior class. -/
def parseFunctionClass (name : String) : ParseM FunctionOperationClass :=
  match name with
  | "semantic-transfer" => pure .semanticTransfer
  | "origin-preserving" => pure .originPreserving
  | "exact" => pure .exactConsumer
  | "allow-unknown" => pure .keyConsumer
  | "complete" => pure .completeConsumer
  | "read" => pure .readConsumer
  | "none" => pure .harmless
  | "conservative-complete" => pure .conservativeComplete
  | _ => throw s!"unsupported function operation class {name}"

/-- Render the normalized operation name used by the conformance protocol. -/
def functionLoweringName (functionClass : FunctionOperationClass) : String :=
  match functionClass.lower [] with
  | none => "deferred"
  | some (.exact _) => "exact"
  | some (.allowUnknown _) => "allowUnknown"
  | some (.complete _) => "complete"
  | some (.read _) => "read"
  | some (.unsupported _ .open .externalOperation) =>
      "unsupported:open:externalOperation"
  | some _ => "invalid"

/-- Verify one row of the production function-to-formal-operation matrix.
    Return its name so the document parser can reject duplicate rows. -/
def verifyFunction (json : Lean.Json) : ParseM (String × Option String) := do
  let name ← stringField json "name"
  if name.isEmpty then
    throw "function matrix contains an empty name"
  let functionClass ← parseFunctionClass (← stringField json "class")
  let goLowering ← stringField json "lowering"
  let leanLowering := functionLoweringName functionClass
  if goLowering == leanLowering then
    pure (name, none)
  else
    pure (name, some s!"{name}: Go lowering {goLowering}; Lean {leanLowering}")

/-- Parse one expected usage observation from Go. -/
def parseObservation (json : Lean.Json) : ParseM Observation := do
  pure
    { path := ← parsePath (← field json "path")
    , mode := ← parseMode (← stringField json "mode")
    }

/-- Combine a list of operations with the same sequence semantics as the
    production analyzer merge. -/
def analyzeOperations (operations : List TemplateOperation) : AnalysisResult :=
  operations.foldl
    (fun result operation => result.merge (analyzeOperation operation)) {}

/-- Compare two lists as finite sets. Duplicate entries and list order have no
    semantic effect. -/
def sameSet {α : Type} [BEq α] (left right : List α) : Bool :=
  left.all (List.contains right) && right.all (List.contains left)

/-- Compare normalized usage node and observation sets. -/
def sameUsage (left right : Usage) : Bool :=
  sameSet left.nodes right.nodes &&
    sameSet left.observations right.observations

mutual
  /-- Parse one named child from the recursive production usage tree. -/
  def parseRawUsageProperty : Nat → Lean.Json → ParseM (String × RawUsage)
    | 0, _ => throw "raw usage exceeds the nesting limit"
    | fuel + 1, json => do
        pure
          ( ← stringField json "name"
          , ← parseRawUsage fuel (← field json "usage")
          )

  /-- Parse the recursive production usage tree without deriving any schema
      decisions. -/
  def parseRawUsage : Nat → Lean.Json → ParseM RawUsage
    | 0, _ => throw "raw usage exceeds the nesting limit"
    | fuel + 1, json => do
        let parseChild (name : String) : ParseM (Option RawUsage) := do
          match ← field json name with
          | .null => pure none
          | child => pure (some (← parseRawUsage fuel child))
        let properties ← arrayOf (← field json "properties")
          (parseRawUsageProperty fuel)
        requireUniqueNames properties
        pure
          { isRead := ← boolField json "read"
          , isExact := ← boolField json "exact"
          , allowsUnknown := ← boolField json "allowUnknown"
          , isOpen := ← boolField json "open"
          , isIterated := ← boolField json "iterated"
          , properties := properties
          , additional := ← parseChild "additional"
          , items := ← parseChild "items"
          , elements := ← parseChild "elements"
          }
end

/-- Parse absent production usage as an empty tree. -/
def parseOptionalRawUsage (json : Lean.Json) : ParseM RawUsage :=
  match json with
  | .null => pure {}
  | value => parseRawUsage 1024 value

/-- Verify one named fixture and return an optional failure message. -/
def verifyCase (json : Lean.Json) : ParseM (Option String) := do
  let name ← stringField json "name"
  let operations ← arrayOf (← field json "operations") parseOperation
  let goUsage := (← parseOptionalRawUsage (← field json "usage")).summarize
  let leanUsage := (analyzeOperations operations).usage
  if sameUsage leanUsage goUsage then
    pure none
  else
    pure (some s!"{name}: Go usage {repr goUsage}; Lean usage {repr leanUsage}")

/-- Parse one dependency value copy. -/
def parseValueFlow (json : Lean.Json) : ParseM ValueFlow := do
  pure
    { source := ← arrayOf (← field json "source") Lean.Json.getStr?
    , destination := ← arrayOf (← field json "destination") Lean.Json.getStr?
    }

/-- Compare production and Lean value-flow propagation. -/
def verifyFlow (json : Lean.Json) : ParseM (Option String) := do
  let name ← stringField json "name"
  let before := (← parseOptionalRawUsage (← field json "before")).summarize
  let flows ← arrayOf (← field json "flows") parseValueFlow
  let goAfter := (← parseOptionalRawUsage (← field json "after")).summarize
  let leanAfter := applyValueFlows before flows
  if sameUsage leanAfter goAfter then
    pure none
  else
    pure (some s!"{name}: Go flow usage {repr goAfter}; Lean {repr leanAfter}")

/-- Parse one scalar JSON value from the semantic schema protocol. -/
def parseScalarValue (json : Lean.Json) : ParseM JValue := do
  match ← stringField json "kind" with
  | "null" => pure .null
  | "boolean" => pure (.bool (← boolField json "value"))
  | "integer" | "number" =>
      let number ← (← field json "value").getNum?
      pure (.number (.ofScientific number.mantissa number.exponent))
  | "string" => pure (.string (← stringField json "value"))
  | kind => throw s!"unsupported scalar value kind {kind}"

mutual
  /-- Parse one named property in a recursive JSON value. -/
  def parseJValueProperty : Nat → Lean.Json → ParseM (String × JValue)
    | 0, _ => throw "JSON value exceeds the nesting limit"
    | fuel + 1, json => do
        pure
          ( ← stringField json "name"
          , ← parseJValue fuel (← field json "value")
          )

  /-- Parse one recursive JSON value from the semantic protocol. -/
  def parseJValue : Nat → Lean.Json → ParseM JValue
    | 0, _ => throw "JSON value exceeds the nesting limit"
    | fuel + 1, json => do
        match ← stringField json "kind" with
        | "array" =>
            pure (.array (← arrayOf (← field json "items") (parseJValue fuel)))
        | "object" =>
            let properties ← arrayOf (← field json "properties")
              (parseJValueProperty fuel)
            requireUniqueNames properties
            pure (.object properties)
        | _ => parseScalarValue json
end

/-- Parse one object-boundary input shared by root and nested objects. -/
def parseBoundaryInput (json : Lean.Json) : ParseM BoundaryInput := do
  pure
    { defaultValues := ← arrayOf (← field json "defaults")
        (parseJValue 1024)
    , usage := ← parseOptionalRawUsage (← field json "usage")
    , inheritedOpen := ← boolField json "inheritedOpen"
    }

/-- Compare one production unknown-property decision with Lean. -/
def verifyBoundary (json : Lean.Json) : ParseM (Option String) := do
  let name ← stringField json "name"
  let defaults ← arrayOf (← field json "defaults") (parseJValue 1024)
  let rawUsage ← parseOptionalRawUsage (← field json "usage")
  let goAllows ← boolField json "goAllows"
  let leanAllows := allowsUnnamed
    { defaultValues := defaults, usage := rawUsage }
  if goAllows == leanAllows then
    pure none
  else
    pure (some s!"{name}: Go allows unnamed = {goAllows}; Lean = {leanAllows}")

/-- Parse one default for a supported scalar leaf. -/
def parseLeafDefault (json : Lean.Json) : ParseM LeafDefault := do
  match ← stringField json "kind" with
  | "missing" => pure .missing
  | "templateString" => pure (.templateString (← stringField json "value"))
  | "null" => pure (.present .null none)
  | "boolean" => pure (.present (← parseScalarValue json) (some .boolean))
  | "integer" => pure (.present (← parseScalarValue json) (some .integer))
  | "number" => pure (.present (← parseScalarValue json) (some .number))
  | "string" => pure (.present (← parseScalarValue json) (some .string))
  | kind => throw s!"unsupported leaf default kind {kind}"

mutual
  /-- Parse one named value input with a bounded nesting depth. -/
  def parseValueProperty : Nat → Lean.Json → ParseM (String × ValueInput)
    | 0, _ => throw "formal input exceeds the nesting limit"
    | fuel + 1, json => do
        pure
          ( ← stringField json "name"
          , ← parseValueInput fuel json
          )

  /-- Parse one recursive compiled value input. -/
  def parseValueInput : Nat → Lean.Json → ParseM ValueInput
    | 0, _ => throw "formal input exceeds the nesting limit"
    | fuel + 1, json => do
        match ← stringField json "kind" with
        | "unrestricted" => pure .unrestricted
        | "typed" =>
            let kind ← match ← stringField json "type" with
              | "null" => pure JsonType.null
              | "boolean" => pure .boolean
              | "integer" => pure .integer
              | "number" => pure .number
              | "string" => pure .string
              | "array" => pure .array
              | "object" => pure .object
              | name => throw s!"unsupported input type {name}"
            pure (.typed kind)
        | "leaf" =>
            pure (.leaf
              { defaultValue := ← parseLeafDefault (← field json "default")
              , directUsage := ← boolField json "directUsage"
              , inheritedOpen := ← boolField json "inheritedOpen"
              , explicitNull := ← boolField json "explicitNull"
              })
        | "fixed" =>
            pure (.fixed
              (← parseJValue fuel (← field json "fixed"))
              (← boolField json "explicitNull"))
        | "object" =>
            let properties ← arrayOf (← field json "properties")
              (parseValueProperty fuel)
            requireUniqueNames properties
            let additional ← match ← field json "additional" with
              | .null => pure none
              | value => pure (some (← parseValueInput fuel value))
            pure (.object
              properties
              additional
              (← parseBoundaryInput (← field json "boundary"))
              (← boolField json "explicitNull"))
        | "array" =>
            pure (.array (← parseValueInput fuel (← field json "items")))
        | "anyOf" =>
            pure (.anyOf (← arrayOf (← field json "alternatives")
              (parseValueInput fuel)))
        | "allOf" =>
            pure (.allOf (← arrayOf (← field json "constraints")
              (parseValueInput fuel)))
        | kind => throw s!"unsupported formal input kind {kind}"
end

/-- Parse one supported production policy input. -/
def parseCoreInput (json : Lean.Json) : ParseM CoreInput := do
  let properties ← arrayOf (← field json "properties")
    (parseValueProperty 1024)
  requireUniqueNames properties
  let additional ← match ← field json "additional" with
    | .null => pure none
    | value => pure (some (← parseValueInput 1024 value))
  pure
    { properties := properties
    , additional := additional
    , boundary := ← parseBoundaryInput (← field json "boundary")
    }

/-- Parse a JSON type from the semantic schema protocol. -/
def parseJsonType (name : String) : ParseM JsonType :=
  match name with
  | "null" => pure .null
  | "boolean" => pure .boolean
  | "integer" => pure .integer
  | "number" => pure .number
  | "string" => pure .string
  | "array" => pure .array
  | "object" => pure .object
  | _ => throw s!"unsupported JSON type {name}"

mutual
  /-- Parse one named property with a bounded schema nesting depth. -/
  def parseSchemaProperty : Nat → Lean.Json → ParseM (String × Schema)
    | 0, _ => throw "semantic schema exceeds the nesting limit"
    | fuel + 1, json => do
        pure
          ( ← stringField json "name"
          , ← parseSchema fuel (← field json "schema")
          )

  /-- Parse the semantic JSON Schema subset with a bounded nesting depth. -/
  def parseSchema : Nat → Lean.Json → ParseM Schema
    | 0, _ => throw "semantic schema exceeds the nesting limit"
    | fuel + 1, json => do
        match ← stringField json "kind" with
        | "any" => pure .any
        | "constant" =>
            pure (.constant (← parseJValue fuel (← field json "value")))
        | "typed" =>
            pure (.typed (← parseJsonType (← stringField json "type")))
        | "object" =>
            let properties ← arrayOf (← field json "properties")
              (parseSchemaProperty fuel)
            requireUniqueNames properties
            let additionalJSON ← field json "additional"
            let additional ← match additionalJSON with
              | .null => pure none
              | value => pure (some (← parseSchema fuel value))
            pure (.object properties additional)
        | "array" =>
            pure (.array (← parseSchema fuel (← field json "items")))
        | "anyOf" =>
            pure (.anyOf (← arrayOf (← field json "alternatives")
              (parseSchema fuel)))
        | "allOf" =>
            pure (.allOf (← arrayOf (← field json "constraints")
              (parseSchema fuel)))
        | kind => throw s!"unsupported semantic schema kind {kind}"
end

/-- Parse one semantic schema with the protocol nesting limit. -/
def parseSemanticSchema (json : Lean.Json) : ParseM Schema :=
  parseSchema 1024 json

/-- Compare one Go schema with the schema generated from the Lean core input. -/
def verifySchema (json : Lean.Json) : ParseM (Option String) := do
  let name ← stringField json "name"
  let input ← parseCoreInput (← field json "input")
  let goSchema ← parseSemanticSchema (← field json "goSchema")
  let leanSchema := generate (corePolicy input)
  if goSchema == leanSchema then
    pure none
  else
    pure (some s!"{name}: Go schema {repr goSchema}; Lean schema {repr leanSchema}")

/-- Compare the executable Lean validator with Helm 4 for one semantic schema
    and canonical JSON value. -/
def verifyValidation (json : Lean.Json) : ParseM (Option String) := do
  let name ← stringField json "name"
  let schema ← parseSemanticSchema (← field json "schema")
  let value ← parseJValue 1024 (← field json "value")
  let helmAccepts ← boolField json "helmAccepts"
  let leanAccepts := accepts schema value
  if leanAccepts == helmAccepts then
    pure none
  else
    pure (some s!"{name}: Helm accepts = {helmAccepts}; Lean = {leanAccepts}")

/-- Verify the complete protocol document. -/
def verifyDocument (json : Lean.Json) : ParseM (List String) := do
  let version ← (← field json "version").getNat?
  if version != 3 then
    throw s!"unsupported protocol version {version}"
  let cases ← arrayOf (← field json "cases") verifyCase
  let flows ← arrayOf (← field json "flows") verifyFlow
  let functionRows ← arrayOf (← field json "functions") verifyFunction
  requireUniqueLabels "function matrix row" functionRows
  let functions := functionRows.map Prod.snd
  let boundaries ← arrayOf (← field json "boundaries") verifyBoundary
  let schemas ← arrayOf (← field json "schemas") verifySchema
  let validations ← arrayOf (← field json "validations") verifyValidation
  pure ((cases ++ flows ++ functions ++ boundaries ++ schemas ++ validations).filterMap id)

end Verify

/-- Read a conformance document from standard input. Exit nonzero on malformed
    input or on a Go/Lean semantic difference. -/
def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Lean.Json.parse input >>= Verify.verifyDocument with
  | .error message =>
      IO.eprintln s!"formal conformance input error: {message}"
      pure 2
  | .ok [] => pure 0
  | .ok failures =>
      for failure in failures do
        IO.eprintln failure
      pure 1
