import HelmSchema.Core

set_option autoImplicit false

namespace HelmSchema

/-!
This file states the validation contract directly on the formal adapter input.
The adapter has already compiled each value shape and dynamic-entry contract.
These definitions do not call `valuePolicy`, `corePolicy`, or `generate`.
-/

/-- Direct acceptance for a leaf before an explicit raw null is added. A
    scalar type is required only when the raw usage supplies type evidence. -/
def LeafBasePermitted (input : LeafInput) (candidate : JValue) : Prop :=
  if !input.inheritedOpen || input.directUsage then
    match input.defaultValue with
    | .present _ inferredType =>
        match inferredType with
        | some kind => HasType candidate kind
        | none => True
    | .missing => True
    | .templateString _ => True
  else
    True

/-- Direct acceptance for one leaf, including Helm's explicit-null removal
    form. -/
def LeafPermitted (input : LeafInput) (candidate : JValue) : Prop :=
  (input.explicitNull = true ∧ JsonEquivalent .null candidate) ∨
    LeafBasePermitted input candidate

/-- Direct acceptance for an unused fixed default. -/
def FixedPermitted (expected : JValue) (explicitNull : Bool)
    (candidate : JValue) : Prop :=
  (explicitNull = true ∧ JsonEquivalent .null candidate) ∨
    JsonEquivalent expected candidate

mutual
/-- Direct acceptance for one recursive adapter value input. -/
  inductive ValueInputPermitted : ValueInput → JValue → Prop where
    | unrestricted (candidate : JValue) :
        ValueInputPermitted .unrestricted candidate
    | typed {kind : JsonType} {candidate : JValue}
        (typeProof : HasType candidate kind) :
        ValueInputPermitted (.typed kind) candidate
    | leaf {input : LeafInput} {candidate : JValue}
        (permitted : LeafPermitted input candidate) :
        ValueInputPermitted (.leaf input) candidate
    | fixed {expected candidate : JValue} {explicitNull : Bool}
        (permitted : FixedPermitted expected explicitNull candidate) :
        ValueInputPermitted (.fixed expected explicitNull) candidate
    | objectNull {properties : List (String × ValueInput)}
        {additional : Option ValueInput}
        {boundary : BoundaryInput} {explicitNull : Bool}
        {candidate : JValue}
        (nullable : explicitNull = true)
        (equal : JsonEquivalent .null candidate) :
        ValueInputPermitted
          (.object properties additional boundary explicitNull) candidate
    | object {properties : List (String × ValueInput)}
        {additional : Option ValueInput}
        {boundary : BoundaryInput} {explicitNull : Bool}
        {values : List (String × JValue)}
        (each : ∀ entry, entry ∈ values →
          ValuePropertyPermitted properties additional boundary
            entry.1 entry.2) :
        ValueInputPermitted
          (.object properties additional boundary explicitNull)
          (.object values)
    | array {items : ValueInput} {values : List JValue}
        (each : ∀ value, value ∈ values → ValueInputPermitted items value) :
        ValueInputPermitted (.array items) (.array values)
    | anyOf {alternatives : List ValueInput} {candidate : JValue}
        (alternative : ValueInput) (member : alternative ∈ alternatives)
        (permitted : ValueInputPermitted alternative candidate) :
        ValueInputPermitted (.anyOf alternatives) candidate
    | allOf {constraints : List ValueInput} {candidate : JValue}
        (each : ∀ constraint, constraint ∈ constraints →
          ValueInputPermitted constraint candidate) :
        ValueInputPermitted (.allOf constraints) candidate

/-- Direct acceptance for one property at an adapter object boundary. -/
  inductive ValuePropertyPermitted : List (String × ValueInput) →
      Option ValueInput → BoundaryInput → String → JValue → Prop where
    | known {properties : List (String × ValueInput)}
        {additional : Option ValueInput} {boundary : BoundaryInput}
        {name : String} {candidate : JValue}
        {input : ValueInput}
        (found : JObject.get? properties name = some input)
        (permitted : ValueInputPermitted input candidate) :
        ValuePropertyPermitted properties additional boundary name candidate
    | structured {properties : List (String × ValueInput)}
        {additional : Option ValueInput} {boundary : BoundaryInput}
        {name : String} {candidate : JValue} {contract : ValueInput}
        (unknown : JObject.get? properties name = none)
        (found : additional = some contract)
        (permitted : ValueInputPermitted contract candidate) :
        ValuePropertyPermitted properties additional boundary name candidate
    | unnamed {properties : List (String × ValueInput)}
        {additional : Option ValueInput} {boundary : BoundaryInput}
        {name : String} {candidate : JValue}
        (unknown : JObject.get? properties name = none)
        (unstructured : additional = none)
        (relevant : UnnamedPropertyRelevant boundary) :
        ValuePropertyPermitted properties additional boundary name candidate
end

/-- Direct acceptance for the root object. The root itself is never nullable. -/
inductive CoreInputPermitted : CoreInput → JValue → Prop where
  | object {input : CoreInput} {values : List (String × JValue)}
      (each : ∀ entry, entry ∈ values →
        ValuePropertyPermitted input.properties input.additional input.boundary
          entry.1 entry.2) :
      CoreInputPermitted input (.object values)

end HelmSchema
