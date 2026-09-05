import HelmSchema.Boundary

set_option autoImplicit false

namespace HelmSchema

/-- One leaf default form supported by the formal adapter. Container defaults
    use `ValueInput.fixed` or `ValueInput.object`. `inferredType` preserves the
    source distinction between integer and number defaults. -/
inductive LeafDefault where
  | missing
  | present (value : JValue) (inferredType : Option JsonType)
  | templateString (value : String)
  deriving BEq, Repr

/-- One non-container property with the raw evidence that controls scalar type
    inference. Direct usage preserves type evidence. Inherited complete use
    without direct usage does not. -/
structure LeafInput where
  defaultValue : LeafDefault
  directUsage : Bool
  inheritedOpen : Bool
  explicitNull : Bool := false
  deriving BEq, Repr

/-- Add a null alternative to a direct policy unless it is already a null
    constant or type. Callers supply only base leaf or fixed-value policies. -/
def permitDirectNull : Policy → Policy
  | policy@(.constant .null) => policy
  | policy@(.typed .null) => policy
  | policy => .anyOf [.constant .null, policy]

/-- Convert one used scalar or missing property into its base semantic policy.
    Fixed values use `ValueInput.fixed` instead. -/
def baseLeafPolicy (input : LeafInput) : Policy :=
  if !input.inheritedOpen || input.directUsage then
    match input.defaultValue with
    | .missing => .unrestricted
    | .present _ inferredType =>
        match inferredType with
        | some kind => .typed kind
        | none => .unrestricted
    | .templateString _ => .unrestricted
  else
    .unrestricted

/-- Convert one scalar or missing property into its final semantic policy.
    An explicit raw null default adds null after ordinary inference, matching
    the production generator's post-processing order. -/
def leafPolicy (input : LeafInput) : Policy :=
  let base := baseLeafPolicy input
  if input.explicitNull then permitDirectNull base else base

/-- One recursively nested value in the supported production input. -/
inductive ValueInput where
  | unrestricted
  | typed (kind : JsonType)
  | leaf (input : LeafInput)
  | fixed (value : JValue) (explicitNull : Bool)
  | object (properties : List (String × ValueInput))
      (additional : Option ValueInput) (boundary : BoundaryInput)
      (explicitNull : Bool)
  | array (items : ValueInput)
  | anyOf (alternatives : List ValueInput)
  | allOf (constraints : List ValueInput)
  deriving BEq, Repr

/-- Convert an explicit dynamic-entry contract or an ordinary boundary
    decision into the policy for unnamed object properties. -/
def additionalPolicy (additional : Option Policy)
    (boundary : BoundaryInput) : Option Policy :=
  match additional with
  | some contract => some contract
  | none => if allowsUnnamed boundary then some .unrestricted else none

/-- Convert one recursive value input into the intermediate policy language. -/
def valuePolicy : ValueInput → Policy
  | .unrestricted => .unrestricted
  | .typed kind => .typed kind
  | .leaf input => leafPolicy input
  | .fixed value explicitNull =>
      let base := Policy.constant value
      if explicitNull then permitDirectNull base else base
  | .object properties additional boundary explicitNull =>
      let unnamed := match additional with
        | none => additionalPolicy none boundary
        | some contract => some (valuePolicy contract)
      let base := Policy.object
        (properties.map fun entry => (entry.1, valuePolicy entry.2))
        unnamed
      if explicitNull then .anyOf [.constant .null, base] else base
  | .array items => .array (valuePolicy items)
  | .anyOf alternatives => .anyOf (alternatives.map valuePolicy)
  | .allOf constraints => .allOf (constraints.map valuePolicy)
termination_by input => sizeOf input
decreasing_by
  · simp_wf
    omega
  · simp_wf
    rename_i _rec member
    cases entry with
    | mk name child =>
        have entrySize := List.sizeOf_lt_of_mem member
        rw [Prod.mk.sizeOf_spec] at entrySize
        change sizeOf child < _
        omega
  · simp_wf
  · simp_wf
    exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega)
  · simp_wf
    exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega)

/-- Resolve an optional structured dynamic-entry input after recursive policy
    compilation. This is the object rule used by contracts and root inputs. -/
def valueAdditionalPolicy (additional : Option ValueInput)
    (boundary : BoundaryInput) : Option Policy :=
  match additional with
  | none => additionalPolicy none boundary
  | some contract => some (valuePolicy contract)

/-- Convert one object without an outer null alternative into its policy. -/
def objectPolicy (properties : List (String × ValueInput))
    (boundary : BoundaryInput) : Policy :=
  .object (JObject.mapValues properties valuePolicy)
    (additionalPolicy none boundary)

/-- Convert one object with a typed dynamic-entry contract into its policy. -/
def structuredObjectPolicy (properties : List (String × ValueInput))
    (additional : ValueInput) (boundary : BoundaryInput := {}) : Policy :=
  .object (JObject.mapValues properties valuePolicy)
    (additionalPolicy (some (valuePolicy additional)) boundary)

/-- The formal adapter input contains compiled scalar, object, array,
    alternative, conjunction, and structured dynamic-entry contracts. -/
structure CoreInput where
  properties : List (String × ValueInput) := []
  additional : Option ValueInput := none
  boundary : BoundaryInput := {}
  deriving BEq, Repr

/-- Convert the supported adapter input into the intermediate policy language. -/
def corePolicy (input : CoreInput) : Policy :=
  .object (JObject.mapValues input.properties valuePolicy)
    (valueAdditionalPolicy input.additional input.boundary)

end HelmSchema
