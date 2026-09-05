import HelmSchema.Generate
import HelmSchema.Usage

set_option autoImplicit false

namespace HelmSchema

/-- The evidence that controls unnamed properties at one object boundary.
    `structural` reports a fixed property, additional-property, item, or
    element node below the boundary. -/
structure BoundaryUsage where
  isRead : Bool := false
  allowsUnknown : Bool := false
  isOpen : Bool := false
  isIterated : Bool := false
  hasStructure : Bool := false
  hasAdditional : Bool := false
  hasElements : Bool := false
  deriving BEq, DecidableEq, Repr

/-- Derive exactly the boundary flags used by schema generation from a raw
    usage node. Present empty children count as structural evidence. -/
def RawUsage.toBoundaryUsage (usage : RawUsage) : BoundaryUsage :=
  { isRead := usage.isRead
  , allowsUnknown := usage.allowsUnknown
  , isOpen := usage.isOpen
  , isIterated := usage.isIterated
  , hasStructure := !usage.properties.isEmpty || usage.additional.isSome ||
      usage.items.isSome || usage.elements.isSome
  , hasAdditional := usage.additional.isSome
  , hasElements := usage.elements.isSome
  }

/-- The raw inputs used by the production unknown-property decision.
    `inheritedOpen` records complete use inherited from an ancestor object. -/
structure BoundaryInput where
  defaultValues : List JValue := []
  usage : RawUsage := {}
  inheritedOpen : Bool := false
  deriving BEq, Repr

/-- Derive the complete evidence used by the boundary decision. -/
def BoundaryInput.evidence (input : BoundaryInput) : BoundaryUsage :=
  let usage := input.usage.toBoundaryUsage
  { usage with isOpen := input.inheritedOpen || usage.isOpen }

/-- Helm removes direct null map members. The effective object is empty when
    no direct default has a non-null value. -/
def defaultObjectIsEmpty (defaults : List JValue) : Bool :=
  defaults.all fun value =>
    match value with
    | .null => true
    | _ => false

/-- Independent statement that Helm removes every direct default member. -/
def AllDefaultsNull (defaults : List JValue) : Prop :=
  ∀ value, value ∈ defaults → value = .null

/-- Decide whether one object boundary accepts a property without a fixed
    template reference. This function matches `allowsUnnamedProperties` in Go. -/
def allowsUnnamed (input : BoundaryInput) : Bool :=
  input.evidence.isOpen || input.evidence.allowsUnknown ||
    input.evidence.isIterated || input.evidence.hasAdditional ||
    input.evidence.hasElements ||
    (input.evidence.isRead && !input.evidence.hasStructure &&
      defaultObjectIsEmpty input.defaultValues)

/-- Raw reasons for accepting a property name that does not occur in the
    default object or in fixed template selections. This relation is an
    independent statement of the boundary policy. It does not call
    `allowsUnnamed` or use its derived `BoundaryUsage` value. -/
inductive UnnamedPropertyRelevant : BoundaryInput → Prop where
  | inheritedOpen {input : BoundaryInput}
      (openUse : input.inheritedOpen = true) :
      UnnamedPropertyRelevant input
  | completeUse {input : BoundaryInput}
      (openUse : input.usage.isOpen = true) :
      UnnamedPropertyRelevant input
  | unknownContext {input : BoundaryInput}
      (contextUse : input.usage.allowsUnknown = true) :
      UnnamedPropertyRelevant input
  | iteration {input : BoundaryInput}
      (iterationUse : input.usage.isIterated = true) :
      UnnamedPropertyRelevant input
  | dynamicEntry {input : BoundaryInput} {child : RawUsage}
      (present : input.usage.additional = some child) :
      UnnamedPropertyRelevant input
  | shapeNeutralElement {input : BoundaryInput} {child : RawUsage}
      (present : input.usage.elements = some child) :
      UnnamedPropertyRelevant input
  | emptyTruthTest {input : BoundaryInput}
      (read : input.usage.isRead = true)
      (noProperties : input.usage.properties = [])
      (noAdditional : input.usage.additional = none)
      (noItems : input.usage.items = none)
      (noElements : input.usage.elements = none)
      (emptyDefaults : AllDefaultsNull input.defaultValues) :
      UnnamedPropertyRelevant input

/-- Add the boundary decision to an otherwise fixed object policy. -/
def boundaryPolicy (properties : List (String × Policy))
    (input : BoundaryInput) : Policy :=
  .object properties (if allowsUnnamed input then some .unrestricted else none)

end HelmSchema
