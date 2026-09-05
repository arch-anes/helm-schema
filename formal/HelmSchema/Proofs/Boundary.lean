import HelmSchema.Boundary
import HelmSchema.Proofs.Generator

set_option autoImplicit false

namespace HelmSchema.Proofs.Boundary

open HelmSchema

/-- The executable Helm-null check is true exactly when every direct default
    is JSON null. -/
@[simp]
theorem defaultObjectIsEmpty_iff_allDefaultsNull (defaults : List JValue) :
    defaultObjectIsEmpty defaults = true ↔ AllDefaultsNull defaults := by
  unfold defaultObjectIsEmpty AllDefaultsNull
  simp only [List.all_eq_true]
  constructor
  · intro allNull value member
    have check := allNull value member
    cases value <;> simp_all
  · intro allNull value member
    have equal := allNull value member
    subst value
    rfl

/-- Complete use always permits unnamed direct properties. -/
theorem open_allows (input : BoundaryInput) (openUse : input.evidence.isOpen = true) :
    allowsUnnamed input = true := by
  simp [allowsUnnamed, openUse]

/-- A dynamic additional-property selector always permits unnamed properties. -/
theorem dynamic_allows (input : BoundaryInput)
    (dynamic : input.evidence.hasAdditional = true) :
    allowsUnnamed input = true := by
  simp [allowsUnnamed, dynamic]

/-- Complete use inherited from an ancestor opens this object boundary. -/
theorem inherited_open_allows (input : BoundaryInput) :
    allowsUnnamed { input with inheritedOpen := true } = true := by
  simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage]

/-- A present additional-property child opens the boundary even when that
    child contains no flags. -/
theorem raw_additional_allows (input : BoundaryInput) (child : RawUsage) :
    allowsUnnamed
      { input with usage := { input.usage with additional := some child } } =
        true := by
  simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage]

/-- A present shape-neutral element child opens the object interpretation of
    the boundary even when that child contains no flags. -/
theorem raw_elements_allows (input : BoundaryInput) (child : RawUsage) :
    allowsUnnamed
      { input with usage := { input.usage with elements := some child } } =
        true := by
  simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage]

/-- The executable boundary decision is true exactly when one independent raw
    relevance reason applies. -/
theorem allowsUnnamed_iff_relevant (input : BoundaryInput) :
    allowsUnnamed input = true ↔ UnnamedPropertyRelevant input := by
  constructor
  · intro allowed
    by_cases inheritedOpen : input.inheritedOpen = true
    · exact UnnamedPropertyRelevant.inheritedOpen inheritedOpen
    by_cases completeUse : input.usage.isOpen = true
    · exact UnnamedPropertyRelevant.completeUse completeUse
    by_cases unknownContext : input.usage.allowsUnknown = true
    · exact UnnamedPropertyRelevant.unknownContext unknownContext
    by_cases iteration : input.usage.isIterated = true
    · exact UnnamedPropertyRelevant.iteration iteration
    cases additional : input.usage.additional with
    | some child =>
        exact UnnamedPropertyRelevant.dynamicEntry additional
    | none =>
        cases elements : input.usage.elements with
        | some child =>
            exact UnnamedPropertyRelevant.shapeNeutralElement elements
        | none =>
            cases properties : input.usage.properties with
            | cons head tail =>
                simp_all [allowsUnnamed, BoundaryInput.evidence,
                  RawUsage.toBoundaryUsage]
            | nil =>
                cases items : input.usage.items with
                | some child =>
                    simp_all [allowsUnnamed, BoundaryInput.evidence,
                      RawUsage.toBoundaryUsage]
                | none =>
                    apply UnnamedPropertyRelevant.emptyTruthTest
                    all_goals
                      simp_all [allowsUnnamed, BoundaryInput.evidence,
                        RawUsage.toBoundaryUsage]
  · intro relevant
    cases relevant with
    | inheritedOpen openUse =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          openUse]
    | completeUse openUse =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          openUse]
    | unknownContext contextUse =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          contextUse]
    | iteration iterationUse =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          iterationUse]
    | dynamicEntry present =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          present]
    | shapeNeutralElement present =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          present]
    | emptyTruthTest read noProperties noAdditional noItems noElements empty =>
        simp [allowsUnnamed, BoundaryInput.evidence, RawUsage.toBoundaryUsage,
          read, noProperties, noAdditional, noItems, noElements,
          defaultObjectIsEmpty_iff_allDefaultsNull, empty]

/-- A read without a field contract permits names when Helm removes every
    direct default member. -/
theorem empty_truth_test_allows (input : BoundaryInput)
    (read : input.evidence.isRead = true)
    (notStructural : input.evidence.hasStructure = false)
    (empty : defaultObjectIsEmpty input.defaultValues = true) :
    allowsUnnamed input = true := by
  simp [allowsUnnamed, read, notStructural, empty]

/-- A read with a field contract does not open a boundary by itself. -/
theorem structural_truth_test_stays_closed (input : BoundaryInput)
    (read : input.evidence.isRead = true)
    (structural : input.evidence.hasStructure = true)
    (notOpen : input.evidence.isOpen = false)
    (notContext : input.evidence.allowsUnknown = false)
    (notIterated : input.evidence.isIterated = false)
    (notAdditional : input.evidence.hasAdditional = false)
    (notElements : input.evidence.hasElements = false) :
    allowsUnnamed input = false := by
  simp [allowsUnnamed, read, structural, notOpen, notContext, notIterated,
    notAdditional, notElements]

/-- The generated boundary policy rejects an unknown property exactly when
    the boundary decision is false. -/
theorem closed_boundary_rejects_unknown
    (properties : List (String × Policy)) (input : BoundaryInput)
    (name : String) (value : JValue)
    (unknown : JObject.get? properties name = none)
    (closed : allowsUnnamed input = false) :
    ¬Accepts (generate (boundaryPolicy properties input))
      (.object [(name, value)]) := by
  simp only [boundaryPolicy, closed, Bool.false_eq_true, ↓reduceIte]
  exact Generator.closed_object_rejects_unknown properties name value unknown

/-- The generated boundary policy accepts every unknown value exactly when
    the boundary decision is true. -/
theorem open_boundary_accepts_unknown
    (properties : List (String × Policy)) (input : BoundaryInput)
    (name : String) (value : JValue)
    (unknown : JObject.get? properties name = none)
    (openBoundary : allowsUnnamed input = true) :
    Accepts (generate (boundaryPolicy properties input))
      (.object [(name, value)]) := by
  simp only [boundaryPolicy, openBoundary, ↓reduceIte]
  exact Generator.unrestricted_additional_accepts properties name value unknown

/-- For one unknown property, generated acceptance is equivalent to the
    production boundary decision. -/
theorem boundary_policy_correct
    (properties : List (String × Policy)) (input : BoundaryInput)
    (name : String) (value : JValue)
    (unknown : JObject.get? properties name = none) :
    Accepts (generate (boundaryPolicy properties input))
      (.object [(name, value)]) ↔ allowsUnnamed input = true := by
  constructor
  · intro accepted
    cases decision : allowsUnnamed input with
    | false =>
        have rejected := closed_boundary_rejects_unknown properties input name
          value unknown decision
        exact (rejected accepted).elim
    | true => rfl
  · intro openBoundary
    exact open_boundary_accepts_unknown properties input name value unknown
      openBoundary

/-- For one unknown property, generated acceptance is equivalent to the raw
    semantic reasons for making that property relevant. -/
theorem boundary_policy_contract
    (properties : List (String × Policy)) (input : BoundaryInput)
    (name : String) (value : JValue)
    (unknown : JObject.get? properties name = none) :
    Accepts (generate (boundaryPolicy properties input))
      (.object [(name, value)]) ↔ UnnamedPropertyRelevant input := by
  exact (boundary_policy_correct properties input name value unknown).trans
    (allowsUnnamed_iff_relevant input)

end HelmSchema.Proofs.Boundary
