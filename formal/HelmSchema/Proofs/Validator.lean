import HelmSchema.Schema

set_option autoImplicit false

namespace HelmSchema.Proofs.Validator

open HelmSchema

/-- If child validation is sound at one fuel level, property validation is
    sound at that level. -/
theorem property_sound {fuel : Nat} {properties : List (String × Schema)}
    {additional : Option Schema} {entry : String × JValue}
    (childSound : ∀ {schema : Schema} {value : JValue},
      acceptsFuel fuel schema value = true → Accepts schema value)
    (accepted : acceptsPropertyFuel fuel properties additional entry = true) :
    PropertyAccepts properties additional entry.1 entry.2 := by
  unfold acceptsPropertyFuel at accepted
  split at accepted
  next propertySchema found =>
    exact PropertyAccepts.known found (childSound accepted)
  next unknown =>
    split at accepted
    next propertySchema =>
      exact PropertyAccepts.additional unknown rfl (childSound accepted)
    next => simp at accepted

/-- A true Boolean result always has a declarative acceptance derivation. -/
theorem acceptsFuel_sound {fuel : Nat} {schema : Schema} {value : JValue}
    (accepted : acceptsFuel fuel schema value = true) :
    Accepts schema value := by
  induction fuel generalizing schema value with
  | zero => simp [acceptsFuel] at accepted
  | succ fuel induction =>
      cases schema with
      | any => exact Accepts.any value
      | constant expected =>
          apply Accepts.constant
          apply (jsonEqual_correct expected value).1
          simpa [acceptsFuel] using accepted
      | typed kind =>
          exact Accepts.typed (hasType_correct value kind |>.1 (by
            simpa [acceptsFuel] using accepted))
      | object properties additional =>
          cases value with
          | object values =>
              apply Accepts.object
              intro entry member
              have entryAccepted :
                  acceptsPropertyFuel fuel properties additional entry = true :=
                (List.all_eq_true.mp (by simpa [acceptsFuel] using accepted))
                  entry member
              exact property_sound induction entryAccepted
          | null => simp [acceptsFuel] at accepted
          | bool value => simp [acceptsFuel] at accepted
          | number value => simp [acceptsFuel] at accepted
          | string value => simp [acceptsFuel] at accepted
          | array items => simp [acceptsFuel] at accepted
      | array itemSchema =>
          cases value with
          | array items =>
              apply Accepts.array
              intro item member
              have itemAccepted : acceptsFuel fuel itemSchema item = true :=
                (List.all_eq_true.mp (by simpa [acceptsFuel] using accepted))
                  item member
              exact induction itemAccepted
          | null => simp [acceptsFuel] at accepted
          | bool value => simp [acceptsFuel] at accepted
          | number value => simp [acceptsFuel] at accepted
          | string value => simp [acceptsFuel] at accepted
          | object properties => simp [acceptsFuel] at accepted
      | anyOf alternatives =>
          have found : ∃ alternative,
              alternative ∈ alternatives ∧
                acceptsFuel fuel alternative value = true := by
            simpa [acceptsFuel] using accepted
          rcases found with ⟨alternative, member, alternativeAccepted⟩
          exact Accepts.anyOf alternative member (induction alternativeAccepted)
      | allOf constraints =>
          apply Accepts.allOf
          intro constraint member
          have constraintAccepted : acceptsFuel fuel constraint value = true :=
            (List.all_eq_true.mp (by simpa [acceptsFuel] using accepted))
              constraint member
          exact induction constraintAccepted

/-- One mapped natural number is no greater than the sum of all mapped
    numbers when its source value is in the list. -/
theorem mapped_value_le_sum {α : Type} (function : α → Nat)
    {value : α} {values : List α} (member : value ∈ values) :
    function value ≤ (values.map function).sum := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      simp only [List.map_cons, List.sum_cons]
      cases member with
      | inl equal => subst head; omega
      | inr tailMember =>
          have bound := induction tailMember
          omega

/-- A named child schema contributes no more than the object-property budget. -/
theorem property_budget_le_sum {properties : List (String × Schema)}
    {name : String} {propertySchema : Schema}
    (member : (name, propertySchema) ∈ properties) :
    schemaBudget propertySchema ≤
      (properties.map fun entry => schemaBudget entry.2).sum := by
  have bound := mapped_value_le_sum
    (fun entry : String × Schema => schemaBudget entry.2) member
  exact bound

/-- Declarative acceptance succeeds for every budget larger than the schema.
    This is the completeness direction for the executable validator. -/
theorem acceptsFuel_complete {schema : Schema} {value : JValue}
    (accepted : Accepts schema value) (fuel : Nat)
    (enough : schemaBudget schema < fuel) :
    acceptsFuel fuel schema value = true := by
  cases schema with
  | any =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [acceptsFuel]
  | constant expected =>
      cases accepted with
      | constant equal =>
          cases fuel with
          | zero => omega
          | succ fuel =>
              simpa [acceptsFuel] using
                (jsonEqual_correct expected value).2 equal
  | typed kind =>
      cases accepted with
      | typed typeProof =>
          cases fuel with
          | zero => omega
          | succ fuel =>
              simpa [acceptsFuel] using (hasType_correct value kind).2 typeProof
  | object properties additional =>
      cases accepted with
      | object each =>
          cases fuel with
          | zero => omega
          | succ childFuel =>
              simp only [acceptsFuel, List.all_eq_true]
              intro entry member
              have property := each entry member
              unfold acceptsPropertyFuel
              cases property with
              | known found child =>
                  have sourceMember :=
                    JObject.pair_mem_of_get?_eq_some properties entry.1 _ found
                  rw [found]
                  apply acceptsFuel_complete child
                  have childBound := property_budget_le_sum sourceMember
                  cases additional <;>
                    simp only [schemaBudget.eq_4, schemaBudget.eq_5] at enough <;>
                    omega
              | additional unknown contract child =>
                  rw [unknown, contract]
                  apply acceptsFuel_complete child
                  rw [contract, schemaBudget.eq_5] at enough
                  omega
  | array itemSchema =>
      cases accepted with
      | array each =>
          have childSmaller :
              sizeOf itemSchema < sizeOf itemSchema.array := by
            rw [Schema.array.sizeOf_spec]
            omega
          cases fuel with
          | zero => omega
          | succ childFuel =>
              simp only [acceptsFuel, List.all_eq_true]
              intro item member
              apply acceptsFuel_complete (each item member)
              rw [schemaBudget.eq_6] at enough
              omega
  | anyOf alternatives =>
      cases accepted with
      | anyOf alternative member child =>
          have childSmaller :
              sizeOf alternative < sizeOf (Schema.anyOf alternatives) := by
            rw [Schema.anyOf.sizeOf_spec]
            exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)
          cases fuel with
          | zero => omega
          | succ childFuel =>
              simp only [acceptsFuel, List.any_eq_true]
              refine ⟨alternative, member, ?_⟩
              apply acceptsFuel_complete child
              rw [schemaBudget.eq_7] at enough
              have childBound := mapped_value_le_sum schemaBudget member
              omega
  | allOf constraints =>
      cases accepted with
      | allOf each =>
          cases fuel with
          | zero => omega
          | succ childFuel =>
              simp only [acceptsFuel, List.all_eq_true]
              intro constraint member
              apply acceptsFuel_complete (each constraint member)
              rw [schemaBudget.eq_8] at enough
              have childBound := mapped_value_le_sum schemaBudget member
              omega
termination_by sizeOf schema
decreasing_by
  all_goals subst_vars
  all_goals try assumption
  all_goals
    first
    | (rw [Schema.object.sizeOf_spec]
       have entrySize := List.sizeOf_lt_of_mem (by assumption)
       rw [Prod.mk.sizeOf_spec] at entrySize
       omega)
    | (rw [Schema.object.sizeOf_spec, Option.some.sizeOf_spec]
       omega)
    | (rw [Schema.array.sizeOf_spec]
       omega)
    | (rw [Schema.anyOf.sizeOf_spec]
       exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega))
    | (rw [Schema.allOf.sizeOf_spec]
       exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega))

/-- The executable validator and the independent declarative relation agree. -/
theorem accepts_correct (schema : Schema) (value : JValue) :
    accepts schema value = true ↔ Accepts schema value := by
  constructor
  · exact acceptsFuel_sound
  · intro accepted
    apply acceptsFuel_complete accepted
    omega

end HelmSchema.Proofs.Validator
