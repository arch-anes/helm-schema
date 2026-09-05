import HelmSchema.Generate

set_option autoImplicit false

namespace HelmSchema.Proofs.Generator

open HelmSchema

/-- Every value permitted by a policy is accepted by its generated schema. -/
theorem permitted_sound {policy : Policy} {value : JValue}
    (permitted : Permitted policy value) : Accepts (generate policy) value := by
  cases policy with
  | unrestricted =>
      rw [generate.eq_def]
      exact Accepts.any value
  | constant expected =>
      rw [generate.eq_def]
      cases permitted with
      | constant equal => exact Accepts.constant equal
  | typed kind =>
      rw [generate.eq_def]
      cases permitted with
      | typed typeProof => exact Accepts.typed typeProof
  | object properties additional =>
      rw [generate.eq_def]
      cases permitted with
      | object each =>
          apply Accepts.object
          intro entry member
          have property := each entry member
          cases property with
          | known found child =>
              have sourceMember :=
                JObject.pair_mem_of_get?_eq_some properties entry.1 _ found
              apply PropertyAccepts.known
              · change JObject.get? (JObject.mapValues properties generate)
                    entry.1 = _
                rw [JObject.get?_mapValues, found]
                rfl
              · exact permitted_sound child
          | additional unknown contract child =>
              apply PropertyAccepts.additional
              · change JObject.get? (JObject.mapValues properties generate)
                    entry.1 = none
                rw [JObject.get?_mapValues, unknown]
                rfl
              · cases additional with
                | none => contradiction
                | some propertyPolicy =>
                    simp at contract
                    subst propertyPolicy
                    rfl
              · exact permitted_sound child
  | array itemPolicy =>
      rw [generate.eq_def]
      cases permitted with
      | array each =>
          have childSmaller : sizeOf itemPolicy < sizeOf itemPolicy.array := by
            rw [Policy.array.sizeOf_spec]
            omega
          apply Accepts.array
          intro item member
          exact permitted_sound (each item member)
  | anyOf alternatives =>
      rw [generate.eq_def]
      cases permitted with
      | anyOf alternative member child =>
          have childSmaller :
              sizeOf alternative < sizeOf (Policy.anyOf alternatives) := by
            rw [Policy.anyOf.sizeOf_spec]
            exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)
          apply Accepts.anyOf (generate alternative)
          · exact List.mem_map.mpr ⟨alternative, member, rfl⟩
          · exact permitted_sound child
  | allOf constraints =>
      rw [generate.eq_def]
      cases permitted with
      | allOf each =>
          apply Accepts.allOf
          intro generatedConstraint member
          obtain ⟨constraint, sourceMember, generated⟩ :=
            List.mem_map.mp member
          subst generatedConstraint
          exact permitted_sound (each constraint sourceMember)
termination_by sizeOf policy
decreasing_by
  all_goals subst_vars
  all_goals try assumption
  all_goals
    first
    | (rw [Policy.allOf.sizeOf_spec]
       exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega))
    | (rw [Policy.object.sizeOf_spec]
       have entrySize := List.sizeOf_lt_of_mem sourceMember
       rw [Prod.mk.sizeOf_spec] at entrySize
       omega)
    | (rw [Policy.object.sizeOf_spec, Option.some.sizeOf_spec]
       omega)
  all_goals simp_all [Policy.array.sizeOf_spec, Policy.anyOf.sizeOf_spec]
  all_goals
    first
    | exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega)
    | omega

/-- Every value accepted by a generated schema is permitted by its source
    policy. Together with `permitted_sound`, this states exact preservation. -/
theorem accepted_complete {policy : Policy} {value : JValue}
    (accepted : Accepts (generate policy) value) : Permitted policy value := by
  cases policy with
  | unrestricted =>
      rw [generate.eq_def] at accepted
      exact Permitted.unrestricted value
  | constant expected =>
      rw [generate.eq_def] at accepted
      cases accepted with
      | constant equal => exact Permitted.constant equal
  | typed kind =>
      rw [generate.eq_def] at accepted
      cases accepted with
      | typed typeProof => exact Permitted.typed typeProof
  | object properties additional =>
      rw [generate.eq_def] at accepted
      cases accepted with
      | object each =>
          apply Permitted.object
          intro entry member
          have property := each entry member
          cases property with
          | known found child =>
              change JObject.get? (JObject.mapValues properties generate)
                entry.1 = _ at found
              rw [JObject.get?_mapValues] at found
              cases lookup : JObject.get? properties entry.1 with
              | none => simp [lookup] at found
              | some propertyPolicy =>
                  simp [lookup] at found
                  subst_vars
                  have sourceMember :=
                    JObject.pair_mem_of_get?_eq_some properties entry.1 _ lookup
                  have childSmaller :
                      sizeOf propertyPolicy <
                        sizeOf (Policy.object properties additional) := by
                    rw [Policy.object.sizeOf_spec]
                    have entrySize := List.sizeOf_lt_of_mem sourceMember
                    rw [Prod.mk.sizeOf_spec] at entrySize
                    omega
                  exact PropertyPermitted.known lookup
                    (accepted_complete child)
          | additional unknown contract child =>
              change JObject.get? (JObject.mapValues properties generate)
                entry.1 = none at unknown
              rw [JObject.get?_mapValues] at unknown
              cases lookup : JObject.get? properties entry.1 with
              | some propertyPolicy => simp [lookup] at unknown
              | none =>
                  cases additional with
                  | none => simp at contract
                  | some propertyPolicy =>
                      simp at contract
                      subst_vars
                      have childSmaller :
                          sizeOf propertyPolicy < sizeOf
                            (Policy.object properties (some propertyPolicy)) := by
                        rw [Policy.object.sizeOf_spec,
                          Option.some.sizeOf_spec]
                        omega
                      exact PropertyPermitted.additional lookup rfl
                        (accepted_complete child)
  | array itemPolicy =>
      rw [generate.eq_def] at accepted
      cases accepted with
      | array each =>
          have childSmaller : sizeOf itemPolicy < sizeOf itemPolicy.array := by
            rw [Policy.array.sizeOf_spec]
            omega
          apply Permitted.array
          intro item member
          exact accepted_complete (each item member)
  | anyOf alternatives =>
      rw [generate.eq_def] at accepted
      cases accepted with
      | anyOf generatedAlternative member child =>
          obtain ⟨alternative, sourceMember, generated⟩ :=
            List.mem_map.mp member
          subst generatedAlternative
          have childSmaller :
              sizeOf alternative < sizeOf (Policy.anyOf alternatives) := by
            rw [Policy.anyOf.sizeOf_spec]
            exact Nat.lt_trans (List.sizeOf_lt_of_mem sourceMember) (by omega)
          exact Permitted.anyOf alternative sourceMember
            (accepted_complete child)
  | allOf constraints =>
      rw [generate.eq_def] at accepted
      cases accepted with
      | allOf each =>
          apply Permitted.allOf
          intro constraint member
          apply accepted_complete
          exact each (generate constraint) (List.mem_map.mpr ⟨constraint, member, rfl⟩)
termination_by sizeOf policy
decreasing_by
  all_goals subst_vars
  all_goals try assumption
  all_goals simp_all [Policy.allOf.sizeOf_spec]
  all_goals
    first
    | exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega)
    | omega

/-- Schema generation implements exactly the declarative policy relation. -/
theorem generate_correct (policy : Policy) (value : JValue) :
    Accepts (generate policy) value ↔ Permitted policy value :=
  ⟨accepted_complete, permitted_sound⟩

/-- A closed generated object rejects every property that is not named. -/
theorem closed_object_rejects_unknown
    (properties : List (String × Policy)) (name : String) (value : JValue)
    (unknown : JObject.get? properties name = none) :
    ¬Accepts (generate (.object properties none)) (.object [(name, value)]) := by
  intro accepted
  have permitted := accepted_complete accepted
  cases permitted with
  | object each =>
      have property := each (name, value) (by simp)
      cases property with
      | known found child => rw [unknown] at found; contradiction
      | additional unknown contract child => contradiction

/-- An unrestricted additional-property policy accepts every unknown value. -/
theorem unrestricted_additional_accepts
    (properties : List (String × Policy)) (name : String) (value : JValue)
    (unknown : JObject.get? properties name = none) :
    Accepts (generate (.object properties (some .unrestricted)))
      (.object [(name, value)]) := by
  apply permitted_sound
  apply Permitted.object
  intro entry member
  simp only [List.mem_singleton] at member
  subst entry
  exact PropertyPermitted.additional unknown rfl
    (Permitted.unrestricted value)

end HelmSchema.Proofs.Generator
