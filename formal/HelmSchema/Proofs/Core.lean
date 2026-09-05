import HelmSchema.Contract
import HelmSchema.Proofs.Generator
import HelmSchema.Proofs.Boundary

set_option autoImplicit false

namespace HelmSchema.Proofs.Core

open HelmSchema

/-- The unrestricted intermediate policy has no candidate restriction. -/
@[simp]
theorem permitted_unrestricted_iff (value : JValue) :
    Permitted .unrestricted value ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact Permitted.unrestricted value

/-- A constant intermediate policy has the independent JSON equality
    meaning. -/
@[simp]
theorem permitted_constant_iff (expected actual : JValue) :
    Permitted (.constant expected) actual ↔
      JsonEquivalent expected actual := by
  constructor
  · intro permitted
    cases permitted with
    | constant equal => exact equal
  · exact Permitted.constant

/-- A typed intermediate policy has the independent JSON type meaning. -/
@[simp]
theorem permitted_typed_iff (kind : JsonType) (value : JValue) :
    Permitted (.typed kind) value ↔ HasType value kind := by
  constructor
  · intro permitted
    cases permitted with
    | typed typeProof => exact typeProof
  · exact Permitted.typed

/-- The standard null alternative permits null independently of its other
    branch. -/
theorem null_alternative_permits (policy : Policy) :
    Permitted (.anyOf [.constant .null, policy]) .null :=
  Permitted.anyOf (.constant .null) (by simp)
    (Permitted.constant (by
      simp [JsonEquivalent, jsonEquivalentFuel, valueBudget]))

/-- The standard two-branch null alternative accepts exactly null or a value
    accepted by its other branch. -/
theorem null_alternative_iff (policy : Policy) (value : JValue) :
    Permitted (.anyOf [.constant .null, policy]) value ↔
      JsonEquivalent .null value ∨ Permitted policy value := by
  constructor
  · intro permitted
    cases permitted with
    | anyOf alternative member child =>
        simp at member
        rcases member with equal | equal
        · subst alternative
          cases child with
          | constant semanticEqual => exact Or.inl semanticEqual
        · subst alternative
          exact Or.inr child
  · intro permitted
    rcases permitted with equal | child
    · exact Permitted.anyOf (.constant .null) (by simp)
        (Permitted.constant equal)
    · exact Permitted.anyOf policy (by simp) child

/-- Adding direct-null support changes a policy only by accepting JSON null. -/
theorem permitDirectNull_iff (policy : Policy) (value : JValue) :
    Permitted (permitDirectNull policy) value ↔
      JsonEquivalent .null value ∨ Permitted policy value := by
  cases policy with
  | constant expected =>
      cases expected with
      | null =>
          constructor
          · exact Or.inr
          · intro permitted
            rcases permitted with equal | child
            · exact Permitted.constant equal
            · exact child
      | bool value => exact null_alternative_iff _ _
      | number value => exact null_alternative_iff _ _
      | string value => exact null_alternative_iff _ _
      | array items => exact null_alternative_iff _ _
      | object properties => exact null_alternative_iff _ _
  | typed kind =>
      cases kind with
      | null =>
          constructor
          · exact Or.inr
          · intro permitted
            rcases permitted with equal | child
            · have actual : value = .null := (jsonEquivalent_null_iff value).1 equal
              subst value
              exact Permitted.typed trivial
            · exact child
      | boolean => exact null_alternative_iff _ _
      | integer => exact null_alternative_iff _ _
      | number => exact null_alternative_iff _ _
      | string => exact null_alternative_iff _ _
      | array => exact null_alternative_iff _ _
      | object => exact null_alternative_iff _ _
  | unrestricted => exact null_alternative_iff _ _
  | object properties additional => exact null_alternative_iff _ _
  | array items => exact null_alternative_iff _ _
  | anyOf alternatives => exact null_alternative_iff _ _
  | allOf constraints => exact null_alternative_iff _ _

/-- Adding explicit-null support to a base leaf policy always permits null. -/
theorem permitDirectNull_permits_null (policy : Policy) :
    Permitted (permitDirectNull policy) .null := by
  cases policy with
  | constant value =>
      cases value with
      | null => exact Permitted.constant (by
          simp [JsonEquivalent, jsonEquivalentFuel, valueBudget])
      | bool value => exact null_alternative_permits _
      | number value => exact null_alternative_permits _
      | string value => exact null_alternative_permits _
      | array items => exact null_alternative_permits _
      | object properties => exact null_alternative_permits _
  | typed kind =>
      cases kind with
      | null => exact Permitted.typed trivial
      | boolean => exact null_alternative_permits _
      | integer => exact null_alternative_permits _
      | number => exact null_alternative_permits _
      | string => exact null_alternative_permits _
      | array => exact null_alternative_permits _
      | object => exact null_alternative_permits _
  | unrestricted => exact null_alternative_permits _
  | object properties additional => exact null_alternative_permits _
  | array items => exact null_alternative_permits _
  | anyOf alternatives => exact null_alternative_permits _
  | allOf constraints => exact null_alternative_permits _

/-- Adding explicit-null support preserves every value already permitted by
    the original policy. -/
theorem permitDirectNull_preserves {policy : Policy} {value : JValue}
    (permitted : Permitted policy value) :
    Permitted (permitDirectNull policy) value := by
  cases policy with
  | constant expected =>
      cases expected with
      | null => exact permitted
      | bool value => exact Permitted.anyOf _ (by simp) permitted
      | number value => exact Permitted.anyOf _ (by simp) permitted
      | string value => exact Permitted.anyOf _ (by simp) permitted
      | array items => exact Permitted.anyOf _ (by simp) permitted
      | object properties => exact Permitted.anyOf _ (by simp) permitted
  | typed kind =>
      cases kind with
      | null => exact permitted
      | boolean => exact Permitted.anyOf _ (by simp) permitted
      | integer => exact Permitted.anyOf _ (by simp) permitted
      | number => exact Permitted.anyOf _ (by simp) permitted
      | string => exact Permitted.anyOf _ (by simp) permitted
      | array => exact Permitted.anyOf _ (by simp) permitted
      | object => exact Permitted.anyOf _ (by simp) permitted
  | unrestricted => exact Permitted.anyOf _ (by simp) permitted
  | object properties additional => exact Permitted.anyOf _ (by simp) permitted
  | array items => exact Permitted.anyOf _ (by simp) permitted
  | anyOf alternatives => exact Permitted.anyOf _ (by simp) permitted
  | allOf constraints => exact Permitted.anyOf _ (by simp) permitted

/-- The executable base-leaf decision has exactly the direct adapter-input
    meaning in `LeafBasePermitted`. -/
theorem base_leaf_policy_contract (input : LeafInput) (candidate : JValue) :
    LeafBasePermitted input candidate ↔
      Permitted (baseLeafPolicy input) candidate := by
  cases input with
  | mk defaultValue directUsage inheritedOpen explicitNull =>
      cases defaultValue with
      | missing =>
          cases directUsage <;> cases inheritedOpen <;>
            simp [LeafBasePermitted, baseLeafPolicy]
      | templateString value =>
          cases directUsage <;> cases inheritedOpen <;>
            simp [LeafBasePermitted, baseLeafPolicy]
      | present value inferredType =>
          cases inferredType with
          | none =>
              cases directUsage <;> cases inheritedOpen <;>
                simp [LeafBasePermitted, baseLeafPolicy]
          | some kind =>
              cases directUsage <;> cases inheritedOpen <;>
                simp [LeafBasePermitted, baseLeafPolicy]

/-- Leaf policy compilation is equivalent to the direct candidate-level
    contract. -/
theorem leaf_policy_contract (input : LeafInput) (candidate : JValue) :
    LeafPermitted input candidate ↔
      Permitted (leafPolicy input) candidate := by
  cases explicitNull : input.explicitNull with
  | false =>
      simp [LeafPermitted, leafPolicy, explicitNull,
        base_leaf_policy_contract input candidate]
  | true =>
      rw [LeafPermitted, leafPolicy, explicitNull]
      simp only [true_and, if_pos]
      rw [permitDirectNull_iff, base_leaf_policy_contract]

/-- Fixed-value policy compilation is equivalent to exact default equality or
    an explicitly permitted null removal. -/
theorem fixed_policy_contract (expected candidate : JValue)
    (explicitNull : Bool) :
    FixedPermitted expected explicitNull candidate ↔
      Permitted (valuePolicy (.fixed expected explicitNull)) candidate := by
  cases explicitNull with
  | false => simp [FixedPermitted, valuePolicy]
  | true =>
      simp [FixedPermitted, valuePolicy, permitDirectNull_iff, or_comm]

private theorem contract_unrestricted_sound (candidate : JValue) :
    Permitted (valuePolicy .unrestricted) candidate := by
  rw [valuePolicy.eq_def]
  exact Permitted.unrestricted candidate

private theorem contract_typed_sound {kind : JsonType} {candidate : JValue}
    (typeProof : HasType candidate kind) :
    Permitted (valuePolicy (.typed kind)) candidate := by
  rw [valuePolicy.eq_def]
  exact Permitted.typed typeProof

private theorem contract_leaf_sound {input : LeafInput} {candidate : JValue}
    (permitted : LeafPermitted input candidate) :
    Permitted (valuePolicy (.leaf input)) candidate := by
  simpa [valuePolicy] using (leaf_policy_contract input candidate).1 permitted

private theorem contract_fixed_sound {expected candidate : JValue}
    {explicitNull : Bool}
    (permitted : FixedPermitted expected explicitNull candidate) :
    Permitted (valuePolicy (.fixed expected explicitNull)) candidate :=
  (fixed_policy_contract expected candidate explicitNull).1 permitted

private theorem contract_object_null_sound
    {properties : List (String × ValueInput)}
    {additional : Option ValueInput} {boundary : BoundaryInput}
    {explicitNull : Bool} {candidate : JValue}
    (nullable : explicitNull = true)
    (equal : JsonEquivalent .null candidate) :
    Permitted
      (valuePolicy (.object properties additional boundary explicitNull))
      candidate := by
  rw [valuePolicy.eq_def, nullable]
  simp only [if_pos]
  exact Permitted.anyOf (.constant .null) (by simp) (Permitted.constant equal)

private theorem contract_object_sound
    {properties : List (String × ValueInput)}
    {additional : Option ValueInput} {boundary : BoundaryInput}
    {explicitNull : Bool} {values : List (String × JValue)}
    (_each : ∀ entry, entry ∈ values →
      ValuePropertyPermitted properties additional boundary entry.1 entry.2)
    (eachSound : ∀ entry, entry ∈ values →
      PropertyPermitted
        (JObject.mapValues properties valuePolicy)
        (valueAdditionalPolicy additional boundary) entry.1 entry.2) :
    Permitted
      (valuePolicy (.object properties additional boundary explicitNull))
      (.object values) := by
  have objectPermitted : Permitted
      (.object (JObject.mapValues properties valuePolicy)
        (valueAdditionalPolicy additional boundary)) (.object values) :=
    Permitted.object eachSound
  cases explicitNull with
  | false =>
      rw [valuePolicy.eq_def]
      dsimp only
      rw [if_neg (by decide)]
      cases additional <;>
        simpa [JObject.mapValues, valueAdditionalPolicy] using objectPermitted
  | true =>
      rw [valuePolicy.eq_def]
      dsimp only
      rw [if_pos rfl]
      cases additional with
      | none =>
          exact Permitted.anyOf
            (.object
              (properties.map fun entry => (entry.1, valuePolicy entry.2))
              (additionalPolicy none boundary)) (by simp)
            (by simpa [JObject.mapValues, valueAdditionalPolicy] using objectPermitted)
      | some contract =>
          exact Permitted.anyOf
            (.object
              (properties.map fun entry => (entry.1, valuePolicy entry.2))
              (some (valuePolicy contract))) (by simp)
            (by simpa [JObject.mapValues, valueAdditionalPolicy] using objectPermitted)

private theorem contract_array_sound {items : ValueInput} {values : List JValue}
    (_each : ∀ value, value ∈ values → ValueInputPermitted items value)
    (eachSound : ∀ value, value ∈ values →
      Permitted (valuePolicy items) value) :
    Permitted (valuePolicy (.array items)) (.array values) := by
  rw [valuePolicy.eq_def]
  exact Permitted.array eachSound

private theorem contract_anyOf_sound {alternatives : List ValueInput}
    {candidate : JValue} (alternative : ValueInput)
    (member : alternative ∈ alternatives)
    (_permitted : ValueInputPermitted alternative candidate)
    (sound : Permitted (valuePolicy alternative) candidate) :
    Permitted (valuePolicy (.anyOf alternatives)) candidate := by
  rw [valuePolicy.eq_def]
  exact Permitted.anyOf (valuePolicy alternative)
    (List.mem_map.mpr ⟨alternative, member, rfl⟩) sound

private theorem contract_allOf_sound {constraints : List ValueInput}
    {candidate : JValue}
    (_each : ∀ constraint, constraint ∈ constraints →
      ValueInputPermitted constraint candidate)
    (eachSound : ∀ constraint, constraint ∈ constraints →
      Permitted (valuePolicy constraint) candidate) :
    Permitted (valuePolicy (.allOf constraints)) candidate := by
  rw [valuePolicy.eq_def]
  apply Permitted.allOf
  intro policy member
  obtain ⟨constraint, sourceMember, generated⟩ := List.mem_map.mp member
  subst policy
  exact eachSound constraint sourceMember

private theorem contract_known_property_sound
    {properties : List (String × ValueInput)}
    {additional : Option ValueInput} {boundary : BoundaryInput}
    {name : String} {candidate : JValue} {child : ValueInput}
    (found : JObject.get? properties name = some child)
    (_permitted : ValueInputPermitted child candidate)
    (childSound : Permitted (valuePolicy child) candidate) :
    PropertyPermitted (JObject.mapValues properties valuePolicy)
      (valueAdditionalPolicy additional boundary) name candidate := by
  apply PropertyPermitted.known
  · rw [JObject.get?_mapValues, found]
    rfl
  · exact childSound

private theorem contract_structured_property_sound
    {properties : List (String × ValueInput)}
    {additional : Option ValueInput} {boundary : BoundaryInput}
    {name : String} {candidate : JValue} {contract : ValueInput}
    (unknown : JObject.get? properties name = none)
    (found : additional = some contract)
    (_permitted : ValueInputPermitted contract candidate)
    (childSound : Permitted (valuePolicy contract) candidate) :
    PropertyPermitted (JObject.mapValues properties valuePolicy)
      (valueAdditionalPolicy additional boundary) name candidate := by
  subst additional
  apply PropertyPermitted.additional (propertyPolicy := valuePolicy contract)
  · rw [JObject.get?_mapValues, unknown]
    rfl
  · rfl
  · exact childSound

private theorem contract_unnamed_property_sound
    {properties : List (String × ValueInput)}
    {additional : Option ValueInput} {boundary : BoundaryInput}
    {name : String} {candidate : JValue}
    (unknown : JObject.get? properties name = none)
    (unstructured : additional = none)
    (relevant : UnnamedPropertyRelevant boundary) :
    PropertyPermitted (JObject.mapValues properties valuePolicy)
      (valueAdditionalPolicy additional boundary) name candidate := by
  subst additional
  have allowed : allowsUnnamed boundary = true :=
    (HelmSchema.Proofs.Boundary.allowsUnnamed_iff_relevant boundary).2 relevant
  apply PropertyPermitted.additional (propertyPolicy := .unrestricted)
  · rw [JObject.get?_mapValues, unknown]
    rfl
  · simp [valueAdditionalPolicy, additionalPolicy, allowed]
  · exact Permitted.unrestricted candidate

/-- Every candidate permitted by the direct recursive input contract is
    permitted by the compiled intermediate policy. -/
theorem value_input_contract_sound {input : ValueInput} {candidate : JValue}
    (permitted : ValueInputPermitted input candidate) :
    Permitted (valuePolicy input) candidate := by
  exact ValueInputPermitted.rec
    (motive_1 := fun input candidate _ =>
      Permitted (valuePolicy input) candidate)
    (motive_2 := fun properties additional boundary name candidate _ =>
      PropertyPermitted (JObject.mapValues properties valuePolicy)
        (valueAdditionalPolicy additional boundary) name candidate)
    contract_unrestricted_sound contract_typed_sound contract_leaf_sound
    contract_fixed_sound contract_object_null_sound contract_object_sound
    contract_array_sound contract_anyOf_sound contract_allOf_sound
    contract_known_property_sound contract_structured_property_sound
    contract_unnamed_property_sound permitted

/-- Direct property permission compiles to the corresponding intermediate
    object-property rule. -/
theorem value_property_contract_sound
    {properties : List (String × ValueInput)}
    {additional : Option ValueInput} {boundary : BoundaryInput}
    {name : String} {candidate : JValue}
    (permitted : ValuePropertyPermitted properties additional boundary
      name candidate) :
    PropertyPermitted (JObject.mapValues properties valuePolicy)
      (valueAdditionalPolicy additional boundary) name candidate := by
  exact ValuePropertyPermitted.rec
    (motive_1 := fun input candidate _ =>
      Permitted (valuePolicy input) candidate)
    (motive_2 := fun properties additional boundary name candidate _ =>
      PropertyPermitted (JObject.mapValues properties valuePolicy)
        (valueAdditionalPolicy additional boundary) name candidate)
    contract_unrestricted_sound contract_typed_sound contract_leaf_sound
    contract_fixed_sound contract_object_null_sound contract_object_sound
    contract_array_sound contract_anyOf_sound contract_allOf_sound
    contract_known_property_sound contract_structured_property_sound
    contract_unnamed_property_sound permitted

/-- Every candidate permitted by a compiled intermediate policy is permitted
    by the direct recursive input contract. -/
theorem value_input_contract_complete (input : ValueInput) (candidate : JValue)
    (permitted : Permitted (valuePolicy input) candidate) :
    ValueInputPermitted input candidate := by
  cases input with
  | unrestricted => exact ValueInputPermitted.unrestricted candidate
  | typed kind =>
      rw [valuePolicy.eq_def] at permitted
      cases permitted with
      | typed typeProof => exact ValueInputPermitted.typed typeProof
  | leaf leafInput =>
      exact ValueInputPermitted.leaf
        ((leaf_policy_contract leafInput candidate).2 (by
          simpa [valuePolicy] using permitted))
  | fixed expected explicitNull =>
      exact ValueInputPermitted.fixed
        ((fixed_policy_contract expected candidate explicitNull).2 permitted)
  | object properties additional boundary explicitNull =>
      let objectPolicy := Policy.object
        (JObject.mapValues properties valuePolicy)
        (valueAdditionalPolicy additional boundary)
      have completeObject (objectPermitted : Permitted objectPolicy candidate) :
          ValueInputPermitted
            (.object properties additional boundary explicitNull) candidate := by
        dsimp [objectPolicy] at objectPermitted
        cases objectPermitted with
        | object each =>
            apply ValueInputPermitted.object
            intro entry member
            have propertyPermitted := each entry member
            cases propertyPermitted with
            | known found childPermitted =>
                rw [JObject.get?_mapValues] at found
                cases lookup : JObject.get? properties entry.1 with
                | none => simp [lookup] at found
                | some child =>
                    simp [lookup] at found
                    subst_vars
                    exact ValuePropertyPermitted.known lookup
                      (value_input_contract_complete child entry.2 childPermitted)
            | additional unknown contract childPermitted =>
                rw [JObject.get?_mapValues] at unknown
                cases lookup : JObject.get? properties entry.1 with
                | some child => simp [lookup] at unknown
                | none =>
                    cases additional with
                    | some child =>
                        simp [valueAdditionalPolicy] at contract
                        subst_vars
                        exact ValuePropertyPermitted.structured lookup rfl
                          (value_input_contract_complete child entry.2 childPermitted)
                    | none =>
                        cases allowed : allowsUnnamed boundary with
                        | false =>
                            simp [valueAdditionalPolicy, additionalPolicy,
                              allowed] at contract
                        | true =>
                            exact ValuePropertyPermitted.unnamed lookup rfl
                              ((HelmSchema.Proofs.Boundary.allowsUnnamed_iff_relevant
                                boundary).1 allowed)
      cases explicitNull with
      | false =>
          apply completeObject
          rw [valuePolicy.eq_def] at permitted
          simpa [valueAdditionalPolicy, objectPolicy, JObject.mapValues] using permitted
      | true =>
          have alternative : JsonEquivalent .null candidate ∨
              Permitted objectPolicy candidate := by
            apply (null_alternative_iff objectPolicy candidate).1
            rw [valuePolicy.eq_def] at permitted
            simpa [valueAdditionalPolicy, objectPolicy, JObject.mapValues] using permitted
          cases alternative with
          | inl equal => exact ValueInputPermitted.objectNull rfl equal
          | inr objectPermitted => exact completeObject objectPermitted
  | array items =>
      rw [valuePolicy.eq_def] at permitted
      cases permitted with
      | array each =>
          apply ValueInputPermitted.array
          intro value member
          exact value_input_contract_complete items value (each value member)
  | anyOf alternatives =>
      rw [valuePolicy.eq_def] at permitted
      cases permitted with
      | anyOf policy member childPermitted =>
          obtain ⟨alternative, sourceMember, generated⟩ := List.mem_map.mp member
          subst policy
          exact ValueInputPermitted.anyOf alternative sourceMember
            (value_input_contract_complete alternative candidate childPermitted)
  | allOf constraints =>
      rw [valuePolicy.eq_def] at permitted
      cases permitted with
      | allOf each =>
          apply ValueInputPermitted.allOf
          intro constraint member
          apply value_input_contract_complete constraint candidate
          exact each (valuePolicy constraint)
            (List.mem_map.mpr ⟨constraint, member, rfl⟩)
termination_by sizeOf input
decreasing_by
  all_goals subst_vars
  all_goals try simp_wf
  all_goals
    first
    | omega
    | (rw [ValueInput.object.sizeOf_spec, Option.some.sizeOf_spec]
       omega)
    | (have sourceMember := JObject.pair_mem_of_get?_eq_some
          properties entry.1 child lookup
       have entrySize := List.sizeOf_lt_of_mem sourceMember
       rw [Prod.mk.sizeOf_spec] at entrySize
       omega)
    | (exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega))

/-- The direct recursive input contract and the compiled policy permit exactly
    the same candidates. -/
theorem value_input_policy_contract (input : ValueInput) (candidate : JValue) :
    ValueInputPermitted input candidate ↔
      Permitted (valuePolicy input) candidate :=
  ⟨value_input_contract_sound, value_input_contract_complete input candidate⟩

/-- A used leaf without type evidence remains unrestricted. -/
theorem leaf_without_type_is_unrestricted (value : JValue) :
    leafPolicy
      { defaultValue := .present value none
      , directUsage := false
      , inheritedOpen := true
      } =
      .unrestricted := by
  rfl

/-- An explicit raw null default permits null after ordinary leaf inference. -/
theorem explicit_null_is_permitted (input : LeafInput) :
    Permitted (leafPolicy { input with explicitNull := true }) .null := by
  simp only [leafPolicy]
  exact permitDirectNull_permits_null
    (baseLeafPolicy { input with explicitNull := true })

/-- An unused value of any JSON shape remains equal to its default. -/
theorem fixed_value_is_constant (value : JValue) :
    valuePolicy (.fixed value false) = .constant value := by
  simp [valuePolicy]

/-- A fixed default is accepted when the caller supplies semantic reflexivity. -/
theorem fixed_value_accepts_default_of_equivalent (value : JValue)
    (reflexive : JsonEquivalent value value) :
    Accepts (generate (valuePolicy (.fixed value false))) value := by
  apply Generator.permitted_sound
  simpa [valuePolicy] using Permitted.constant reflexive

/-- Every canonical fixed default is accepted unchanged. Canonical values have
    unique object names at every depth, as enforced by the protocol parser. -/
theorem fixed_value_accepts_default (value : JValue)
    (canonical : Canonical value) :
    Accepts (generate (valuePolicy (.fixed value false))) value :=
  fixed_value_accepts_default_of_equivalent value
    (canonical_jsonEquivalent_self canonical)

/-- A changed value cannot pass an unused fixed-default policy. -/
theorem fixed_value_rejects_change (expected actual : JValue)
    (different : ¬JsonEquivalent expected actual) :
    ¬Accepts (generate (valuePolicy (.fixed expected false))) actual := by
  intro accepted
  have permitted : Permitted (.constant expected) actual := by
    simpa [valuePolicy] using Generator.accepted_complete accepted
  cases permitted with
  | constant equal => exact different equal

/-- An explicitly nullable fixed value permits null. -/
theorem nullable_fixed_permits_null (value : JValue) :
    Permitted (valuePolicy (.fixed value true)) .null := by
  simp only [valuePolicy]
  exact permitDirectNull_permits_null (.constant value)

/-- Boolean type evidence keeps the Boolean type. -/
theorem inferred_boolean_is_typed (value : Bool) :
    leafPolicy
      { defaultValue := .present (.bool value) (some .boolean)
      , directUsage := true
      , inheritedOpen := false
      } =
        .typed .boolean := by
  rfl

/-- Each scalar with type evidence keeps exactly its inferred JSON type. -/
theorem inferred_scalar_is_typed (value : JValue) (kind : JsonType) :
    leafPolicy
      { defaultValue := .present value (some kind)
      , directUsage := true
      , inheritedOpen := false
      } =
        .typed kind := by
  simp [leafPolicy, baseLeafPolicy]

/-- A missing value accepts every JSON value. -/
theorem missing_leaf_is_unrestricted :
    leafPolicy
      { defaultValue := .missing, directUsage := true, inheritedOpen := false } =
      .unrestricted := by
  rfl

/-- A templated string does not impose a string type. -/
theorem template_leaf_is_unrestricted (value : String) :
    leafPolicy
      { defaultValue := .templateString value
      , directUsage := true
      , inheritedOpen := false
      } =
        .unrestricted := by
  rfl

/-- A templated string without type evidence remains unrestricted. -/
theorem template_without_type_is_unrestricted (value : String) :
    leafPolicy
      { defaultValue := .templateString value
      , directUsage := false
      , inheritedOpen := true
      } =
        .unrestricted := by
  rfl

/-- A nullable recursive object permits null. -/
theorem nullable_object_permits_null
    (properties : List (String × ValueInput)) (boundary : BoundaryInput) :
    Permitted (valuePolicy (.object properties none boundary true)) .null := by
  rw [valuePolicy.eq_def]
  simp only [if_pos]
  exact null_alternative_permits _

/-- A nullable recursive object preserves values that its object policy
    permits. -/
theorem nullable_object_preserves
    {properties : List (String × ValueInput)} {boundary : BoundaryInput}
    {value : JValue} (permitted : Permitted (objectPolicy properties boundary) value) :
    Permitted (valuePolicy (.object properties none boundary true)) value := by
  rw [valuePolicy.eq_def]
  simp only [if_pos]
  exact Permitted.anyOf
    (.object
      (properties.map fun entry => (entry.1, valuePolicy entry.2))
      (additionalPolicy none boundary))
    (by simp)
    (by simpa [objectPolicy, JObject.mapValues] using permitted)

/-- Generated validation preserves the intermediate policy language. The
    stronger `core_contract_correct` theorem below connects validation to the
    direct adapter-input contract. -/
theorem core_policy_correct (input : CoreInput) (value : JValue) :
    Accepts (generate (corePolicy input)) value ↔
      Permitted (corePolicy input) value :=
  Generator.generate_correct (corePolicy input) value

/-- Treating a root input as a non-nullable recursive object produces the same
    intermediate policy. -/
theorem core_policy_as_value (input : CoreInput) :
    valuePolicy
      (.object input.properties input.additional input.boundary false) =
      corePolicy input := by
  rw [valuePolicy.eq_def]
  simp [corePolicy, valueAdditionalPolicy, JObject.mapValues]

/-- The root contract is exactly the recursive object contract with no outer
    null alternative. -/
theorem core_contract_as_value (input : CoreInput) (candidate : JValue) :
    CoreInputPermitted input candidate ↔
      ValueInputPermitted
        (.object input.properties input.additional input.boundary false)
        candidate := by
  constructor
  · intro permitted
    cases permitted with
    | object each => exact ValueInputPermitted.object each
  · intro permitted
    cases permitted with
    | objectNull nullable equal => contradiction
    | object each => exact CoreInputPermitted.object each

/-- The compiled root policy permits exactly the candidates described by the
    direct input contract. -/
theorem core_input_policy_contract (input : CoreInput) (candidate : JValue) :
    CoreInputPermitted input candidate ↔
      Permitted (corePolicy input) candidate := by
  rw [core_contract_as_value, ← core_policy_as_value]
  exact value_input_policy_contract _ _

/-- Main correctness theorem for every compiled `CoreInput`.
    Generated schema validation is equivalent to the direct contract on
    `CoreInput`. The right side does not call the policy compiler or schema
    generator. -/
theorem core_contract_correct (input : CoreInput) (candidate : JValue) :
    Accepts (generate (corePolicy input)) candidate ↔
      CoreInputPermitted input candidate := by
  exact (Generator.generate_correct (corePolicy input) candidate).trans
    (core_input_policy_contract input candidate).symm

/-- An array input accepts exactly arrays whose members satisfy the item
    contract. This statement does not refer to the compiled policy. -/
theorem array_input_contract (items : ValueInput) (values : List JValue) :
    ValueInputPermitted (.array items) (.array values) ↔
      ∀ value, value ∈ values → ValueInputPermitted items value := by
  constructor
  · intro permitted
    cases permitted with
    | array each => exact each
  · exact ValueInputPermitted.array

/-- A generated array schema has exactly the direct item contract. -/
theorem generated_array_contract (items : ValueInput) (values : List JValue) :
    Accepts (generate (valuePolicy (.array items))) (.array values) ↔
      ∀ value, value ∈ values → ValueInputPermitted items value := by
  exact (Generator.generate_correct _ _).trans
    ((value_input_policy_contract _ _).symm.trans
      (array_input_contract items values))

/-- A shape alternative accepts exactly when at least one direct input
    alternative accepts the candidate. -/
theorem alternatives_input_contract (alternatives : List ValueInput)
    (candidate : JValue) :
    ValueInputPermitted (.anyOf alternatives) candidate ↔
      ∃ alternative, alternative ∈ alternatives ∧
        ValueInputPermitted alternative candidate := by
  constructor
  · intro permitted
    cases permitted with
    | anyOf alternative member child => exact ⟨alternative, member, child⟩
  · rintro ⟨alternative, member, permitted⟩
    exact ValueInputPermitted.anyOf alternative member permitted

/-- A generated shape union has exactly the direct alternative contract. -/
theorem generated_alternatives_contract (alternatives : List ValueInput)
    (candidate : JValue) :
    Accepts (generate (valuePolicy (.anyOf alternatives))) candidate ↔
      ∃ alternative, alternative ∈ alternatives ∧
        ValueInputPermitted alternative candidate := by
  exact (Generator.generate_correct _ _).trans
    ((value_input_policy_contract _ _).symm.trans
      (alternatives_input_contract alternatives candidate))

/-- A conjunction accepts exactly when every direct input constraint accepts
    the candidate. Used arrays combine their array shape and replacement
    alternatives through this contract. -/
theorem constraints_input_contract (constraints : List ValueInput)
    (candidate : JValue) :
    ValueInputPermitted (.allOf constraints) candidate ↔
      ∀ constraint, constraint ∈ constraints →
        ValueInputPermitted constraint candidate := by
  constructor
  · intro permitted
    cases permitted with
    | allOf each => exact each
  · exact ValueInputPermitted.allOf

/-- A generated conjunction has exactly the direct constraint contract. -/
theorem generated_constraints_contract (constraints : List ValueInput)
    (candidate : JValue) :
    Accepts (generate (valuePolicy (.allOf constraints))) candidate ↔
      ∀ constraint, constraint ∈ constraints →
        ValueInputPermitted constraint candidate := by
  exact (Generator.generate_correct _ _).trans
    ((value_input_policy_contract _ _).symm.trans
      (constraints_input_contract constraints candidate))

/-- At a structured dynamic boundary, every unknown name is checked against
    the explicit dynamic-entry contract. The ordinary open/closed boundary
    decision cannot bypass that contract. -/
theorem structured_unknown_property_contract
    (properties : List (String × ValueInput)) (additional : ValueInput)
    (boundary : BoundaryInput) (name : String) (candidate : JValue)
    (unknown : JObject.get? properties name = none) :
    ValuePropertyPermitted properties (some additional) boundary name candidate ↔
      ValueInputPermitted additional candidate := by
  constructor
  · intro permitted
    cases permitted with
    | known found _ => simp [unknown] at found
    | structured _ found child =>
        cases found
        exact child
    | unnamed _ unstructured _ => contradiction
  · intro permitted
    exact ValuePropertyPermitted.structured unknown rfl permitted

/-- A generated root schema with structured dynamic entries validates every
    unknown direct child with that entry contract. -/
theorem generated_structured_root_contract
    (properties : List (String × ValueInput)) (additional : ValueInput)
    (boundary : BoundaryInput) (name : String) (candidate : JValue)
    (unknown : JObject.get? properties name = none) :
    Accepts
        (generate (corePolicy
          { properties := properties
          , additional := some additional
          , boundary := boundary
          }))
        (.object [(name, candidate)]) ↔
      ValueInputPermitted additional candidate := by
  rw [core_contract_correct]
  constructor
  · intro permitted
    cases permitted with
    | object each =>
        exact (structured_unknown_property_contract properties additional
          boundary name candidate unknown).1
            (each (name, candidate) (by simp))
  · intro permitted
    apply CoreInputPermitted.object
    intro entry member
    simp only [List.mem_singleton] at member
    subst entry
    exact (structured_unknown_property_contract properties additional
      boundary name candidate unknown).2 permitted

/-- Unknown direct children of a supported object are accepted exactly when
    the executable boundary decision permits unnamed properties. -/
theorem object_unknown_property_decision
    (properties : List (String × ValueInput)) (boundary : BoundaryInput)
    (name : String)
    (value : JValue)
    (unknown : JObject.get? properties name = none) :
    Accepts (generate (objectPolicy properties boundary))
      (.object [(name, value)]) ↔ allowsUnnamed boundary = true := by
  have mappedUnknown :
      JObject.get? (JObject.mapValues properties valuePolicy) name = none := by
    rw [JObject.get?_mapValues, unknown]
    rfl
  exact HelmSchema.Proofs.Boundary.boundary_policy_correct
    (JObject.mapValues properties valuePolicy) boundary name value
      mappedUnknown

/-- Unknown direct children of a supported object are accepted exactly when
    an independent raw relevance reason applies at that boundary. -/
theorem object_unknown_property_correct
    (properties : List (String × ValueInput)) (boundary : BoundaryInput)
    (name : String)
    (value : JValue)
    (unknown : JObject.get? properties name = none) :
    Accepts (generate (objectPolicy properties boundary))
      (.object [(name, value)]) ↔ UnnamedPropertyRelevant boundary := by
  exact (object_unknown_property_decision properties boundary name value
    unknown).trans
      (HelmSchema.Proofs.Boundary.allowsUnnamed_iff_relevant boundary)

/-- Root unknown-property acceptance in the supported fragment is equivalent
    to the exported production boundary decision. -/
theorem core_unknown_property_decision (input : CoreInput) (name : String)
    (value : JValue)
    (unstructured : input.additional = none)
    (unknown : JObject.get?
      (JObject.mapValues input.properties valuePolicy) name = none) :
    Accepts (generate (corePolicy input)) (.object [(name, value)]) ↔
      allowsUnnamed input.boundary = true := by
  have policy : corePolicy input =
      boundaryPolicy (JObject.mapValues input.properties valuePolicy)
        input.boundary := by
    simp [corePolicy, boundaryPolicy, valueAdditionalPolicy,
      additionalPolicy, unstructured]
  rw [policy]
  exact HelmSchema.Proofs.Boundary.boundary_policy_correct
    (JObject.mapValues input.properties valuePolicy)
    input.boundary name value unknown

/-- Root unknown-property acceptance in the supported fragment is equivalent
    to an independent raw relevance reason at the root boundary. -/
theorem core_unknown_property_correct (input : CoreInput) (name : String)
    (value : JValue)
    (unstructured : input.additional = none)
    (unknown : JObject.get?
      (JObject.mapValues input.properties valuePolicy) name = none) :
    Accepts (generate (corePolicy input)) (.object [(name, value)]) ↔
      UnnamedPropertyRelevant input.boundary := by
  exact (core_unknown_property_decision input name value unstructured unknown).trans
    (HelmSchema.Proofs.Boundary.allowsUnnamed_iff_relevant input.boundary)

end HelmSchema.Proofs.Core
