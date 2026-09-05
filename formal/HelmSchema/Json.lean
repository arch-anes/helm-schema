import Std

set_option autoImplicit false

namespace HelmSchema

/-- An exact JSON number represented as a decimal mantissa and scale.
    Its value is `mantissa * 10^-scale`. -/
structure JsonNumber where
  mantissa : Int
  scale : Nat
  deriving BEq, DecidableEq, Repr

namespace JsonNumber

/-- Construct an exact integer. -/
def integer (value : Int) : JsonNumber := { mantissa := value, scale := 0 }

/-- Construct a number from a decimal mantissa and scale. -/
def ofScientific (mantissa : Int) (scale : Nat) : JsonNumber :=
  { mantissa := mantissa, scale := scale }

/-- Return the canonical numeric key that ignores trailing decimal zeroes. -/
def key (value : JsonNumber) : Int × Nat :=
  let rec removeZeroes (mantissa : Int) (scale : Nat) : Int × Nat :=
    match scale with
    | 0 => (mantissa, 0)
    | next + 1 =>
        if mantissa % 10 = 0 then
          removeZeroes (mantissa / 10) next
        else
          (mantissa, next + 1)
  if value.mantissa = 0 then (0, 0)
  else removeZeroes value.mantissa value.scale

/-- Report whether two JSON number spellings have the same numeric value. -/
def equal (left right : JsonNumber) : Bool := left.key == right.key

/-- Mathematical numeric equality. -/
def Equivalent (left right : JsonNumber) : Prop := left.key = right.key

/-- Report whether the number has no fractional part. -/
def isInteger (value : JsonNumber) : Bool :=
  value.mantissa % (10 ^ value.scale) == 0

/-- The number has no fractional part. -/
def IsInteger (value : JsonNumber) : Prop :=
  value.mantissa % (10 ^ value.scale) = 0

/-- Boolean numeric equality agrees with mathematical numeric equality. -/
theorem equal_correct (left right : JsonNumber) :
    equal left right = true ↔ Equivalent left right := by
  simp [equal, Equivalent]

/-- Boolean integer classification agrees with its proposition. -/
theorem isInteger_correct (value : JsonNumber) :
    isInteger value = true ↔ IsInteger value := by
  simp [isInteger, IsInteger]

end JsonNumber

/-- A finite JSON object. A schema protocol must sort keys and remove duplicate
    keys before conversion. Proofs use lookup behavior, not list order. -/
abbrev JObject (α : Type) := List (String × α)

/-- JSON values that Helm values schemas can validate. -/
inductive JValue where
  | null
  | bool (value : Bool)
  | number (value : JsonNumber)
  | string (value : String)
  | array (items : List JValue)
  | object (properties : List (String × JValue))
  deriving BEq, Repr

namespace JObject

variable {α β : Type}

/-- Find a property by name. Callers must supply unique keys, so a successful
    lookup has one meaning. -/
def get? (object : JObject α) (name : String) : Option α :=
  match object with
  | [] => none
  | (key, value) :: rest =>
      if key == name then some value else get? rest name

/-- Report whether an object contains a property. -/
def contains (object : JObject α) (name : String) : Bool :=
  (object.get? name).isSome

/-- Replace a property or add it at the end of the object. -/
def insert (object : JObject α) (name : String) (value : α) : JObject α :=
  (object.filter fun entry => entry.1 != name) ++ [(name, value)]

/-- Remove a property from an object. -/
def erase (object : JObject α) (name : String) : JObject α :=
  object.filter fun entry => entry.1 != name

/-- Apply a function to every property value. -/
def mapValues (object : JObject α) (function : α → β) : JObject β :=
  object.map fun entry => (entry.1, function entry.2)

/-- An object has one value for each property name. -/
def NamesUnique (object : JObject α) : Prop :=
  (object.map fun entry => entry.1).Nodup

/-- Lookup fails for an empty object. -/
@[simp]
theorem get?_empty (name : String) : (get? ([] : JObject α) name) = none := rfl

/-- Lookup returns the first property when its name matches. -/
@[simp]
theorem get?_same (name : String) (value : α) (rest : JObject α) :
    get? ((name, value) :: rest) name = some value := by
  unfold get?
  have same : (name == name) = true := by
    change (decide (name = name)) = true
    exact decide_eq_true rfl
  simp only [same, ↓reduceIte]

/-- Lookup skips a property when its name differs. -/
theorem get?_different (key name : String) (value : α) (rest : JObject α)
    (different : key ≠ name) :
    get? ((key, value) :: rest) name = get? rest name := by
  simp [get?, different]

/-- Looking up a mapped object is the same as mapping a successful lookup. -/
theorem get?_mapValues (object : JObject α) (function : α → β)
    (name : String) :
    get? (mapValues object function) name = (get? object name).map function := by
  induction object with
  | nil => rfl
  | cons entry rest induction =>
      cases entry with
      | mk key value =>
          simp only [mapValues, List.map_cons, get?]
          split
          · rfl
          · change get? (mapValues rest function) name =
              Option.map function (get? rest name)
            exact induction

/-- A successful lookup identifies an entry in the object list. -/
theorem pair_mem_of_get?_eq_some (object : JObject α) (name : String)
    (value : α) (found : get? object name = some value) :
    (name, value) ∈ object := by
  induction object with
  | nil => simp at found
  | cons entry rest induction =>
      cases entry with
      | mk key candidate =>
          simp only [get?] at found
          split at found
          · simp_all
          · exact List.mem_cons_of_mem _ (induction found)

/-- In an object with unique names, membership determines lookup. -/
theorem get?_eq_some_of_mem {object : JObject α} {name : String} {value : α}
    (unique : NamesUnique object) (member : (name, value) ∈ object) :
    get? object name = some value := by
  induction object with
  | nil => simp at member
  | cons entry rest induction =>
      cases entry with
      | mk key candidate =>
          simp only [NamesUnique, List.map_cons, List.nodup_cons] at unique
          simp only [List.mem_cons] at member
          rcases member with equal | tailMember
          · cases equal
            exact get?_same name value rest
          · have different : key ≠ name := by
              intro equal
              apply unique.1
              rw [equal]
              exact List.mem_map.mpr ⟨(name, value), tailMember, rfl⟩
            rw [get?_different key name candidate rest different]
            exact induction unique.2 tailMember

end JObject

/-- A canonical JSON value has unique object property names at every depth. -/
inductive Canonical : JValue → Prop where
  | null : Canonical .null
  | bool (value : Bool) : Canonical (.bool value)
  | number (value : JsonNumber) : Canonical (.number value)
  | string (value : String) : Canonical (.string value)
  | array {items : List JValue}
      (each : ∀ item, item ∈ items → Canonical item) :
      Canonical (.array items)
  | object {properties : List (String × JValue)}
      (unique : JObject.NamesUnique properties)
      (each : ∀ entry, entry ∈ properties → Canonical entry.2) :
      Canonical (.object properties)

/-- Semantic JSON equality with exact numbers and order-independent objects.
    Object inputs must not contain duplicate keys. -/
def jsonEqualFuel : Nat → JValue → JValue → Bool
  | 0, _, _ => false
  | _ + 1, .null, .null => true
  | _ + 1, .bool left, .bool right => left == right
  | _ + 1, .number left, .number right => left.equal right
  | _ + 1, .string left, .string right => left == right
  | fuel + 1, .array left, .array right =>
      left.length == right.length &&
        (left.zip right).all fun pair => jsonEqualFuel fuel pair.1 pair.2
  | fuel + 1, .object left, .object right =>
      left.length == right.length && left.all fun entry =>
        match JObject.get? right entry.1 with
        | none => false
        | some value => jsonEqualFuel fuel entry.2 value
  | _ + 1, _, _ => false
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

/-- Declarative JSON equality with an explicit recursion budget. This
    definition does not call the executable Boolean equality function. -/
def jsonEquivalentFuel : Nat → JValue → JValue → Prop
  | 0, _, _ => False
  | _ + 1, .null, .null => True
  | _ + 1, .bool left, .bool right => left = right
  | _ + 1, .number left, .number right => left.Equivalent right
  | _ + 1, .string left, .string right => left = right
  | fuel + 1, .array left, .array right =>
      left.length = right.length ∧ ∀ pair, pair ∈ left.zip right →
        jsonEquivalentFuel fuel pair.1 pair.2
  | fuel + 1, .object left, .object right =>
      left.length = right.length ∧ ∀ entry, entry ∈ left →
        match JObject.get? right entry.1 with
        | none => False
        | some value => jsonEquivalentFuel fuel entry.2 value
  | _ + 1, _, _ => False
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

/-- Executable and declarative equality agree at every explicit recursion
    budget. -/
theorem jsonEqualFuel_correct (fuel : Nat) (left right : JValue) :
    jsonEqualFuel fuel left right = true ↔
      jsonEquivalentFuel fuel left right := by
  induction fuel generalizing left right with
  | zero => simp [jsonEqualFuel, jsonEquivalentFuel]
  | succ fuel induction =>
      cases left <;> cases right <;>
        simp [jsonEqualFuel, jsonEquivalentFuel, JsonNumber.equal_correct,
          induction, List.all_eq_true]
      case object.object left right =>
        intro _
        constructor
        · intro executable name value member
          have accepted := executable name value member
          cases lookup : JObject.get? right name with
          | none => simp [lookup] at accepted
          | some candidate =>
              simp [lookup] at accepted ⊢
              exact (induction value candidate).1 accepted
        · intro declarative name value member
          have accepted := declarative name value member
          cases lookup : JObject.get? right name with
          | none => simp [lookup] at accepted
          | some candidate =>
              simp [lookup] at accepted ⊢
              exact (induction value candidate).2 accepted

/-- Compute a recursion budget for one JSON value. -/
def valueBudget : JValue → Nat
  | .null => 1
  | .bool _ => 1
  | .number _ => 1
  | .string _ => 1
  | .array items => 1 + (items.map valueBudget).sum
  | .object properties =>
      1 + (properties.map fun entry => valueBudget entry.2).sum
termination_by value => sizeOf value
decreasing_by
  · rename_i item member
    rw [JValue.array.sizeOf_spec]
    exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)
  · simp_wf
    cases entry with
    | mk name child =>
      have entrySize := List.sizeOf_lt_of_mem (by assumption)
      rw [Prod.mk.sizeOf_spec] at entrySize
      change sizeOf child < 1 + sizeOf properties
      omega

/-- A member of a list contributes no more than the sum of a nonnegative
    measure over that list. -/
theorem mappedValue_le_sum {α : Type} (measure : α → Nat)
    {value : α} {values : List α} (member : value ∈ values) :
    measure value ≤ (values.map measure).sum := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      simp only [List.map_cons, List.sum_cons]
      rcases member with equal | tailMember
      · subst head
        omega
      · have bound := induction tailMember
        omega

/-- Every pair in a list zipped with itself contains the same source member on
    both sides. -/
theorem mem_zip_self {items : List JValue} {pair : JValue × JValue}
    (member : pair ∈ items.zip items) :
    ∃ item, item ∈ items ∧ pair = (item, item) := by
  induction items with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with equal | tailMember
      · exact ⟨head, by simp, equal⟩
      · obtain ⟨item, itemMember, equal⟩ := induction tailMember
        exact ⟨item, by simp [itemMember], equal⟩

/-- A canonical value is semantically equal to itself at every sufficient
    recursion budget. -/
theorem canonical_jsonEquivalentFuel_self {value : JValue}
    (canonical : Canonical value) (fuel : Nat)
    (enough : valueBudget value < fuel) :
    jsonEquivalentFuel fuel value value := by
  induction canonical generalizing fuel with
  | null =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel => simp [jsonEquivalentFuel]
  | bool value =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel => simp [jsonEquivalentFuel]
  | number value =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel => simp [jsonEquivalentFuel, JsonNumber.Equivalent]
  | string value =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel => simp [jsonEquivalentFuel]
  | array each eachInduction =>
      rename_i items
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ childFuel =>
          simp only [jsonEquivalentFuel, true_and]
          intro pair pairMember
          obtain ⟨item, itemMember, rfl⟩ := mem_zip_self pairMember
          apply eachInduction item itemMember
          have childBound := mappedValue_le_sum valueBudget itemMember
          have sumBound :
              (items.map valueBudget).sum < childFuel := by
            apply Nat.lt_of_succ_lt_succ
            simpa [valueBudget, Nat.succ_eq_add_one, Nat.add_comm] using enough
          exact Nat.lt_of_le_of_lt childBound sumBound
  | object unique each eachInduction =>
      rename_i properties
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ childFuel =>
          simp only [jsonEquivalentFuel, true_and]
          intro entry entryMember
          rw [JObject.get?_eq_some_of_mem unique entryMember]
          apply eachInduction entry entryMember
          have childBound := mappedValue_le_sum
            (fun property : String × JValue => valueBudget property.2)
            entryMember
          have sumBound :
              (properties.map fun property => valueBudget property.2).sum <
                childFuel := by
            apply Nat.lt_of_succ_lt_succ
            simpa [valueBudget, Nat.succ_eq_add_one, Nat.add_comm] using enough
          exact Nat.lt_of_le_of_lt childBound sumBound

/-- Semantic JSON equality. The derived budget exceeds both value depths. -/
def jsonEqual (left right : JValue) : Bool :=
  jsonEqualFuel (valueBudget left + valueBudget right + 1) left right

/-- Declarative semantic JSON equality with a budget derived from both values. -/
def JsonEquivalent (left right : JValue) : Prop :=
  jsonEquivalentFuel (valueBudget left + valueBudget right + 1) left right

/-- Semantic JSON equality is reflexive for canonical values. -/
theorem canonical_jsonEquivalent_self {value : JValue}
    (canonical : Canonical value) : JsonEquivalent value value := by
  apply canonical_jsonEquivalentFuel_self canonical
  omega

/-- Executable semantic JSON equality decides the declarative relation. -/
theorem jsonEqual_correct (left right : JValue) :
    jsonEqual left right = true ↔ JsonEquivalent left right := by
  exact jsonEqualFuel_correct _ left right

/-- Only JSON null is semantically equal to JSON null. -/
theorem jsonEquivalent_null_iff (value : JValue) :
    JsonEquivalent .null value ↔ value = .null := by
  cases value <;>
    simp [JsonEquivalent, jsonEquivalentFuel, valueBudget]

/-- One property path inside a JSON value. -/
abbrev ValuePath := List String

end HelmSchema
