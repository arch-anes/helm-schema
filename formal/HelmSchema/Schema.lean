import HelmSchema.Json

set_option autoImplicit false

namespace HelmSchema

/-- JSON types represented by the generated Draft 7 subset. -/
inductive JsonType where
  | null
  | boolean
  | integer
  | number
  | string
  | array
  | object
  deriving BEq, DecidableEq, Repr

/-- The semantic subset of JSON Schema emitted by the Go generator.

`object` uses `none` to reject unnamed properties. `some contract` validates
each unnamed property with that contract. `some any` permits all unnamed
properties. -/
inductive Schema where
  | any
  | constant (value : JValue)
  | typed (kind : JsonType)
  | object (properties : List (String × Schema))
      (additional : Option Schema)
  | array (items : Schema)
  | anyOf (alternatives : List Schema)
  | allOf (constraints : List Schema)
  deriving BEq, Repr

/-- The independent type relation used by declarative schema acceptance. -/
def HasType : JValue → JsonType → Prop
  | .null, .null => True
  | .bool _, .boolean => True
  | .number value, .integer => JsonNumber.IsInteger value
  | .number _, .number => True
  | .string _, .string => True
  | .array _, .array => True
  | .object _, .object => True
  | _, _ => False

/-- Boolean JSON type validation. -/
def hasType : JValue → JsonType → Bool
  | .null, .null => true
  | .bool _, .boolean => true
  | .number value, .integer => JsonNumber.isInteger value
  | .number _, .number => true
  | .string _, .string => true
  | .array _, .array => true
  | .object _, .object => true
  | _, _ => false

/-- Boolean type validation is equivalent to the declarative type relation. -/
theorem hasType_correct (value : JValue) (kind : JsonType) :
    hasType value kind = true ↔ HasType value kind := by
  cases value <;> cases kind <;> simp [hasType, HasType]
  case number.integer number => exact JsonNumber.isInteger_correct number

mutual
  /-- Declarative schema acceptance. This relation is independent from the
      Boolean validator. -/
  inductive Accepts : Schema → JValue → Prop where
    | any (value : JValue) : Accepts .any value
    | constant {expected actual : JValue}
        (equal : JsonEquivalent expected actual) :
        Accepts (.constant expected) actual
    | typed {value : JValue} {kind : JsonType}
        (typeProof : HasType value kind) : Accepts (.typed kind) value
    | object {properties : List (String × Schema)}
        {additional : Option Schema} {values : List (String × JValue)}
        (each : ∀ entry, entry ∈ values →
          PropertyAccepts properties additional entry.1 entry.2) :
        Accepts (.object properties additional) (.object values)
    | array {itemSchema : Schema} {items : List JValue}
        (each : ∀ item, item ∈ items → Accepts itemSchema item) :
        Accepts (.array itemSchema) (.array items)
    | anyOf {alternatives : List Schema} {value : JValue}
        (alternative : Schema) (member : alternative ∈ alternatives)
        (accepted : Accepts alternative value) :
        Accepts (.anyOf alternatives) value
    | allOf {constraints : List Schema} {value : JValue}
        (each : ∀ constraint, constraint ∈ constraints →
          Accepts constraint value) :
        Accepts (.allOf constraints) value

  /-- Declarative validation for one object property. -/
  inductive PropertyAccepts : List (String × Schema) → Option Schema →
      String → JValue → Prop where
    | known {properties additional name value propertySchema}
        (found : JObject.get? properties name = some propertySchema)
        (accepted : Accepts propertySchema value) :
        PropertyAccepts properties additional name value
    | additional {properties additional name value propertySchema}
        (unknown : JObject.get? properties name = none)
        (contract : additional = some propertySchema)
        (accepted : Accepts propertySchema value) :
        PropertyAccepts properties additional name value
end

mutual
  /-- Validate one property with a fixed recursion budget. -/
  def acceptsPropertyFuel (fuel : Nat) (properties : List (String × Schema))
      (additional : Option Schema) (entry : String × JValue) : Bool :=
    match JObject.get? properties entry.1 with
    | some propertySchema => acceptsFuel fuel propertySchema entry.2
    | none =>
        match additional with
        | some propertySchema => acceptsFuel fuel propertySchema entry.2
        | none => false

  /-- Executable schema validation with an explicit recursion budget. -/
  def acceptsFuel : Nat → Schema → JValue → Bool
    | 0, _, _ => false
    | _ + 1, .any, _ => true
    | _ + 1, .constant expected, actual => jsonEqual expected actual
    | _ + 1, .typed kind, value => hasType value kind
    | fuel + 1, .object properties additional, .object values =>
        values.all (acceptsPropertyFuel fuel properties additional)
    | fuel + 1, .array itemSchema, .array items =>
        items.all (acceptsFuel fuel itemSchema)
    | fuel + 1, .anyOf alternatives, value =>
        alternatives.any fun alternative => acceptsFuel fuel alternative value
    | fuel + 1, .allOf constraints, value =>
        constraints.all fun constraint => acceptsFuel fuel constraint value
    | _ + 1, _, _ => false
end

/-- Compute a recursion budget greater than every nested schema depth. -/
def schemaBudget : Schema → Nat
  | .any => 1
  | .constant _ => 1
  | .typed _ => 1
  | .object properties additional =>
      1 + (properties.map fun entry => schemaBudget entry.2).sum +
        (match additional with
         | none => 0
         | some propertySchema => schemaBudget propertySchema)
  | .array items => 1 + schemaBudget items
  | .anyOf alternatives =>
      1 + (alternatives.map schemaBudget).sum
  | .allOf constraints =>
      1 + (constraints.map schemaBudget).sum
termination_by schema => sizeOf schema
decreasing_by
  · cases entry with
    | mk name propertySchema =>
        have member : (name, propertySchema) ∈ properties := by assumption
        have entrySize := List.sizeOf_lt_of_mem member
        rw [Prod.mk.sizeOf_spec] at entrySize
        rw [Schema.object.sizeOf_spec]
        change sizeOf propertySchema < _
        omega
  · rw [Schema.object.sizeOf_spec, Option.some.sizeOf_spec]
    omega
  · rw [Schema.array.sizeOf_spec]
    omega
  · rename_i alternative member
    rw [Schema.anyOf.sizeOf_spec]
    exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)
  · rename_i constraint member
    rw [Schema.allOf.sizeOf_spec]
    exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)

/-- Validate a value with a recursion budget derived from the schema.
    Callers do not choose this implementation detail. -/
def accepts (schema : Schema) (value : JValue) : Bool :=
  acceptsFuel (schemaBudget schema + 1) schema value

end HelmSchema
