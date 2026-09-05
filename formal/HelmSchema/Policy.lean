import HelmSchema.Schema

set_option autoImplicit false

namespace HelmSchema

/-- The intermediate validation policy that schema generation implements. Its
    declarative meaning is independent from the generated `Schema` syntax. -/
inductive Policy where
  | unrestricted
  | constant (value : JValue)
  | typed (kind : JsonType)
  | object (properties : List (String × Policy))
      (additional : Option Policy)
  | array (items : Policy)
  | anyOf (alternatives : List Policy)
  | allOf (constraints : List Policy)
  deriving Repr

mutual
  /-- The policy permits one candidate override. -/
  inductive Permitted : Policy → JValue → Prop where
    | unrestricted (value : JValue) : Permitted .unrestricted value
    | constant {expected actual : JValue}
        (equal : JsonEquivalent expected actual) :
        Permitted (.constant expected) actual
    | typed {value : JValue} {kind : JsonType}
        (typeProof : HasType value kind) : Permitted (.typed kind) value
    | object {properties : List (String × Policy)}
        {additional : Option Policy} {values : List (String × JValue)}
        (each : ∀ entry, entry ∈ values →
          PropertyPermitted properties additional entry.1 entry.2) :
        Permitted (.object properties additional) (.object values)
    | array {itemPolicy : Policy} {items : List JValue}
        (each : ∀ item, item ∈ items → Permitted itemPolicy item) :
        Permitted (.array itemPolicy) (.array items)
    | anyOf {alternatives : List Policy} {value : JValue}
        (alternative : Policy) (member : alternative ∈ alternatives)
        (permitted : Permitted alternative value) :
        Permitted (.anyOf alternatives) value
    | allOf {constraints : List Policy} {value : JValue}
        (each : ∀ constraint, constraint ∈ constraints →
          Permitted constraint value) :
        Permitted (.allOf constraints) value

  /-- The policy permits one property at an object boundary. -/
  inductive PropertyPermitted : List (String × Policy) → Option Policy →
      String → JValue → Prop where
    | known {properties additional name value propertyPolicy}
        (found : JObject.get? properties name = some propertyPolicy)
        (permitted : Permitted propertyPolicy value) :
        PropertyPermitted properties additional name value
    | additional {properties additional name value propertyPolicy}
        (unknown : JObject.get? properties name = none)
        (contract : additional = some propertyPolicy)
        (permitted : Permitted propertyPolicy value) :
        PropertyPermitted properties additional name value
end

end HelmSchema
