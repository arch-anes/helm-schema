import HelmSchema.Policy

set_option autoImplicit false

namespace HelmSchema

/-- Convert the intermediate policy into the semantic schema language. -/
def generate : Policy → Schema
  | .unrestricted => .any
  | .constant value => .constant value
  | .typed kind => .typed kind
  | .object properties additional =>
      .object
        (properties.map fun entry => (entry.1, generate entry.2))
        (match additional with
         | none => none
         | some policy => some (generate policy))
  | .array items => .array (generate items)
  | .anyOf alternatives => .anyOf (alternatives.map generate)
  | .allOf constraints => .allOf (constraints.map generate)
termination_by policy => sizeOf policy
decreasing_by
  · cases entry with
    | mk name propertyPolicy =>
        have member : (name, propertyPolicy) ∈ properties := by assumption
        have entrySize := List.sizeOf_lt_of_mem member
        rw [Prod.mk.sizeOf_spec] at entrySize
        rw [Policy.object.sizeOf_spec]
        change sizeOf propertyPolicy < 1 + sizeOf properties + sizeOf additional
        omega
  · rw [Policy.object.sizeOf_spec, Option.some.sizeOf_spec]
    omega
  · rw [Policy.array.sizeOf_spec]
    omega
  · rename_i alternative member
    rw [Policy.anyOf.sizeOf_spec]
    exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)
  · rename_i constraint member
    rw [Policy.allOf.sizeOf_spec]
    exact Nat.lt_trans (List.sizeOf_lt_of_mem member) (by omega)

end HelmSchema
