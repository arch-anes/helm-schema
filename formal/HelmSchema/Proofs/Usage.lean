import HelmSchema.Usage

set_option autoImplicit false

namespace HelmSchema.Proofs.Usage

/-!
This module is the public proof surface for the usage algebra. The theorem
names make the algebraic contract easy to find without exposing implementation
details from `HelmSchema.Usage`.
-/

/-- Public associative merge law. -/
theorem associative (first second third : HelmSchema.Usage) :
    (first.merge second).merge third = first.merge (second.merge third) :=
  HelmSchema.Usage.merge_associative first second third

/-- Public commutative merge law, modulo observation membership. -/
theorem commutative (left right : HelmSchema.Usage) :
    (left.merge right).Equivalent (right.merge left) :=
  HelmSchema.Usage.merge_commutative left right

/-- Public idempotent merge law, modulo observation membership. -/
theorem idempotent (usage : HelmSchema.Usage) :
    (usage.merge usage).Equivalent usage :=
  HelmSchema.Usage.merge_idempotent usage

/-- Public left-identity law. -/
theorem empty_left (usage : HelmSchema.Usage) :
    HelmSchema.Usage.empty.merge usage = usage :=
  HelmSchema.Usage.merge_empty_left usage

/-- Public right-identity law. -/
theorem empty_right (usage : HelmSchema.Usage) :
    usage.merge HelmSchema.Usage.empty = usage :=
  HelmSchema.Usage.merge_empty_right usage

/-- Public proof that merge retains its left input. -/
theorem keeps_left (left right : HelmSchema.Usage)
    (observation : HelmSchema.Observation)
    (present : left.contains observation) :
    (left.merge right).contains observation :=
  HelmSchema.Usage.left_contained_in_merge left right observation present

/-- Public proof that merge retains its right input. -/
theorem keeps_right (left right : HelmSchema.Usage)
    (observation : HelmSchema.Observation)
    (present : right.contains observation) :
    (left.merge right).contains observation :=
  HelmSchema.Usage.right_contained_in_merge left right observation present

end HelmSchema.Proofs.Usage
