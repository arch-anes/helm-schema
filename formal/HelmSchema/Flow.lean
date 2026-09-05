import HelmSchema.Usage

set_option autoImplicit false

namespace HelmSchema

namespace FlowName

/-- Compare natural numbers without the library equality type class. -/
private def natEqual : Nat → Nat → Bool
  | 0, 0 => true
  | left + 1, right + 1 => natEqual left right
  | _, _ => false

/-- The local natural-number comparison is reflexive. -/
private theorem natEqual_self (value : Nat) : natEqual value value = true := by
  induction value with
  | zero => rfl
  | succ value induction => exact induction

/-- A successful local natural-number comparison implies equality. -/
private theorem natEqual_sound {left right : Nat}
    (equal : natEqual left right = true) : left = right := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => rfl
      | succ right => exact Bool.noConfusion equal
  | succ left induction =>
      cases right with
      | zero => exact Bool.noConfusion equal
      | succ right =>
          exact congrArg Nat.succ (induction equal)

/-- Compare bytes by their natural-number values. -/
private def byteEqual (left right : UInt8) : Bool :=
  natEqual left.toNat right.toNat

/-- The local byte comparison is reflexive. -/
private theorem byteEqual_self (value : UInt8) :
    byteEqual value value = true :=
  natEqual_self value.toNat

/-- A successful local byte comparison implies equality. -/
private theorem byteEqual_sound {left right : UInt8}
    (equal : byteEqual left right = true) : left = right := by
  apply UInt8.toNat_inj.mp
  exact natEqual_sound equal

/-- Compare two byte lists in order. -/
private def bytesEqual : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      byteEqual left right && bytesEqual leftRest rightRest
  | _, _ => false

/-- The local byte-list comparison is reflexive. -/
private theorem bytesEqual_self (value : List UInt8) :
    bytesEqual value value = true := by
  induction value with
  | nil => rfl
  | cons head tail induction =>
      simp only [bytesEqual, Bool.and_eq_true]
      exact ⟨byteEqual_self head, induction⟩

/-- A successful local byte-list comparison implies equality. -/
private theorem bytesEqual_sound {left right : List UInt8}
    (equal : bytesEqual left right = true) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => exact Bool.noConfusion equal
  | cons leftHead leftTail induction =>
      cases right with
      | nil => exact Bool.noConfusion equal
      | cons rightHead rightTail =>
          simp only [bytesEqual, Bool.and_eq_true] at equal
          have heads := byteEqual_sound equal.1
          have tails := induction equal.2
          subst rightHead
          subst rightTail
          rfl

/-- Compare flow property names by their UTF-8 bytes. This local executable
    comparison satisfies the strict declaration audit. -/
def equal (left right : String) : Bool :=
  bytesEqual left.toByteArray.data.toList right.toByteArray.data.toList

/-- Flow property-name comparison is reflexive. -/
theorem equal_self (value : String) : equal value value = true :=
  bytesEqual_self value.toByteArray.data.toList

/-- A successful flow property-name comparison implies string equality. -/
theorem equal_sound {left right : String} (same : equal left right = true) :
    left = right := by
  have bytes : left.toByteArray.data.toList =
      right.toByteArray.data.toList := bytesEqual_sound same
  cases left with
  | ofByteArray leftBytes leftValid =>
      cases right with
      | ofByteArray rightBytes rightValid =>
          cases leftBytes with
          | mk leftData =>
              cases rightBytes with
              | mk rightData =>
                  cases leftData with
                  | mk leftList =>
                      cases rightData with
                      | mk rightList =>
                          cases bytes
                          rfl

/-- Flow property-name comparison is true exactly for equal strings. -/
theorem equal_iff (left right : String) :
    equal left right = true ↔ left = right := by
  constructor
  · exact equal_sound
  · intro same
    subst right
    exact equal_self left

end FlowName

/-- One Helm dependency value copy. Helm can copy the source subtree to the
    destination, and validation evidence must therefore move both ways. -/
structure ValueFlow where
  source : List String
  destination : List String
  deriving BEq, Repr

/-- Convert fixed property names into a usage path prefix. -/
def propertySegments (names : List String) : UsagePath :=
  names.map UsageSegment.property

/-- Remove an exact fixed-property prefix. Non-property suffix segments are
    retained because flows copy the complete value subtree. -/
def stripPropertyPrefix : UsagePath → List String → Option UsagePath
  | path, [] => some path
  | .property actual :: path, expected :: remaining =>
      if FlowName.equal actual expected then
        stripPropertyPrefix path remaining
      else
        none
  | _, _ :: _ => none

/-- Replace one fixed-property prefix and retain the complete suffix. -/
def remapPropertyPrefix (path : UsagePath)
    (sourceNames destinationNames : List String) :
    Option UsagePath := do
  let suffix ← stripPropertyPrefix path sourceNames
  pure (propertySegments destinationNames ++ suffix)

namespace ValueFlow

/-- Return every direct path produced by one bidirectional copy edge. -/
def remapBoth (flow : ValueFlow) (path : UsagePath) : List UsagePath :=
  [ remapPropertyPrefix path flow.source flow.destination
  , remapPropertyPrefix path flow.destination flow.source
  ].filterMap id

end ValueFlow

/-- Add stable numeric identities to flow edges. Equal duplicate edges remain
    distinct, matching the production bit set. -/
def indexFlowsFrom : Nat → List ValueFlow → List (Nat × ValueFlow)
  | _, [] => []
  | index, flow :: rest =>
      (index, flow) :: indexFlowsFrom (index + 1) rest

/-- Add zero-based identities to all flow edges. -/
def indexFlows (flows : List ValueFlow) : List (Nat × ValueFlow) :=
  indexFlowsFrom 0 flows

/-- Enumerate paths reachable with at most `fuel` more edges. An edge identity
    cannot occur twice on one evidence path. -/
def reachableFlowPaths (flows : List ValueFlow) :
    Nat → List Nat → UsagePath → List UsagePath
  | 0, _, path => [path]
  | fuel + 1, used, path =>
      path :: (indexFlows flows).flatMap fun entry =>
        if used.contains entry.1 then []
        else
          (entry.2.remapBoth path).flatMap fun mapped =>
            reachableFlowPaths flows fuel (entry.1 :: used) mapped

/-- Record every reachable form of one original observation. -/
def propagateObservation (flows : List ValueFlow) (usage : Usage)
    (observation : Observation) : Usage :=
  (reachableFlowPaths flows flows.length [] observation.path).foldl
    (fun result path => result.record path observation.mode) usage

/-- Apply all value flows to the observations present before propagation.
    Newly recorded observations do not start a second unbounded pass. -/
def applyValueFlows (usage : Usage) (flows : List ValueFlow) : Usage :=
  usage.observations.foldl (propagateObservation flows) usage

/-- One direct indexed flow step. The relation states the intended prefix
    operation independently from the executable search. -/
inductive ValueFlowStep (flows : List ValueFlow) :
    UsagePath → UsagePath → Nat → Prop where
  | forward {path mapped index flow}
      (selected : (index, flow) ∈ indexFlows flows)
      (remapped : remapPropertyPrefix path flow.source flow.destination =
        some mapped) :
      ValueFlowStep flows path mapped index
  | backward {path mapped index flow}
      (selected : (index, flow) ∈ indexFlows flows)
      (remapped : remapPropertyPrefix path flow.destination flow.source =
        some mapped) :
      ValueFlowStep flows path mapped index

/-- A bounded propagation journey. `fuel` counts the available search steps.
    `used` prevents one edge identity from occurring twice. -/
inductive ValueFlowJourney (flows : List ValueFlow) :
    Nat → List Nat → UsagePath → UsagePath → Prop where
  | refl (fuel : Nat) (used : List Nat) (path : UsagePath) :
      ValueFlowJourney flows fuel used path path
  | next {fuel : Nat} {used : List Nat}
      {source middle destination : UsagePath}
      {index : Nat}
      (fresh : index ∉ used)
      (step : ValueFlowStep flows source middle index)
      (tail : ValueFlowJourney flows fuel (index :: used) middle destination) :
      ValueFlowJourney flows (fuel + 1) used source destination

/-- One observation can flow to another when their modes are equal and their
    paths are connected without reusing an edge identity. -/
def ObservationFlows (flows : List ValueFlow)
    (source destination : Observation) : Prop :=
  source.mode = destination.mode ∧
    ValueFlowJourney flows flows.length [] source.path destination.path

end HelmSchema
