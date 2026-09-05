import HelmSchema.Json

set_option autoImplicit false

namespace HelmSchema

/-- One step through a normalized usage tree. -/
inductive UsageSegment where
  | property (name : String)
  | additional
  | items
  | elements
  deriving BEq, DecidableEq, Repr

/-- One way in which a template can observe a value. -/
inductive UsageMode where
  | read
  | exact
  | open
  | allowUnknown
  | iterate
  deriving BEq, DecidableEq, Repr

namespace UsageMode

/-- The raw flags created by recording one observation. Complete consumption
    records both a direct read and an open use. -/
def recorded : UsageMode → List UsageMode
  | .open => [.read, .open]
  | mode => [mode]

end UsageMode

/-- One path through a usage tree. -/
abbrev UsagePath := List UsageSegment

/-- One atomic observation from the production usage tree. -/
structure Observation where
  path : UsagePath
  mode : UsageMode
  deriving BEq, DecidableEq, Repr

/-- A normalized usage tree represented as two finite fact sets. `nodes`
    records every present non-root node, including empty nodes. The root is
    implicit. `observations` records the flags set at those nodes. Duplicate
    facts and list order have no semantic effect. -/
structure Usage where
  nodes : List UsagePath := []
  observations : List Observation := []
  deriving BEq, Repr

namespace Usage

/-- Empty usage has an implicit root and no non-root nodes or observations. -/
def empty : Usage := {}

/-- Report whether a node is present. The root node is always present. -/
def hasNode (usage : Usage) (path : UsagePath) : Prop :=
  path = [] ∨ path ∈ usage.nodes

/-- Report whether usage contains one observation. -/
def contains (usage : Usage) (observation : Observation) : Prop :=
  observation ∈ usage.observations

/-- Usage is well formed when every observation occurs at a present node. -/
def WellFormed (usage : Usage) : Prop :=
  ∀ observation, usage.contains observation → usage.hasNode observation.path

/-- Two usage values have the same node and observation facts. -/
def Equivalent (left right : Usage) : Prop :=
  (∀ path, left.hasNode path ↔ right.hasNode path) ∧
    (∀ observation, left.contains observation ↔ right.contains observation)

/-- Return every non-root prefix of a path, from shortest to longest. -/
def nonRootPrefixes : UsagePath → List UsagePath
  | [] => []
  | head :: tail =>
      [head] :: (nonRootPrefixes tail).map (fun suffix => head :: suffix)

/-- Record one observation and every tree node on its path. -/
def record (usage : Usage) (path : UsagePath) (mode : UsageMode) : Usage :=
  { nodes := nonRootPrefixes path ++ usage.nodes
  , observations := mode.recorded.map (fun recordedMode =>
      { path := path, mode := recordedMode }) ++ usage.observations
  }

/-- Merge retains every node and observation from both inputs. -/
def merge (left right : Usage) : Usage :=
  { nodes := left.nodes ++ right.nodes
  , observations := left.observations ++ right.observations
  }

/-- Restrict usage to a fixed property prefix and remove that prefix. -/
def belowProperties (usage : Usage) (propertyPath : List String) : Usage :=
  let segments := propertyPath.map UsageSegment.property
  let nodes := usage.nodes.filterMap fun path =>
    if segments.isPrefixOf path then
      let remainder := path.drop segments.length
      if remainder.isEmpty then none else some remainder
    else
      none
  let observations := usage.observations.filterMap fun observation =>
    if segments.isPrefixOf observation.path then
      some { observation with path := observation.path.drop segments.length }
    else
      none
  { nodes := nodes, observations := observations }

/-- No observation occurs in empty usage. -/
@[simp]
theorem contains_empty (observation : Observation) :
    ¬empty.contains observation := by
  simp [empty, contains]

/-- Only the implicit root node is present in empty usage. -/
@[simp]
theorem hasNode_empty (path : UsagePath) :
    empty.hasNode path ↔ path = [] := by
  simp [empty, hasNode]

/-- An observation occurs in a merge exactly when one input contains it. -/
@[simp]
theorem contains_merge (left right : Usage) (observation : Observation) :
    (left.merge right).contains observation ↔
      left.contains observation ∨ right.contains observation := by
  simp [merge, contains]

/-- A node occurs in a merge exactly when it occurs in one input. -/
@[simp]
theorem hasNode_merge (left right : Usage) (path : UsagePath) :
    (left.merge right).hasNode path ↔
      left.hasNode path ∨ right.hasNode path := by
  constructor
  · intro present
    rcases present with root | present
    · exact Or.inl (Or.inl root)
    · rcases List.mem_append.mp present with leftPresent | rightPresent
      · exact Or.inl (Or.inr leftPresent)
      · exact Or.inr (Or.inr rightPresent)
  · intro present
    rcases present with (root | leftPresent) | (root | rightPresent)
    · exact Or.inl root
    · exact Or.inr (List.mem_append.mpr (Or.inl leftPresent))
    · exact Or.inl root
    · exact Or.inr (List.mem_append.mpr (Or.inr rightPresent))

/-- Usage equivalence is reflexive. -/
theorem equivalent_refl (usage : Usage) : usage.Equivalent usage := by
  exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- Usage equivalence is symmetric. -/
theorem equivalent_symm {left right : Usage} (equal : left.Equivalent right) :
    right.Equivalent left := by
  exact
    ⟨ fun path => (equal.1 path).symm
    , fun observation => (equal.2 observation).symm
    ⟩

/-- Usage equivalence is transitive. -/
theorem equivalent_trans {first second third : Usage}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) :
    first.Equivalent third := by
  exact
    ⟨ fun path => (firstSecond.1 path).trans (secondThird.1 path)
    , fun observation =>
        (firstSecond.2 observation).trans (secondThird.2 observation)
    ⟩

/-- Merge is associative as list append in both fact collections. -/
theorem merge_associative (first second third : Usage) :
    (first.merge second).merge third = first.merge (second.merge third) := by
  simp [merge, List.append_assoc]

/-- Merge is commutative by node and observation membership. -/
theorem merge_commutative (left right : Usage) :
    (left.merge right).Equivalent (right.merge left) := by
  constructor
  · intro path
    simp [or_comm]
  · intro observation
    simp [or_comm]

/-- Repeated evidence does not change usage meaning. -/
theorem merge_idempotent (usage : Usage) :
    (usage.merge usage).Equivalent usage := by
  constructor <;> intro value <;> simp

/-- Empty usage is the left identity for merge. -/
@[simp]
theorem merge_empty_left (usage : Usage) : empty.merge usage = usage := by
  simp [empty, merge]

/-- Empty usage is the right identity for merge. -/
@[simp]
theorem merge_empty_right (usage : Usage) : usage.merge empty = usage := by
  simp [empty, merge]

/-- Merge retains each observation from its left input. -/
theorem left_contained_in_merge (left right : Usage) (observation : Observation)
    (present : left.contains observation) :
    (left.merge right).contains observation := by
  exact contains_merge left right observation |>.2 (Or.inl present)

/-- Merge retains each observation from its right input. -/
theorem right_contained_in_merge (left right : Usage) (observation : Observation)
    (present : right.contains observation) :
    (left.merge right).contains observation := by
  exact contains_merge left right observation |>.2 (Or.inr present)

/-- Merge retains each node from its left input. -/
theorem left_node_in_merge (left right : Usage) (path : UsagePath)
    (present : left.hasNode path) :
    (left.merge right).hasNode path := by
  exact hasNode_merge left right path |>.2 (Or.inl present)

/-- Merge retains each node from its right input. -/
theorem right_node_in_merge (left right : Usage) (path : UsagePath)
    (present : right.hasNode path) :
    (left.merge right).hasNode path := by
  exact hasNode_merge left right path |>.2 (Or.inr present)

/-- Every non-empty path occurs in its list of non-root prefixes. -/
theorem self_mem_nonRootPrefixes {path : UsagePath} (notRoot : path ≠ []) :
    path ∈ nonRootPrefixes path := by
  induction path with
  | nil => exact False.elim (notRoot rfl)
  | cons head tail induction =>
      cases tail with
      | nil => simp [nonRootPrefixes]
      | cons next rest =>
          simp only [nonRootPrefixes, List.mem_cons]
          apply Or.inr
          apply List.mem_map.mpr
          exact ⟨next :: rest, induction (by simp), rfl⟩

/-- An observation occurs after recording exactly when it was newly recorded
    or already occurred in the input. -/
@[simp]
theorem contains_record (usage : Usage) (path : UsagePath) (mode : UsageMode)
    (observation : Observation) :
    (usage.record path mode).contains observation ↔
      observation ∈ mode.recorded.map (fun recordedMode =>
        { path := path, mode := recordedMode }) ∨
      usage.contains observation := by
  simp [record, contains]

/-- A node occurs after recording exactly when it already occurred or is one
    of the newly materialized non-root path prefixes. -/
@[simp]
theorem hasNode_record (usage : Usage) (path target : UsagePath)
    (mode : UsageMode) :
    (usage.record path mode).hasNode target ↔
      usage.hasNode target ∨ target ∈ nonRootPrefixes path := by
  constructor
  · intro present
    rcases present with root | present
    · exact Or.inl (Or.inl root)
    · rcases List.mem_append.mp present with newNode | old
      · exact Or.inr newNode
      · exact Or.inl (Or.inr old)
  · intro present
    rcases present with (root | old) | newNode
    · exact Or.inl root
    · exact Or.inr (List.mem_append.mpr (Or.inr old))
    · exact Or.inr (List.mem_append.mpr (Or.inl newNode))

/-- Recording at a path makes the target node present. -/
theorem record_has_target_node (usage : Usage) (path : UsagePath)
    (mode : UsageMode) :
    (usage.record path mode).hasNode path := by
  by_cases root : path = []
  · exact Or.inl root
  · exact Or.inr (by
      simp [record, self_mem_nonRootPrefixes root])

/-- Recording does not remove an existing node. -/
theorem record_preserves_node (usage : Usage) (path target : UsagePath)
    (mode : UsageMode) (present : usage.hasNode target) :
    (usage.record path mode).hasNode target := by
  rcases present with root | present
  · exact Or.inl root
  · exact Or.inr (by simp [record, present])

/-- Recording creates the requested observation. -/
theorem record_contains_mode (usage : Usage) (path : UsagePath)
    (mode : UsageMode) :
    (usage.record path mode).contains { path := path, mode := mode } := by
  cases mode <;> simp [record, contains, UsageMode.recorded]

/-- Recording open usage also records a direct read. -/
theorem record_open_records_read (usage : Usage) (path : UsagePath) :
    (usage.record path .open).contains { path := path, mode := .read } := by
  simp [record, contains, UsageMode.recorded]

/-- Recording open usage records the open observation. -/
theorem record_open_records_open (usage : Usage) (path : UsagePath) :
    (usage.record path .open).contains { path := path, mode := .open } := by
  simp [record, contains, UsageMode.recorded]

/-- Empty usage satisfies the observation-to-node invariant. -/
theorem empty_wellFormed : empty.WellFormed := by
  intro observation present
  exact False.elim (contains_empty observation present)

/-- Recording preserves the observation-to-node invariant. -/
theorem record_wellFormed {usage : Usage} (valid : usage.WellFormed)
    (path : UsagePath) (mode : UsageMode) :
    (usage.record path mode).WellFormed := by
  intro observation present
  simp only [record, contains, List.mem_append, List.mem_map] at present
  rcases present with ⟨recordedMode, _, rfl⟩ | old
  · exact record_has_target_node usage path mode
  · exact record_preserves_node usage path observation.path mode
      (valid observation old)

/-- Merge preserves the observation-to-node invariant. -/
theorem merge_wellFormed {left right : Usage}
    (leftValid : left.WellFormed) (rightValid : right.WellFormed) :
    (left.merge right).WellFormed := by
  intro observation present
  rcases (contains_merge left right observation).1 present with leftPresent | rightPresent
  · exact left_node_in_merge left right observation.path
      (leftValid observation leftPresent)
  · exact right_node_in_merge left right observation.path
      (rightValid observation rightPresent)

end Usage

/-- The recursive usage tree transferred from Go. This type contains no schema
    decisions. In particular, an empty value inside `additional`, `items`,
    `elements`, or `properties` remains a present node. -/
structure RawUsage where
  isRead : Bool := false
  isExact : Bool := false
  allowsUnknown : Bool := false
  isOpen : Bool := false
  isIterated : Bool := false
  properties : List (String × RawUsage) := []
  additional : Option RawUsage := none
  items : Option RawUsage := none
  elements : Option RawUsage := none
  deriving BEq, Repr

namespace RawUsage

/-- Create the observations set directly on one raw node. -/
def observationsAt (path : UsagePath) (usage : RawUsage) : List Observation :=
  [ (usage.isRead, UsageMode.read)
  , (usage.isExact, UsageMode.exact)
  , (usage.isOpen, UsageMode.open)
  , (usage.allowsUnknown, UsageMode.allowUnknown)
  , (usage.isIterated, UsageMode.iterate)
  ].filterMap fun entry =>
    if entry.1 then some { path := path, mode := entry.2 } else none

/-- Convert a raw recursive tree into order-insensitive proof facts. -/
def summarizeAt (path : UsagePath) (usage : RawUsage) : Usage :=
  let here : Usage :=
    { nodes := if path.isEmpty then [] else [path]
    , observations := observationsAt path usage
    }
  let properties := usage.properties.foldl
    (fun result property =>
      result.merge (summarizeAt (path ++ [.property property.1]) property.2))
    Usage.empty
  let additional := match _additionalEq : usage.additional with
    | none => Usage.empty
    | some child => summarizeAt (path ++ [.additional]) child
  let items := match _itemsEq : usage.items with
    | none => Usage.empty
    | some child => summarizeAt (path ++ [.items]) child
  let elements := match _elementsEq : usage.elements with
    | none => Usage.empty
    | some child => summarizeAt (path ++ [.elements]) child
  here.merge properties |>.merge additional |>.merge items |>.merge elements
termination_by sizeOf usage
decreasing_by
  · have childPair : sizeOf property.2 < sizeOf property := by
      cases property
      simp
      omega
    have pairList : sizeOf property < sizeOf usage.properties :=
      List.sizeOf_lt_of_mem (by assumption)
    have listParent : sizeOf usage.properties < sizeOf usage := by
      cases usage
      simp
      omega
    exact Nat.lt_trans childPair (Nat.lt_trans pairList listParent)
  · have childOption : sizeOf child < sizeOf usage.additional := by
      rw [_additionalEq]
      simp
    have optionParent : sizeOf usage.additional < sizeOf usage := by
      cases usage
      simp
      omega
    exact Nat.lt_trans childOption optionParent
  · have childOption : sizeOf child < sizeOf usage.items := by
      rw [_itemsEq]
      simp
    have optionParent : sizeOf usage.items < sizeOf usage := by
      cases usage
      simp
      omega
    exact Nat.lt_trans childOption optionParent
  · have childOption : sizeOf child < sizeOf usage.elements := by
      rw [_elementsEq]
      simp
    have optionParent : sizeOf usage.elements < sizeOf usage := by
      cases usage
      simp
      omega
    exact Nat.lt_trans childOption optionParent

/-- Normalize one complete raw usage tree. -/
def summarize (usage : RawUsage) : Usage := summarizeAt [] usage

/-- Normalizing a raw node at a non-root path preserves that node even when
    the node has no flags or descendants. -/
theorem summarizeAt_has_current_node (path : UsagePath) (usage : RawUsage)
    (notRoot : path ≠ []) :
    (summarizeAt path usage).hasNode path := by
  rw [summarizeAt.eq_def]
  apply Usage.left_node_in_merge
  apply Usage.left_node_in_merge
  apply Usage.left_node_in_merge
  apply Usage.left_node_in_merge
  exact Or.inr (by simp [notRoot])

/-- A present empty additional-property node remains present after raw-tree
    normalization. -/
theorem summarize_additional_present (usage child : RawUsage) :
    ({ usage with additional := some child }.summarize).hasNode [.additional] := by
  unfold summarize
  rw [summarizeAt.eq_def]
  apply Usage.left_node_in_merge
  apply Usage.left_node_in_merge
  apply Usage.right_node_in_merge
  exact summarizeAt_has_current_node [.additional] child (by simp)

/-- A present empty item node remains present after raw-tree normalization. -/
theorem summarize_items_present (usage child : RawUsage) :
    ({ usage with items := some child }.summarize).hasNode [.items] := by
  unfold summarize
  rw [summarizeAt.eq_def]
  apply Usage.left_node_in_merge
  apply Usage.right_node_in_merge
  exact summarizeAt_has_current_node [.items] child (by simp)

/-- A present empty shape-neutral element node remains present after raw-tree
    normalization. -/
theorem summarize_elements_present (usage child : RawUsage) :
    ({ usage with elements := some child }.summarize).hasNode [.elements] := by
  unfold summarize
  rw [summarizeAt.eq_def]
  apply Usage.right_node_in_merge
  exact summarizeAt_has_current_node [.elements] child (by simp)

end RawUsage

end HelmSchema
