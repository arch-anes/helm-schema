import HelmSchema.Flow

set_option autoImplicit false

namespace HelmSchema.Proofs.Flow

open HelmSchema

/-- Removing a prefix from that exact prefix followed by a suffix returns the
    suffix. The suffix can contain property, additional, item, or element
    segments. -/
theorem strip_exact_prefix (names : List String) (suffix : UsagePath) :
    stripPropertyPrefix (propertySegments names ++ suffix) names =
      some suffix := by
  induction names with
  | nil =>
      rw [propertySegments, List.map_nil, List.nil_append,
        stripPropertyPrefix.eq_def]
  | cons name rest induction =>
      rw [propertySegments, List.map_cons, List.cons_append,
        stripPropertyPrefix.eq_def]
      simp only [FlowName.equal_self, if_true]
      exact induction

/-- Prefix remapping changes only the fixed prefix. -/
theorem remap_preserves_suffix (sourceNames destinationNames : List String)
    (suffix : UsagePath) :
    remapPropertyPrefix (propertySegments sourceNames ++ suffix)
      sourceNames destinationNames =
      some (propertySegments destinationNames ++ suffix) := by
  simp [remapPropertyPrefix, strip_exact_prefix]

/-- Every reachable-path enumeration retains its input path. -/
theorem reachable_retains_source (flows : List ValueFlow) (fuel : Nat)
    (used : List Nat) (path : UsagePath) :
    path ∈ reachableFlowPaths flows fuel used path := by
  cases fuel <;> simp [reachableFlowPaths]

/-- A relational flow step is one of the direct remappings enumerated by the
    corresponding indexed executable edge. -/
theorem step_is_enumerated {flows : List ValueFlow}
    {source destination : UsagePath} {index : Nat}
    (step : ValueFlowStep flows source destination index) :
    ∃ flow, (index, flow) ∈ indexFlows flows ∧
      destination ∈ flow.remapBoth source := by
  cases step with
  | forward selected remapped =>
      refine ⟨_, selected, ?_⟩
      simp [ValueFlow.remapBoth, remapped]
  | backward selected remapped =>
      refine ⟨_, selected, ?_⟩
      simp [ValueFlow.remapBoth, remapped]

/-- Every direct remapping from an indexed executable edge is a relational
    flow step. -/
theorem enumerated_is_step {flows : List ValueFlow}
    {source destination : UsagePath} {index : Nat} {flow : ValueFlow}
    (selected : (index, flow) ∈ indexFlows flows)
    (mapped : destination ∈ flow.remapBoth source) :
    ValueFlowStep flows source destination index := by
  cases forward : remapPropertyPrefix source flow.source flow.destination with
  | none =>
      cases backward : remapPropertyPrefix source flow.destination flow.source with
      | none =>
          simp [ValueFlow.remapBoth, forward, backward] at mapped
      | some backwardPath =>
          simp [ValueFlow.remapBoth, forward, backward] at mapped
          subst destination
          exact ValueFlowStep.backward selected backward
  | some forwardPath =>
      cases backward : remapPropertyPrefix source flow.destination flow.source with
      | none =>
          simp [ValueFlow.remapBoth, forward, backward] at mapped
          subst destination
          exact ValueFlowStep.forward selected forward
      | some backwardPath =>
          simp [ValueFlow.remapBoth, forward, backward] at mapped
          rcases mapped with mapped | mapped
          · subst destination
            exact ValueFlowStep.forward selected forward
          · subst destination
            exact ValueFlowStep.backward selected backward

/-- Every bounded relational journey occurs in the executable path search. -/
theorem journey_reachable {flows : List ValueFlow} {fuel : Nat}
    {used : List Nat} {source destination : UsagePath}
    (journey : ValueFlowJourney flows fuel used source destination) :
    destination ∈ reachableFlowPaths flows fuel used source := by
  induction journey with
  | refl fuel used path =>
      exact reachable_retains_source flows fuel used path
  | @next fuel used source middle destination index fresh step tail induction =>
      obtain ⟨flow, indexed, mapped⟩ := step_is_enumerated step
      simp only [reachableFlowPaths, List.mem_cons]
      right
      apply List.mem_flatMap.mpr
      refine ⟨(index, flow), indexed, ?_⟩
      simp only [fresh, List.contains_eq_mem, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      apply List.mem_flatMap.mpr
      exact ⟨middle, mapped, induction⟩

/-- Every path returned by the executable search has a matching bounded
    relational journey. -/
theorem reachable_is_journey {flows : List ValueFlow} {fuel : Nat}
    {used : List Nat} {source destination : UsagePath}
    (reachable : destination ∈ reachableFlowPaths flows fuel used source) :
    ValueFlowJourney flows fuel used source destination := by
  induction fuel generalizing used source with
  | zero =>
      simp [reachableFlowPaths] at reachable
      subst destination
      exact ValueFlowJourney.refl 0 used source
  | succ fuel induction =>
      simp only [reachableFlowPaths, List.mem_cons] at reachable
      rcases reachable with equal | reached
      · subst destination
        exact ValueFlowJourney.refl (fuel + 1) used source
      · rcases List.mem_flatMap.mp reached with
          ⟨⟨index, flow⟩, selected, reached⟩
        have active : index ∉ used ∧ destination ∈
            (flow.remapBoth source).flatMap (fun mapped =>
              reachableFlowPaths flows fuel (index :: used) mapped) := by
          simpa [List.contains_eq_mem] using reached
        rcases active with ⟨fresh, active⟩
        rcases List.mem_flatMap.mp active with ⟨middle, mapped, tail⟩
        exact ValueFlowJourney.next fresh
          (enumerated_is_step selected mapped) (induction tail)

/-- The executable search and the independent journey relation permit the
    same paths for each fuel value and used-edge list. -/
theorem reachable_iff_journey {flows : List ValueFlow} {fuel : Nat}
    {used : List Nat} {source destination : UsagePath} :
    destination ∈ reachableFlowPaths flows fuel used source ↔
      ValueFlowJourney flows fuel used source destination :=
  ⟨reachable_is_journey, journey_reachable⟩

/-- Every relational observation flow occurs in the executable path search. -/
theorem observation_flow_reachable {flows : List ValueFlow}
    {source destination : Observation}
    (flowed : ObservationFlows flows source destination) :
    destination.path ∈
      reachableFlowPaths flows flows.length [] source.path :=
  journey_reachable flowed.2

/-- A single flow maps every source suffix to the same destination suffix. -/
theorem one_flow_forward (flow : ValueFlow) (suffix : UsagePath) :
    ValueFlowJourney [flow] 1 []
      (propertySegments flow.source ++ suffix)
      (propertySegments flow.destination ++ suffix) := by
  apply ValueFlowJourney.next (index := 0)
  · simp
  · apply ValueFlowStep.forward (flow := flow)
    · simp [indexFlows, indexFlowsFrom]
    · exact remap_preserves_suffix flow.source flow.destination suffix
  · exact ValueFlowJourney.refl 0 [0]
      (propertySegments flow.destination ++ suffix)

/-- Dependency value copies are bidirectional for validation evidence. -/
theorem one_flow_backward (flow : ValueFlow) (suffix : UsagePath) :
    ValueFlowJourney [flow] 1 []
      (propertySegments flow.destination ++ suffix)
      (propertySegments flow.source ++ suffix) := by
  apply ValueFlowJourney.next (index := 0)
  · simp
  · apply ValueFlowStep.backward (flow := flow)
    · simp [indexFlows, indexFlowsFrom]
    · exact remap_preserves_suffix flow.destination flow.source suffix
  · exact ValueFlowJourney.refl 0 [0]
      (propertySegments flow.source ++ suffix)

/-- Two distinct dependency copies propagate evidence transitively. -/
theorem two_flow_forward (first second : ValueFlow)
    (connected : first.destination = second.source) (suffix : UsagePath) :
    ValueFlowJourney [first, second] 2 []
      (propertySegments first.source ++ suffix)
      (propertySegments second.destination ++ suffix) := by
  apply ValueFlowJourney.next (index := 0)
  · simp
  · apply ValueFlowStep.forward (flow := first)
    · simp [indexFlows, indexFlowsFrom]
    · exact remap_preserves_suffix first.source first.destination suffix
  · apply ValueFlowJourney.next (index := 1)
    · simp
    · apply ValueFlowStep.forward (flow := second)
      · simp [indexFlows, indexFlowsFrom]
      · rw [← connected]
        exact remap_preserves_suffix first.destination second.destination suffix
    · exact ValueFlowJourney.refl 0 [1, 0]
        (propertySegments second.destination ++ suffix)

/-- Flow propagation never changes the observation mode. -/
theorem observation_mode_preserved {flows : List ValueFlow}
    {source destination : Observation}
    (flowed : ObservationFlows flows source destination) :
    source.mode = destination.mode :=
  flowed.1

/-- Every observation flows to itself without using a dependency edge. -/
theorem observation_flow_reflexive (flows : List ValueFlow)
    (observation : Observation) :
    ObservationFlows flows observation observation :=
  ⟨rfl, ValueFlowJourney.refl flows.length [] observation.path⟩

/-- Recording a list of propagated paths does not remove an observation that
    was already present. -/
theorem record_paths_preserves (paths : List UsagePath) (usage : Usage)
    (mode : UsageMode) (observation : Observation)
    (present : usage.contains observation) :
    (paths.foldl (fun result path =>
      result.record path mode) usage).contains observation := by
  induction paths generalizing usage with
  | nil => exact present
  | cons path rest induction =>
      apply induction
      exact Usage.contains_record usage path mode observation |>.2
        (Or.inr present)

/-- Recording every path in a list records each path in that list with the
    requested mode. Later records do not remove the observation. -/
theorem record_paths_contains (paths : List UsagePath) (usage : Usage)
    (mode : UsageMode) (path : UsagePath) (member : path ∈ paths) :
    (paths.foldl (fun result current =>
      result.record current mode) usage).contains { path := path, mode := mode } := by
  induction paths generalizing usage with
  | nil => simp at member
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst head
        exact record_paths_preserves rest (usage.record path mode) mode
          { path := path, mode := mode }
          (Usage.record_contains_mode usage path mode)
      · exact induction (usage := usage.record head mode) member

/-- Every observation present after a path fold was either present before the
    fold or was recorded at one of the requested paths. -/
theorem record_paths_origin (paths : List UsagePath) (usage : Usage)
    (mode : UsageMode) (observation : Observation)
    (present : (paths.foldl (fun result path =>
      result.record path mode) usage).contains observation) :
    usage.contains observation ∨
      ∃ path ∈ paths, observation ∈ mode.recorded.map
        (fun recordedMode => { path := path, mode := recordedMode }) := by
  induction paths generalizing usage with
  | nil => exact Or.inl present
  | cons head rest induction =>
      rcases induction (usage := usage.record head mode) present with
        recorded | ⟨path, member, recorded⟩
      · rcases (Usage.contains_record usage head mode observation).1 recorded with
          added | old
        · exact Or.inr ⟨head, by simp, added⟩
        · exact Or.inl old
      · exact Or.inr ⟨path, by simp [member], recorded⟩

/-- Propagating a fixed list of source observations preserves every
    observation already present in the input usage. -/
theorem propagate_observations_preserves (flows : List ValueFlow)
    (observations : List Observation) (usage : Usage)
    (observation : Observation) (present : usage.contains observation) :
    (observations.foldl (propagateObservation flows) usage).contains observation := by
  induction observations generalizing usage with
  | nil => exact present
  | cons current rest induction =>
      apply induction
      simpa [propagateObservation] using record_paths_preserves
        (reachableFlowPaths flows flows.length [] current.path)
        usage current.mode observation present

/-- If an original observation can reach a path in the executable flow
    search, folding propagation over the original observations records that
    path with the same mode. -/
theorem propagate_observations_contains (flows : List ValueFlow)
    (observations : List Observation) (usage : Usage)
    (source : Observation) (destination : UsagePath)
    (sourceMember : source ∈ observations)
    (reachable : destination ∈
      reachableFlowPaths flows flows.length [] source.path) :
    (observations.foldl (propagateObservation flows) usage).contains
      { path := destination, mode := source.mode } := by
  induction observations generalizing usage with
  | nil => simp at sourceMember
  | cons current rest induction =>
      simp only [List.mem_cons] at sourceMember
      rcases sourceMember with equal | sourceMember
      · subst current
        exact propagate_observations_preserves flows rest
          (propagateObservation flows usage source)
          { path := destination, mode := source.mode }
          (record_paths_contains
            (reachableFlowPaths flows flows.length [] source.path)
            usage source.mode destination reachable)
      · exact induction (usage := propagateObservation flows usage current)
          sourceMember

/-- Every observation present after a propagation fold comes from the input
    usage or from one source observation and one reachable path. -/
theorem propagate_observations_origin (flows : List ValueFlow)
    (observations : List Observation) (usage : Usage)
    (destination : Observation)
    (present : (observations.foldl (propagateObservation flows) usage).contains
      destination) :
    usage.contains destination ∨
      ∃ source ∈ observations, ∃ path ∈
        reachableFlowPaths flows flows.length [] source.path,
        destination ∈ source.mode.recorded.map
          (fun recordedMode => { path := path, mode := recordedMode }) := by
  induction observations generalizing usage with
  | nil => exact Or.inl present
  | cons current rest induction =>
      rcases induction (usage := propagateObservation flows usage current)
          present with fromCurrent | ⟨source, sourceMember, path,
            reachable, recorded⟩
      · have origin := record_paths_origin
          (reachableFlowPaths flows flows.length [] current.path)
          usage current.mode destination (by
            simpa [propagateObservation] using fromCurrent)
        rcases origin with old | ⟨path, reachable, recorded⟩
        · exact Or.inl old
        · exact Or.inr ⟨current, by simp, path, reachable, recorded⟩
      · exact Or.inr ⟨source, by simp [sourceMember], path,
          reachable, recorded⟩

/-- Recording one mode always records that same mode. -/
theorem mode_occurs_in_recorded (mode : UsageMode) :
    mode ∈ mode.recorded := by
  cases mode <;> simp [UsageMode.recorded]

/-- The executable dependency-flow pass records every path returned by its
    bounded flow search for every original observation. -/
theorem apply_records_reachable (usage : Usage) (flows : List ValueFlow)
    (source : Observation) (destination : UsagePath)
    (present : usage.contains source)
    (reachable : destination ∈
      reachableFlowPaths flows flows.length [] source.path) :
    (applyValueFlows usage flows).contains
      { path := destination, mode := source.mode } := by
  unfold applyValueFlows
  exact propagate_observations_contains flows usage.observations usage
    source destination present reachable

/-- The executable dependency-flow pass records every observation permitted
    by the independent finite-journey relation, including transitive journeys
    of any length up to the number of distinct flow edges. -/
theorem apply_records_observation_flow (usage : Usage)
    (flows : List ValueFlow) (source destination : Observation)
    (present : usage.contains source)
    (flowed : ObservationFlows flows source destination) :
    (applyValueFlows usage flows).contains destination := by
  have recorded := apply_records_reachable usage flows source destination.path
    present (observation_flow_reachable flowed)
  simpa [flowed.1] using recorded

/-- Every output observation comes from an original observation and a valid
    bounded journey. An open source can also produce its required read fact. -/
theorem apply_observation_has_source (usage : Usage) (flows : List ValueFlow)
    (destination : Observation)
    (present : (applyValueFlows usage flows).contains destination) :
    ∃ source, usage.contains source ∧
      ValueFlowJourney flows flows.length []
        source.path destination.path ∧
      destination.mode ∈ source.mode.recorded := by
  unfold applyValueFlows at present
  rcases propagate_observations_origin flows usage.observations usage
      destination present with old | ⟨source, sourceMember, path,
        reachable, recorded⟩
  · exact ⟨destination, old,
      ValueFlowJourney.refl flows.length [] destination.path,
      mode_occurs_in_recorded destination.mode⟩
  · rcases List.mem_map.mp recorded with
      ⟨recordedMode, modeMember, equal⟩
    cases equal
    exact ⟨source, sourceMember, reachable_is_journey reachable, modeMember⟩

/-- Applying dependency flows retains every original observation. -/
theorem apply_retains_observation (usage : Usage) (flows : List ValueFlow)
    (observation : Observation) (present : usage.contains observation) :
    (applyValueFlows usage flows).contains observation := by
  exact apply_records_reachable usage flows observation observation.path
    present (reachable_retains_source flows flows.length [] observation.path)

/-- The executable propagation pass copies an observation from one dependency
    prefix to the other and retains its complete suffix. -/
theorem apply_one_flow_forward (usage : Usage) (flow : ValueFlow)
    (suffix : UsagePath) (mode : UsageMode)
    (present : usage.contains
      { path := propertySegments flow.source ++ suffix, mode := mode }) :
    (applyValueFlows usage [flow]).contains
      { path := propertySegments flow.destination ++ suffix, mode := mode } := by
  apply apply_records_reachable usage [flow]
    { path := propertySegments flow.source ++ suffix, mode := mode }
  · exact present
  · simp [reachableFlowPaths, indexFlows, indexFlowsFrom,
      ValueFlow.remapBoth, remap_preserves_suffix]

/-- The executable propagation pass also copies validation evidence backward
    through a dependency value edge. -/
theorem apply_one_flow_backward (usage : Usage) (flow : ValueFlow)
    (suffix : UsagePath) (mode : UsageMode)
    (present : usage.contains
      { path := propertySegments flow.destination ++ suffix, mode := mode }) :
    (applyValueFlows usage [flow]).contains
      { path := propertySegments flow.source ++ suffix, mode := mode } := by
  apply apply_records_reachable usage [flow]
    { path := propertySegments flow.destination ++ suffix, mode := mode }
  · exact present
  · simp [reachableFlowPaths, indexFlows, indexFlowsFrom,
      ValueFlow.remapBoth, remap_preserves_suffix]

end HelmSchema.Proofs.Flow
