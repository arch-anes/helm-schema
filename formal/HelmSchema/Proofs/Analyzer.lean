import HelmSchema.Analyze

set_option autoImplicit false

namespace HelmSchema.Proofs.Analyzer

open HelmSchema

/-- Every semantic key selection is represented by a fixed key or an exact
    dynamic classification. -/
theorem selected_key_covered {program : TemplateIR}
    {path : List UsageSegment} {name : String}
    (selected : SelectsKey program path name) :
    { path := path, name := name : SelectedKey } ∈ (analyze program).selectedKeys ∨
      DynamicAt program path := by
  induction selected with
  | fixed path name =>
      exact Or.inl (by simp [analyze, analyzeOperation])
  | finite path names name member =>
      exact Or.inl (by simp [analyze, analyzeOperation, member])
  | dynamic path name =>
      exact Or.inr (DynamicAt.dynamic path)
  | sequenceLeft selected induction =>
      cases induction with
      | inl fixed =>
          exact Or.inl (by simp [analyze, AnalysisResult.merge, fixed])
      | inr dynamic => exact Or.inr (DynamicAt.sequenceLeft dynamic)
  | sequenceRight selected induction =>
      cases induction with
      | inl fixed =>
          exact Or.inl (by simp [analyze, AnalysisResult.merge, fixed])
      | inr dynamic => exact Or.inr (DynamicAt.sequenceRight dynamic)
  | branchTrue selected induction =>
      cases induction with
      | inl fixed =>
          exact Or.inl (by simp [analyze, AnalysisResult.merge, fixed])
      | inr dynamic => exact Or.inr (DynamicAt.branchTrue dynamic)
  | branchFalse selected induction =>
      cases induction with
      | inl fixed =>
          exact Or.inl (by simp [analyze, AnalysisResult.merge, fixed])
      | inr dynamic => exact Or.inr (DynamicAt.branchFalse dynamic)

/-- Every reported fixed key has a semantic selection derivation. -/
theorem selected_key_justified {program : TemplateIR}
    {path : List UsageSegment} {name : String}
    (present : { path := path, name := name : SelectedKey } ∈
      (analyze program).selectedKeys) :
    StaticSelectsKey program path name := by
  induction program with
  | skip => simp [analyze] at present
  | operation operation =>
      cases operation with
      | selectFixed selectedPath selectedName =>
          simp [analyze, analyzeOperation] at present
          rcases present with ⟨rfl, rfl⟩
          exact StaticSelectsKey.fixed _ _
      | selectFinite selectedPath names =>
          simp [analyze, analyzeOperation] at present
          rcases present with ⟨member, rfl⟩
          exact StaticSelectsKey.finite _ _ _ member
      | selectDynamic path => simp [analyze, analyzeOperation] at present
      | read path => simp [analyze, analyzeOperation] at present
      | exact path => simp [analyze, analyzeOperation] at present
      | complete path => simp [analyze, analyzeOperation] at present
      | allowUnknown path => simp [analyze, analyzeOperation] at present
      | iterate path => simp [analyze, analyzeOperation] at present
      | unsupported path mode reason => simp [analyze, analyzeOperation] at present
  | sequence first second firstInduction secondInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl firstPresent =>
          exact StaticSelectsKey.sequenceLeft (firstInduction firstPresent)
      | inr secondPresent =>
          exact StaticSelectsKey.sequenceRight (secondInduction secondPresent)
  | branch whenTrue whenFalse trueInduction falseInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl truePresent =>
          exact StaticSelectsKey.branchTrue (trueInduction truePresent)
      | inr falsePresent =>
          exact StaticSelectsKey.branchFalse (falseInduction falsePresent)

/-- Every semantic dynamic selection has an exact dynamic evidence reason. -/
theorem dynamic_sound {program : TemplateIR} {path : List UsageSegment}
    (dynamic : DynamicAt program path) :
    { path := path, kind := EvidenceKind.dynamicSelection : EvidenceReason } ∈
      (analyze program).reasons := by
  induction dynamic with
  | dynamic path => simp [analyze, analyzeOperation]
  | sequenceLeft dynamic induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | sequenceRight dynamic induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | branchTrue dynamic induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | branchFalse dynamic induction =>
      simp [analyze, AnalysisResult.merge, induction]

/-- Every exact dynamic evidence reason has a semantic derivation. -/
theorem dynamic_justified {program : TemplateIR} {path : List UsageSegment}
    (present :
      { path := path, kind := EvidenceKind.dynamicSelection : EvidenceReason } ∈
        (analyze program).reasons) :
    DynamicAt program path := by
  induction program with
  | skip => simp [analyze] at present
  | operation operation =>
      cases operation with
      | selectFixed selectedPath selectedName =>
          simp [analyze, analyzeOperation] at present
      | selectFinite selectedPath names =>
          simp [analyze, analyzeOperation] at present
      | selectDynamic selectedPath =>
          simp [analyze, analyzeOperation] at present
          subst path
          exact DynamicAt.dynamic selectedPath
      | read selectedPath => simp [analyze, analyzeOperation] at present
      | exact selectedPath => simp [analyze, analyzeOperation] at present
      | complete selectedPath => simp [analyze, analyzeOperation] at present
      | allowUnknown selectedPath => simp [analyze, analyzeOperation] at present
      | iterate selectedPath => simp [analyze, analyzeOperation] at present
      | unsupported selectedPath mode reason =>
          simp [analyze, analyzeOperation] at present
  | sequence first second firstInduction secondInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl firstPresent =>
          exact DynamicAt.sequenceLeft (firstInduction firstPresent)
      | inr secondPresent =>
          exact DynamicAt.sequenceRight (secondInduction secondPresent)
  | branch whenTrue whenFalse trueInduction falseInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl truePresent =>
          exact DynamicAt.branchTrue (trueInduction truePresent)
      | inr falsePresent =>
          exact DynamicAt.branchFalse (falseInduction falsePresent)

/-- Every semantic complete consumer has an exact open evidence reason. -/
theorem open_sound {program : TemplateIR} {path : List UsageSegment}
    (openUse : OpenAt program path) :
    { path := path, kind := EvidenceKind.completeConsumption : EvidenceReason } ∈
      (analyze program).reasons := by
  induction openUse with
  | complete path => simp [analyze, analyzeOperation]
  | sequenceLeft openUse induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | sequenceRight openUse induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | branchTrue openUse induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | branchFalse openUse induction =>
      simp [analyze, AnalysisResult.merge, induction]

/-- Every exact open evidence reason has a semantic derivation. -/
theorem open_justified {program : TemplateIR} {path : List UsageSegment}
    (present :
      { path := path, kind := EvidenceKind.completeConsumption : EvidenceReason } ∈
        (analyze program).reasons) :
    OpenAt program path := by
  induction program with
  | skip => simp [analyze] at present
  | operation operation =>
      cases operation with
      | selectFixed selectedPath selectedName =>
          simp [analyze, analyzeOperation] at present
      | selectFinite selectedPath names =>
          simp [analyze, analyzeOperation] at present
      | selectDynamic selectedPath => simp [analyze, analyzeOperation] at present
      | read selectedPath => simp [analyze, analyzeOperation] at present
      | exact selectedPath => simp [analyze, analyzeOperation] at present
      | complete selectedPath =>
          simp [analyze, analyzeOperation] at present
          subst path
          exact OpenAt.complete selectedPath
      | allowUnknown selectedPath => simp [analyze, analyzeOperation] at present
      | iterate selectedPath => simp [analyze, analyzeOperation] at present
      | unsupported selectedPath mode reason =>
          simp [analyze, analyzeOperation] at present
  | sequence first second firstInduction secondInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl firstPresent => exact OpenAt.sequenceLeft (firstInduction firstPresent)
      | inr secondPresent => exact OpenAt.sequenceRight (secondInduction secondPresent)
  | branch whenTrue whenFalse trueInduction falseInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl truePresent => exact OpenAt.branchTrue (trueInduction truePresent)
      | inr falsePresent => exact OpenAt.branchFalse (falseInduction falsePresent)

/-- Every modeled unsupported operation has its conservative evidence reason. -/
theorem unsupported_sound {program : TemplateIR} {path : List UsageSegment}
    {mode : UsageMode} {reason : FallbackReason}
    (unsupported : UnsupportedAt program path mode reason) :
    { path := path, kind := EvidenceKind.conservativeFallback reason mode :
      EvidenceReason } ∈ (analyze program).reasons := by
  induction unsupported with
  | unsupported path mode reason => simp [analyze, analyzeOperation]
  | sequenceLeft unsupported induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | sequenceRight unsupported induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | branchTrue unsupported induction =>
      simp [analyze, AnalysisResult.merge, induction]
  | branchFalse unsupported induction =>
      simp [analyze, AnalysisResult.merge, induction]

/-- Every conservative evidence reason has a modeled unsupported operation. -/
theorem unsupported_justified {program : TemplateIR} {path : List UsageSegment}
    {mode : UsageMode} {reason : FallbackReason}
    (present :
      { path := path, kind := EvidenceKind.conservativeFallback reason mode :
        EvidenceReason } ∈ (analyze program).reasons) :
    UnsupportedAt program path mode reason := by
  induction program with
  | skip => simp [analyze] at present
  | operation operation =>
      cases operation with
      | selectFixed selectedPath selectedName =>
          simp [analyze, analyzeOperation] at present
      | selectFinite selectedPath names =>
          simp [analyze, analyzeOperation] at present
      | selectDynamic selectedPath => simp [analyze, analyzeOperation] at present
      | read selectedPath => simp [analyze, analyzeOperation] at present
      | exact selectedPath => simp [analyze, analyzeOperation] at present
      | complete selectedPath => simp [analyze, analyzeOperation] at present
      | allowUnknown selectedPath => simp [analyze, analyzeOperation] at present
      | iterate selectedPath => simp [analyze, analyzeOperation] at present
      | unsupported selectedPath selectedMode selectedReason =>
          simp [analyze, analyzeOperation] at present
          rcases present with ⟨rfl, rfl, rfl⟩
          exact UnsupportedAt.unsupported _ _ _
  | sequence first second firstInduction secondInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl firstPresent =>
          exact UnsupportedAt.sequenceLeft (firstInduction firstPresent)
      | inr secondPresent =>
          exact UnsupportedAt.sequenceRight (secondInduction secondPresent)
  | branch whenTrue whenFalse trueInduction falseInduction =>
      simp [analyze, AnalysisResult.merge] at present
      cases present with
      | inl truePresent =>
          exact UnsupportedAt.branchTrue (trueInduction truePresent)
      | inr falsePresent =>
          exact UnsupportedAt.branchFalse (falseInduction falsePresent)

/-- One operation's executable analysis contains exactly the observations in
    the independent operation specification. -/
theorem analyzeOperation_observations_iff (operation : TemplateOperation)
    (observation : Observation) :
    (analyzeOperation operation).usage.contains observation ↔
      observation ∈ operation.observations := by
  cases operation with
  | selectFixed path name => simp [analyzeOperation, TemplateOperation.observations]
  | selectFinite path names => simp [analyzeOperation, TemplateOperation.observations]
  | selectDynamic path => simp [analyzeOperation, TemplateOperation.observations]
  | read path =>
      simp [analyzeOperation, TemplateOperation.observations, Usage.record,
        Usage.contains, Usage.empty, UsageMode.recorded]
  | exact path =>
      simp [analyzeOperation, TemplateOperation.observations, Usage.record,
        Usage.contains, Usage.empty, UsageMode.recorded]
  | complete path =>
      simp [analyzeOperation, TemplateOperation.observations, Usage.record,
        Usage.contains, Usage.empty, UsageMode.recorded]
  | allowUnknown path =>
      simp [analyzeOperation, TemplateOperation.observations, Usage.record,
        Usage.contains, Usage.empty, UsageMode.recorded]
  | iterate path =>
      simp [analyzeOperation, TemplateOperation.observations, Usage.record,
        Usage.contains, Usage.empty, UsageMode.recorded]
  | unsupported path mode reason =>
      cases mode <;>
        simp [analyzeOperation, TemplateOperation.observations, Usage.record,
          Usage.contains, Usage.empty, UsageMode.recorded]

/-- The executable analyzer reports an observation exactly when the independent
    program specification creates it. -/
theorem analyze_observations_iff (program : TemplateIR)
    (observation : Observation) :
    (analyze program).usage.contains observation ↔
      ProgramObserves program observation := by
  induction program with
  | skip => simp [analyze, ProgramObserves]
  | operation operation =>
      exact analyzeOperation_observations_iff operation observation
  | sequence first second firstInduction secondInduction =>
      simp [analyze, AnalysisResult.merge, ProgramObserves,
        firstInduction, secondInduction]
  | branch whenTrue whenFalse trueInduction falseInduction =>
      simp [analyze, AnalysisResult.merge, ProgramObserves,
        trueInduction, falseInduction]

/-- One operation's executable analysis contains exactly its non-root path
    nodes, in addition to the implicit root. -/
theorem analyzeOperation_nodes_iff (operation : TemplateOperation)
    (path : UsagePath) :
    (analyzeOperation operation).usage.hasNode path ↔
      path = [] ∨ path ∈ operation.nodes := by
  cases operation with
  | selectFixed selectedPath name =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations]
  | selectFinite selectedPath names =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations]
  | selectDynamic selectedPath =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations]
  | read selectedPath =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations, Usage.record, Usage.hasNode,
        Usage.empty, UsageMode.recorded]
  | exact selectedPath =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations, Usage.record, Usage.hasNode,
        Usage.empty, UsageMode.recorded]
  | complete selectedPath =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations, Usage.record, Usage.hasNode,
        Usage.empty, UsageMode.recorded]
  | allowUnknown selectedPath =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations, Usage.record, Usage.hasNode,
        Usage.empty, UsageMode.recorded]
  | iterate selectedPath =>
      simp [analyzeOperation, TemplateOperation.nodes,
        TemplateOperation.observations, Usage.record, Usage.hasNode,
        Usage.empty, UsageMode.recorded]
  | unsupported selectedPath mode reason =>
      cases mode <;>
        simp [analyzeOperation, TemplateOperation.nodes,
          TemplateOperation.observations, Usage.record, Usage.hasNode,
          Usage.empty, UsageMode.recorded]

/-- The executable analyzer contains a node exactly when it is the implicit
    root or the independent program specification creates it. -/
theorem analyze_nodes_iff (program : TemplateIR) (path : UsagePath) :
    (analyze program).usage.hasNode path ↔
      path = [] ∨ ProgramCreatesNode program path := by
  induction program with
  | skip => simp [analyze, ProgramCreatesNode]
  | operation operation => exact analyzeOperation_nodes_iff operation path
  | sequence first second firstInduction secondInduction =>
      simp only [analyze, AnalysisResult.merge, Usage.hasNode_merge,
        firstInduction, secondInduction, ProgramCreatesNode]
      constructor
      · intro present
        rcases present with (root | firstNode) | (root | secondNode)
        · exact Or.inl root
        · exact Or.inr (Or.inl firstNode)
        · exact Or.inl root
        · exact Or.inr (Or.inr secondNode)
      · intro present
        rcases present with root | firstNode | secondNode
        · exact Or.inl (Or.inl root)
        · exact Or.inl (Or.inr firstNode)
        · exact Or.inr (Or.inr secondNode)
  | branch whenTrue whenFalse trueInduction falseInduction =>
      simp only [analyze, AnalysisResult.merge, Usage.hasNode_merge,
        trueInduction, falseInduction, ProgramCreatesNode]
      constructor
      · intro present
        rcases present with (root | trueNode) | (root | falseNode)
        · exact Or.inl root
        · exact Or.inr (Or.inl trueNode)
        · exact Or.inl root
        · exact Or.inr (Or.inr falseNode)
      · intro present
        rcases present with root | trueNode | falseNode
        · exact Or.inl (Or.inl root)
        · exact Or.inl (Or.inr trueNode)
        · exact Or.inr (Or.inr falseNode)

/-- Every executable analyzer result is a well-formed usage value. -/
theorem analyze_wellFormed (program : TemplateIR) :
    (analyze program).usage.WellFormed := by
  induction program with
  | skip => exact Usage.empty_wellFormed
  | operation operation =>
      cases operation with
      | selectFixed path name => exact Usage.empty_wellFormed
      | selectFinite path names => exact Usage.empty_wellFormed
      | selectDynamic path => exact Usage.empty_wellFormed
      | read path => exact Usage.record_wellFormed Usage.empty_wellFormed path .read
      | exact path => exact Usage.record_wellFormed Usage.empty_wellFormed path .exact
      | complete path => exact Usage.record_wellFormed Usage.empty_wellFormed path .open
      | allowUnknown path =>
          exact Usage.record_wellFormed Usage.empty_wellFormed path .allowUnknown
      | iterate path =>
          exact Usage.record_wellFormed Usage.empty_wellFormed path .iterate
      | unsupported path mode reason =>
          exact Usage.record_wellFormed Usage.empty_wellFormed path mode
  | sequence first second firstInduction secondInduction =>
      exact Usage.merge_wellFormed firstInduction secondInduction
  | branch whenTrue whenFalse trueInduction falseInduction =>
      exact Usage.merge_wellFormed trueInduction falseInduction

/-- Every analyzer observation occurs at a node that the same analysis
    contains. -/
theorem analyze_observation_has_node (program : TemplateIR)
    (observation : Observation)
    (present : (analyze program).usage.contains observation) :
    (analyze program).usage.hasNode observation.path :=
  analyze_wellFormed program observation present

end HelmSchema.Proofs.Analyzer
