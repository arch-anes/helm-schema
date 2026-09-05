import HelmSchema.Usage

set_option autoImplicit false

namespace HelmSchema

/-- The reason that exact template analysis stops at one operation. -/
inductive FallbackReason where
  | unknownFunction
  | dynamicTemplate
  | externalOperation
  | analysisLimit
  | unsupportedNode
  deriving BEq, DecidableEq, Repr

/-- One normalized template operation. Function-specific Go rules lower into
    these behavior classes before formal analysis. -/
inductive TemplateOperation where
  | selectFixed (path : List UsageSegment) (name : String)
  | selectFinite (path : List UsageSegment) (names : List String)
  | selectDynamic (path : List UsageSegment)
  | read (path : List UsageSegment)
  | exact (path : List UsageSegment)
  | complete (path : List UsageSegment)
  | allowUnknown (path : List UsageSegment)
  | iterate (path : List UsageSegment)
  | unsupported (path : List UsageSegment) (mode : UsageMode)
      (reason : FallbackReason)
  deriving BEq, DecidableEq, Repr

/-- Production function classes. Argument-sensitive and origin-preserving
    rules defer observations until the result or a specific argument is used. -/
inductive FunctionOperationClass where
  | semanticTransfer
  | originPreserving
  | exactConsumer
  | keyConsumer
  | completeConsumer
  | readConsumer
  | harmless
  | conservativeComplete
  deriving BEq, DecidableEq, Repr

namespace FunctionOperationClass

/-- Lower a path-independent function class to its formal operation. -/
def lower (path : UsagePath) : FunctionOperationClass → Option TemplateOperation
  | .semanticTransfer => none
  | .originPreserving => none
  | .exactConsumer => some (.exact path)
  | .keyConsumer => some (.allowUnknown path)
  | .completeConsumer => some (.complete path)
  | .readConsumer => some (.read path)
  | .harmless => none
  | .conservativeComplete =>
      some (.unsupported path .open .externalOperation)

/-- Argument-sensitive transfers defer their observation to the transfer
    implementation and its consumers. -/
@[simp]
theorem semanticTransfer_lower (path : UsagePath) :
    semanticTransfer.lower path = none := rfl

/-- Origin-preserving transforms defer their observation to a later consumer
    of the transformed result. -/
@[simp]
theorem originPreserving_lower (path : UsagePath) :
    originPreserving.lower path = none := rfl

/-- Exact consumers lower to the proved exact-value operation. -/
@[simp]
theorem exactConsumer_lower (path : UsagePath) :
    exactConsumer.lower path = some (.exact path) := rfl

/-- Key consumers lower to the proved direct-key operation. -/
@[simp]
theorem keyConsumer_lower (path : UsagePath) :
    keyConsumer.lower path = some (.allowUnknown path) := rfl

/-- Complete consumers lower to the proved complete-value operation. -/
@[simp]
theorem complete_lower (path : UsagePath) :
    completeConsumer.lower path = some (.complete path) := rfl

/-- Scalar consumers lower to the proved direct-read operation. -/
@[simp]
theorem readConsumer_lower (path : UsagePath) :
    readConsumer.lower path = some (.read path) := rfl

/-- Functions without chart-value arguments create no usage operation. -/
@[simp]
theorem harmless_lower (path : UsagePath) :
    harmless.lower path = none := rfl

/-- Conservative known functions use a named fallback rather than exact open
    evidence. -/
@[simp]
theorem conservative_lower (path : UsagePath) :
    conservativeComplete.lower path =
      some (.unsupported path .open .externalOperation) := rfl

end FunctionOperationClass

/-- A small control-flow language for normalized Helm template behavior. -/
inductive TemplateIR where
  | skip
  | operation (value : TemplateOperation)
  | sequence (first second : TemplateIR)
  | branch (whenTrue whenFalse : TemplateIR)
  deriving BEq, DecidableEq, Repr

namespace TemplateOperation

/-- The exact usage observations created by one normalized operation.
    Selection only classifies possible keys; a later consumer records usage. -/
def observations : TemplateOperation → List Observation
  | .selectFixed _ _ => []
  | .selectFinite _ _ => []
  | .selectDynamic _ => []
  | .read path => [{ path := path, mode := .read }]
  | .exact path => [{ path := path, mode := .exact }]
  | .complete path =>
      [{ path := path, mode := .read }, { path := path, mode := .open }]
  | .allowUnknown path => [{ path := path, mode := .allowUnknown }]
  | .iterate path => [{ path := path, mode := .iterate }]
  | .unsupported path mode _ =>
      mode.recorded.map fun recordedMode => { path := path, mode := recordedMode }

/-- Every non-root usage node required by an operation's observations. -/
def nodes (operation : TemplateOperation) : List UsagePath :=
  operation.observations.flatMap fun observation =>
    Usage.nonRootPrefixes observation.path

end TemplateOperation

/-- State that a program creates one observation. This specification is
    independent from `analyze` and contains no analyzer result. -/
def ProgramObserves : TemplateIR → Observation → Prop
  | .skip, _ => False
  | .operation operation, observation => observation ∈ operation.observations
  | .sequence first second, observation =>
      ProgramObserves first observation ∨ ProgramObserves second observation
  | .branch whenTrue whenFalse, observation =>
      ProgramObserves whenTrue observation ∨ ProgramObserves whenFalse observation

/-- State that a program creates one non-root usage node. Intermediate empty
    nodes are included because each operation reports every path prefix. -/
def ProgramCreatesNode : TemplateIR → UsagePath → Prop
  | .skip, _ => False
  | .operation operation, path => path ∈ operation.nodes
  | .sequence first second, path =>
      ProgramCreatesNode first path ∨ ProgramCreatesNode second path
  | .branch whenTrue whenFalse, path =>
      ProgramCreatesNode whenTrue path ∨ ProgramCreatesNode whenFalse path

/-- Semantic key selection. This relation does not inspect analyzer output. -/
inductive SelectsKey : TemplateIR → List UsageSegment → String → Prop where
  | fixed (path : List UsageSegment) (name : String) :
      SelectsKey (.operation (.selectFixed path name)) path name
  | finite (path : List UsageSegment) (names : List String) (name : String)
      (member : name ∈ names) :
      SelectsKey (.operation (.selectFinite path names)) path name
  | dynamic (path : List UsageSegment) (name : String) :
      SelectsKey (.operation (.selectDynamic path)) path name
  | sequenceLeft {first second path name}
      (selected : SelectsKey first path name) :
      SelectsKey (.sequence first second) path name
  | sequenceRight {first second path name}
      (selected : SelectsKey second path name) :
      SelectsKey (.sequence first second) path name
  | branchTrue {whenTrue whenFalse path name}
      (selected : SelectsKey whenTrue path name) :
      SelectsKey (.branch whenTrue whenFalse) path name
  | branchFalse {whenTrue whenFalse path name}
      (selected : SelectsKey whenFalse path name) :
      SelectsKey (.branch whenTrue whenFalse) path name

/-- Semantic selection with a statically bounded property name. Unlike
    `SelectsKey`, this relation excludes unbounded dynamic selection. -/
inductive StaticSelectsKey : TemplateIR → List UsageSegment → String → Prop where
  | fixed (path : List UsageSegment) (name : String) :
      StaticSelectsKey (.operation (.selectFixed path name)) path name
  | finite (path : List UsageSegment) (names : List String) (name : String)
      (member : name ∈ names) :
      StaticSelectsKey (.operation (.selectFinite path names)) path name
  | sequenceLeft {first second path name}
      (selected : StaticSelectsKey first path name) :
      StaticSelectsKey (.sequence first second) path name
  | sequenceRight {first second path name}
      (selected : StaticSelectsKey second path name) :
      StaticSelectsKey (.sequence first second) path name
  | branchTrue {whenTrue whenFalse path name}
      (selected : StaticSelectsKey whenTrue path name) :
      StaticSelectsKey (.branch whenTrue whenFalse) path name
  | branchFalse {whenTrue whenFalse path name}
      (selected : StaticSelectsKey whenFalse path name) :
      StaticSelectsKey (.branch whenTrue whenFalse) path name

/-- Every statically bounded selection is also a semantic selection. -/
theorem StaticSelectsKey.selects {program : TemplateIR}
    {path : List UsageSegment} {name : String}
    (selected : StaticSelectsKey program path name) :
    SelectsKey program path name := by
  induction selected with
  | fixed path name => exact SelectsKey.fixed path name
  | finite path names name member => exact SelectsKey.finite path names name member
  | sequenceLeft selected induction => exact SelectsKey.sequenceLeft induction
  | sequenceRight selected induction => exact SelectsKey.sequenceRight induction
  | branchTrue selected induction => exact SelectsKey.branchTrue induction
  | branchFalse selected induction => exact SelectsKey.branchFalse induction

/-- Semantic unbounded key selection. A dynamic selector can select every
    property name in the formal model. -/
inductive DynamicAt : TemplateIR → List UsageSegment → Prop where
  | dynamic (path : List UsageSegment) :
      DynamicAt (.operation (.selectDynamic path)) path
  | sequenceLeft {first second path} (dynamic : DynamicAt first path) :
      DynamicAt (.sequence first second) path
  | sequenceRight {first second path} (dynamic : DynamicAt second path) :
      DynamicAt (.sequence first second) path
  | branchTrue {whenTrue whenFalse path} (dynamic : DynamicAt whenTrue path) :
      DynamicAt (.branch whenTrue whenFalse) path
  | branchFalse {whenTrue whenFalse path} (dynamic : DynamicAt whenFalse path) :
      DynamicAt (.branch whenTrue whenFalse) path

/-- Semantic complete consumption. -/
inductive OpenAt : TemplateIR → List UsageSegment → Prop where
  | complete (path : List UsageSegment) :
      OpenAt (.operation (.complete path)) path
  | sequenceLeft {first second path} (openUse : OpenAt first path) :
      OpenAt (.sequence first second) path
  | sequenceRight {first second path} (openUse : OpenAt second path) :
      OpenAt (.sequence first second) path
  | branchTrue {whenTrue whenFalse path} (openUse : OpenAt whenTrue path) :
      OpenAt (.branch whenTrue whenFalse) path
  | branchFalse {whenTrue whenFalse path} (openUse : OpenAt whenFalse path) :
      OpenAt (.branch whenTrue whenFalse) path

/-- A modeled loss of precision. This relation does not claim that the
    concrete Helm operation consumes the complete selected value. -/
inductive UnsupportedAt : TemplateIR → List UsageSegment → UsageMode →
    FallbackReason → Prop where
  | unsupported (path : List UsageSegment) (mode : UsageMode)
      (reason : FallbackReason) :
      UnsupportedAt (.operation (.unsupported path mode reason)) path mode reason
  | sequenceLeft {first second path mode reason}
      (unsupported : UnsupportedAt first path mode reason) :
      UnsupportedAt (.sequence first second) path mode reason
  | sequenceRight {first second path mode reason}
      (unsupported : UnsupportedAt second path mode reason) :
      UnsupportedAt (.sequence first second) path mode reason
  | branchTrue {whenTrue whenFalse path mode reason}
      (unsupported : UnsupportedAt whenTrue path mode reason) :
      UnsupportedAt (.branch whenTrue whenFalse) path mode reason
  | branchFalse {whenTrue whenFalse path mode reason}
      (unsupported : UnsupportedAt whenFalse path mode reason) :
      UnsupportedAt (.branch whenTrue whenFalse) path mode reason

theorem dynamic_selects_every_key {program : TemplateIR}
    {path : List UsageSegment} (dynamic : DynamicAt program path)
    (name : String) : SelectsKey program path name := by
  induction dynamic with
  | dynamic path => exact SelectsKey.dynamic path name
  | sequenceLeft dynamic induction => exact SelectsKey.sequenceLeft induction
  | sequenceRight dynamic induction => exact SelectsKey.sequenceRight induction
  | branchTrue dynamic induction => exact SelectsKey.branchTrue induction
  | branchFalse dynamic induction => exact SelectsKey.branchFalse induction

theorem finite_selection_is_bounded {path : List UsageSegment}
    {names : List String} {name : String}
    (selected : SelectsKey (.operation (.selectFinite path names)) path name) :
    name ∈ names := by
  cases selected with
  | finite _ _ _ member => exact member

end HelmSchema
