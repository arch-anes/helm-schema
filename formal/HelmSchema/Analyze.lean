import HelmSchema.TemplateIR

set_option autoImplicit false

namespace HelmSchema

/-- Why the analyzer created non-static usage evidence. -/
inductive EvidenceKind where
  | dynamicSelection
  | completeConsumption
  | conservativeFallback (reason : FallbackReason) (mode : UsageMode)
  deriving BEq, DecidableEq, Repr

/-- One reviewable reason at one value path. -/
structure EvidenceReason where
  path : List UsageSegment
  kind : EvidenceKind
  deriving BEq, DecidableEq, Repr

/-- One fixed property that exact analysis found selectable. -/
structure SelectedKey where
  path : List UsageSegment
  name : String
  deriving BEq, DecidableEq, Repr

/-- The normalized usage and its non-static evidence reasons. -/
structure AnalysisResult where
  usage : Usage := Usage.empty
  selectedKeys : List SelectedKey := []
  reasons : List EvidenceReason := []
  deriving BEq, Repr

namespace AnalysisResult

/-- Combine control-flow results without removing evidence. -/
def merge (left right : AnalysisResult) : AnalysisResult :=
  { usage := left.usage.merge right.usage
  , selectedKeys := left.selectedKeys ++ right.selectedKeys
  , reasons := left.reasons ++ right.reasons
  }

end AnalysisResult

/-- The executable reference analyzer for `TemplateIR`. -/
def analyzeOperation : TemplateOperation → AnalysisResult
  | .selectFixed path name =>
      { selectedKeys := [{ path := path, name := name }] }
  | .selectFinite path names =>
      { selectedKeys := names.map fun name => { path := path, name := name } }
  | .selectDynamic path =>
      { reasons := [{ path := path, kind := .dynamicSelection }] }
  | .read path => { usage := Usage.empty.record path .read }
  | .exact path => { usage := Usage.empty.record path .exact }
  | .complete path =>
      { usage := Usage.empty.record path .open
      , reasons := [{ path := path, kind := .completeConsumption }] }
  | .allowUnknown path => { usage := Usage.empty.record path .allowUnknown }
  | .iterate path => { usage := Usage.empty.record path .iterate }
  | .unsupported path mode reason =>
      { usage := Usage.empty.record path mode
      , reasons := [{ path := path, kind := .conservativeFallback reason mode }] }

/-- Analyze normalized control flow. Both branches contribute because either
    branch can execute for some values input. -/
def analyze : TemplateIR → AnalysisResult
  | .skip => {}
  | .operation operation => analyzeOperation operation
  | .sequence first second => (analyze first).merge (analyze second)
  | .branch whenTrue whenFalse => (analyze whenTrue).merge (analyze whenFalse)

end HelmSchema
