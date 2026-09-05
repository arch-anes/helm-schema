import HelmSchema
import Lean.Elab.Command
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Lean.Elab Lean.Elab.Command

namespace Audit

/-- Formal-library modules that the umbrella import must continue to expose.
    The prefix check below includes new imported modules automatically. This
    list prevents a removed import from silently reducing the audit scope. -/
private def requiredModules : Array Name := #[
  `HelmSchema,
  `HelmSchema.Analyze,
  `HelmSchema.Boundary,
  `HelmSchema.Contract,
  `HelmSchema.Core,
  `HelmSchema.Flow,
  `HelmSchema.Generate,
  `HelmSchema.Json,
  `HelmSchema.Policy,
  `HelmSchema.Schema,
  `HelmSchema.TemplateIR,
  `HelmSchema.Usage,
  `HelmSchema.Proofs.Analyzer,
  `HelmSchema.Proofs.Boundary,
  `HelmSchema.Proofs.Core,
  `HelmSchema.Proofs.Flow,
  `HelmSchema.Proofs.Generator,
  `HelmSchema.Proofs.Usage,
  `HelmSchema.Proofs.Validator,
]

/-- Standard Lean axioms accepted by the formal library. `propext` states
    proposition extensionality. `Quot.sound` supports quotient types. Other
    dependencies, including choice and native evaluation axioms, need review. -/
private def allowedAxioms : Array Name := #[`propext, `Quot.sound]

/-- Return the source module recorded for one imported declaration. -/
private def declarationModule? (environment : Environment)
    (declaration : Name) : Option Name := do
  let moduleIndex ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[moduleIndex.toNat]?

/-- Report whether a declaration came from the `HelmSchema` formal library. -/
private def isProjectDeclaration (environment : Environment)
    (declaration : Name) : Bool :=
  match declarationModule? environment declaration with
  | none => false
  | some moduleName => (`HelmSchema).isPrefixOf moduleName

/-- Audit every project declaration and reject any unapproved transitive axiom.
    Checking definitions and generated declarations as well as theorems makes
    the audit stricter than a list of `#print axioms` commands. -/
elab "#audit_helm_schema_axioms" : command => do
  let environment ← getEnv
  let projectModules := environment.header.moduleNames.filter fun moduleName =>
    (`HelmSchema).isPrefixOf moduleName
  let missingModules := requiredModules.filter fun moduleName =>
    !projectModules.contains moduleName
  unless missingModules.isEmpty do
    throwError m!"axiom audit is missing required modules: {repr missingModules}"

  let declarations := environment.constants.toList.filterMap fun (name, _) =>
    if isProjectDeclaration environment name then some name else none
  let declarations := declarations.toArray.qsort Name.lt
  if declarations.isEmpty then
    throwError "axiom audit found no HelmSchema declarations"

  let mut failures : Array (Name × Array Name) := #[]
  for declaration in declarations do
    let dependencies ← collectAxioms declaration
    let unexpected := (dependencies.filter fun dependency =>
      !allowedAxioms.contains dependency).qsort Name.lt
    if !unexpected.isEmpty then
      failures := failures.push (declaration, unexpected)

  unless failures.isEmpty do
    throwError m!"project declaration axiom audit failed: {repr failures}"

  logInfo m!"project declaration axiom audit passed for \
    {declarations.size} declarations across {projectModules.size} modules; \
    allowed axioms: {repr allowedAxioms}"

#audit_helm_schema_axioms

end Audit

/-- The executable has no runtime work. Its compile-time command performs the
    audit, so a successful build is the result. -/
def main : IO UInt32 := pure 0
