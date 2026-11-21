import Lean
import Lean.Replay
import Lean.Util.CollectAxioms
import Export.Parse

open Lean

/-- The trusted environment contains the organizer-generated goal. Only neutral proof
data crosses from the contestant process. The final conversion is checked by the kernel. -/
def main (args : List String) : IO Unit := do
  let [file] := args | throw <| IO.userError "expected one NDJSON certificate"
  initSearchPath (← findSysroot)
  let base ← importModules #[{module := `Expected}, {module := `PoissonDAG.V2.Lower99}] {} 0
  let handle ← IO.FS.Handle.mk file .read
  let data ← Export.parseStream (IO.FS.Stream.ofHandle handle)
  for (name, ci) in data.constMap.toList do
    if (base.find? name).isSome || name == `Judge.checked then
      throw <| IO.userError "attempted redeclaration of a protected constant"
    if ci.isUnsafe || ci.isPartial then throw <| IO.userError "unsafe or partial declaration"
    match ci with
    | .axiomInfo _ | .quotInfo _ => throw <| IO.userError "additional axiom or quotient primitive"
    | _ => pure ()
  let some (.thmInfo cert) := data.constMap[`Submission.certificate]? |
    throw <| IO.userError "missing Submission.certificate theorem"
  unless cert.levelParams.isEmpty do throw <| IO.userError "unexpected universe parameters"
  let checked ← Lean.Environment.replay data.constMap base
  let witness := Declaration.thmDecl {
    name := `Judge.checked, levelParams := [], type := mkConst `Judge.goal,
    value := mkConst `Submission.certificate }
  match checked.toKernelEnv.addDeclCore 0 witness (cancelTk? := none) with
  | .error _ => throw <| IO.userError "certificate has a different target or byte bound"
  | .ok kenv =>
    let env := Lean.Environment.ofKernelEnv kenv
    let axs ← (Lean.collectAxioms `Judge.checked).toIO'
      { fileName := "<certificate>", fileMap := default } { env := env }
    unless axs.all (fun n => [`propext, `Classical.choice, `Quot.sound].contains n) do
      throw <| IO.userError s!"forbidden axiom dependency: {axs}"
    IO.println "Kernel checked Submission.certificate against Judge.goal"
