import Export
open Lean

/-- Serialize only the proof declarations additional to the organizer's library. -/
def main (args : List String) : IO Unit := do
  let [mod] := args | throw <| IO.userError "expected one contestant module"
  initSearchPath (← findSysroot)
  let base ← importModules #[{module := `JudgeImports}] {}
  let solution ← importModules #[{module := mod.toName}] {}
  M.run solution do
    initState solution
    let visited := base.constants.fold (init := ({} : NameHashSet)) fun s n _ => s.insert n
    modify fun st => {st with visitedConstants := visited}
    dumpMetadata
    dumpConstant `Submission.certificate
