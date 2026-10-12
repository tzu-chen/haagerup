import ResultGraph.Extract

/-!
Read cached project proof terms using result-graph. Explicit `import all` for
each project module retains private proofs without loading Mathlib's private
proofs. No environment initializers, elaboration, or proof rebuilding is needed.
-/

open Lean ResultGraph

def main (args : List String) : IO Unit := do
  let [modulesFile, setupFile, output] := args
    | throw <| IO.userError "usage: Main.lean MODULES.txt SETUP.json OUTPUT.json"
  initSearchPath (← findSysroot)
  let modules := ((← IO.FS.readFile modulesFile).splitOn "\n").toArray
    |>.filter (!·.isEmpty) |>.map nameOfString
  IO.eprintln s!"Loading {modules.size} project modules with their private proof terms"
  let setupJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile setupFile)
  let setup : ModuleSetup ← IO.ofExcept <| fromJson? setupJson
  let env ← importModules
    (modules.map fun m => { module := m, importAll := true }) {}
    (level := .exported) (arts := setup.importArts)
  let cfg : Extract.Config :=
    { roots := modules, includePrivate := true, includeAuto := true }
  IO.eprintln "Import complete; streaming declaration terms"
  let kept := Extract.foldConstants env (#[] : Array (Name × ConstantInfo)) fun acc n ci =>
    if Extract.inProject env cfg n then acc.push (n, ci) else acc
  IO.FS.withFile output .write fun handle => do
    handle.putStr "{\"graph\":{\"roots\":[\"HaagerupIzumi\"],\"nodes\":["
    let mut first := true
    for (name, ci) in kept do
      if Extract.hasSorry ci || (ci matches .axiomInfo _) then
        throw <| IO.userError s!"Project sorry or axiom: {name}"
      let node : NodeJson :=
        { name := name.toString, module := (Extract.moduleOf env name).toString
          kind := (Kind.ofConstantInfo ci).toString, rank := "lemma"
          isPrivate := isPrivateName name, isUnsafe := ci.isUnsafe
          hasSorry := false, sorryTainted := false, customAxioms := #[], axiomTainted := false }
      unless first do handle.putStr ","
      first := false
      handle.putStr (toJson node).compress
    handle.putStr "],\"edges\":["
    let mut edgeCount := 0
    let mut boundaryCount := 0
    for internal in #[true, false] do
      first := true
      for (name, ci) in kept do
        let (types, values) := Extract.usedConstants ci
        for (deps, kind) in #[(types, "statement"), (values, "proof")] do
          for dep in deps do
            if Extract.inProject env cfg dep != internal then continue
            if (env.find? dep).isNone then
              throw <| IO.userError s!"Unresolved constant: {dep}"
            unless first do handle.putStr ","
            first := false
            let fields := [("src", toJson dep.toString), ("tgt", toJson name.toString),
                           ("kind", toJson kind)]
            let fields := if internal then fields else
              fields ++ [("module", toJson (Extract.moduleOf env dep).toString)]
            handle.putStr (Json.mkObj fields).compress
            if internal then edgeCount := edgeCount + 1 else boundaryCount := boundaryCount + 1
      if internal then handle.putStr "]},\"boundary\":["
    handle.putStr ("],\"modules\":" ++ (toJson (modules.map (·.toString))).compress ++
      ",\"lean_version\":" ++ (toJson Lean.versionString).compress ++ "}")
    IO.eprintln s!"Extracted {kept.size} declarations, {edgeCount} project edges, {boundaryCount} boundary references"
