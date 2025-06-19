import Lean
import Lean.Util.Path
import Lean.Elab.Command

open Lean System

/-- Find all sorries in a Lean file -/
def findSorriesInFile (path : FilePath) : IO (Array (String × Nat × String)) := do
  let contents ← IO.FS.readFile path
  let lines := contents.splitOn "\n"
  let mut results := #[]

  for i in [:lines.length] do
    let line := lines[i]!
    if line.containsSubstr "sorry" then
      -- Try to extract lemma/theorem name
      let mut lemmaName := ""

      -- Look backwards for lemma/theorem declaration
      for j in [:min i 10] do
        if i ≥ j then
          let prevLine := lines[i - j]!
          if prevLine.containsSubstr "lemma " || prevLine.containsSubstr "theorem " then
            -- Extract name
            let parts := prevLine.splitOn " "
            if parts.length ≥ 2 then
              lemmaName := parts[1]!.takeWhile (· ≠ ' ' ∧ · ≠ '{' ∧ · ≠ '(')
              break

      results := results.push (path.toString, i + 1, lemmaName)

  return results

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  let path := match args with
    | [p] => p
    | _ => "NavierStokesLedger/UnconditionalProof.lean"

  let results ← findSorriesInFile ⟨path⟩

  for (file, line, name) in results do
    IO.println s!"{file}:{line}: {if name.isEmpty then "unknown" else s!"lemma {name}"}"

  if results.isEmpty then
    IO.println "No sorries found!"
  else
    IO.println s!"\nTotal sorries: {results.size}"
