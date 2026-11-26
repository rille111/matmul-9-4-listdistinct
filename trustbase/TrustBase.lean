import ListDistinct
open Lean Elab Command

/-- Transitive closure of constants used by the given roots (types and values). -/
def closureOf (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  repeat
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
      | none => pure ()
  return seen

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `ListDistinct

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def report (env : Environment) (root : Name) : IO String := do
  let s := closureOf env [root]
  let mut byMod : Std.HashMap Name Nat := {}
  let mut byTop : Std.HashMap Name Nat := {}
  let mut kinds : Std.HashMap String Nat := {}
  let mut axs : Array Name := #[]
  for n in s.toList do
    let m := modOf env n
    byMod := byMod.insert m (byMod.getD m 0 + 1)
    byTop := byTop.insert m.getRoot (byTop.getD m.getRoot 0 + 1)
    if let some ci := env.find? n then
      let k := kindOf ci
      kinds := kinds.insert k (kinds.getD k 0 + 1)
      if k == "axiom" then axs := axs.push n
  let mut out := s!"ROOT {root}\nTOTAL_CONSTANTS {s.size}\nMODULES_TOUCHED {byMod.size}\n"
  for (k, v) in byTop.toList do out := out ++ s!"TOP {k} {v}\n"
  for (k, v) in kinds.toList do out := out ++ s!"KIND {k} {v}\n"
  for a in axs do out := out ++ s!"AXIOM {a}\n"
  let oai := byMod.toList.filter (fun (m, _) => m.getRoot == `OAI || m == `ListDistinct)
  let oai := oai.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (m, v) in oai do out := out ++ s!"MOD {m} {v}\n"
  return out

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut all := ""
  for r in [`ListDistinctExposition.circuit_lower,
            `OAI.LinearAlgebra.MatrixExponent.BatchDescent.hard,
            `ListDistinctExposition.circuit_dnet] do
    all := all ++ (← report env r) ++ "\n"
  IO.FS.writeFile "trustbase.txt" all
  IO.println s!"wrote trustbase.txt ({all.length} chars)"
