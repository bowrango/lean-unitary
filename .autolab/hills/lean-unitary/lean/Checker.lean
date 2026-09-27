import Lean

/-!
# Claim checker (lean-unitary hills)

Run by `eval.py` inside the evaluation build directory, in one of two modes:

    lake env lean --run Checker.lean milestones
    lake env lean --run Checker.lean general 3 4 5 6 7 8

1. Loads the compiled `LeanUnitary.Claims` module and everything it imports.
2. Re-checks every declaration from a `LeanUnitary.*` module in the kernel, on top of a fresh
   import of the dependencies (Mathlib, Quantumlib, ...). Elaborator tricks cannot survive this.
3. `milestones`: for each milestone `LeanUnitary.Spec.<P>`, looks for the theorem
   `LeanUnitary.Claims.<p>` and requires its statement to be exactly `P`.
   `general`: looks for the theorem `LeanUnitary.Claims.synth : LeanUnitary.Spec.GeneralBound f`
   and evaluates `f n` to a numeral with the kernel for each requested `n`.
4. Requires every accepted claim to depend on no axioms beyond `propext`, `Classical.choice`
   and `Quot.sound`.

Prints one JSON object on stdout.
-/

open Lean

def allowedAxioms : NameSet :=
  NameSet.empty |>.insert `propext |>.insert `Classical.choice |>.insert `Quot.sound

/-- Scored milestones: (theorem in `LeanUnitary.Claims`, frozen statement in `LeanUnitary.Spec`). -/
def milestones : List (String × String) :=
  [("muxRotations", "MuxRotations"), ("demultiplex", "Demultiplex"),
   ("cosineSine", "CosineSine"), ("twoQubitOptimal", "TwoQubitOptimal"), ("qsd", "QSD"),
   ("qsdOptimized", "QSDOptimized"), ("blockZXZ", "BlockZXZ")]

def specName (s : String) : Name := (`LeanUnitary.Spec).str s
def claimName (s : String) : Name := (`LeanUnitary.Claims).str s

def isProjectModule (m : Name) : Bool := (`LeanUnitary).isPrefixOf m

/-- Axioms (and unknown constants) that `root` transitively depends on. -/
def axiomsOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack := #[root]
  let mut found := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => found := found.push n
    | some ci =>
      if ci matches .axiomInfo _ then found := found.push n
      for c in ci.type.getUsedConstants do stack := stack.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do stack := stack.push c
  return found

/-- Reduce a closed `ℕ` expression to a numeral with the kernel. -/
def evalNat (env : Environment) (e : Expr) : Except String Nat :=
  match Kernel.whnf env {} e with
  | .ok (.lit (.natVal k)) => .ok k
  | .ok e' => .error s!"does not reduce to a numeral (stuck at {e'})"
  | .error _ => .error "kernel failed to reduce it"

/-- The theorem `name`, or why it cannot be scored. -/
def findTheorem (env : Environment) (name : Name) : Except (String × String) ConstantInfo :=
  match env.find? name with
  | none => .error ("missing", s!"no declaration {name}")
  | some ci =>
    if ci matches .thmInfo _ then .ok ci else .error ("rejected", s!"{name} must be a theorem")

def axiomProblem (env : Environment) (name : Name) : Option String :=
  let bad := (axiomsOf env name).filter (!allowedAxioms.contains ·)
  if bad.isEmpty then none else some s!"{name} depends on disallowed axioms {bad.toList}"

def status (fields : List (String × Json)) (st msg : String) : Json :=
  Json.mkObj (fields ++ [("status", toJson st), ("message", toJson msg)])

def checkMilestone (env : Environment) : String × String → Json
  | (claim, spec) =>
    let name := claimName claim
    let fields := [("milestone", toJson spec)]
    match findTheorem env name with
    | .error (st, msg) => status fields st msg
    | .ok ci =>
      if !Kernel.isDefEqGuarded env {} ci.type (mkConst (specName spec)) then
        status fields "rejected" s!"statement of {name} must be `{specName spec}`"
      else match axiomProblem env name with
        | some msg => status fields "rejected" msg
        | none => Json.mkObj (fields ++ [("status", toJson "proved")])

def checkGeneral (env : Environment) (ns : List Nat) : Json :=
  let name := claimName "synth"
  match findTheorem env name with
  | .error (st, msg) => status [] st msg
  | .ok ci =>
    match ci.type.getAppFnArgs with
    | (head, #[f]) =>
      if head != specName "GeneralBound" then
        status [] "rejected" s!"statement of {name} must be `{specName "GeneralBound"} f`" else
      let evals := ns.map fun n => (n, evalNat env (.app f (mkRawNatLit n)))
      match evals.find? (·.2 matches .error _) with
      | some (n, .error msg) => status [] "rejected" s!"bound at n = {n} {msg}"
      | _ =>
        let bounds := Json.mkObj <| evals.map fun
          | (n, .ok k) => (toString n, toJson k)
          | (n, .error _) => (toString n, Json.null)
        match axiomProblem env name with
        | some msg => status [("bounds", bounds)] "rejected" msg
        | none => Json.mkObj [("bounds", bounds), ("status", "proved")]
    | _ => status [] "rejected" s!"statement of {name} must be `{specName "GeneralBound"} f`"

def emit (j : Json) : IO UInt32 := do
  IO.println j.compress
  return 0

def main (args : List String) : IO UInt32 := do
  let (mode, ns) := match args with
    | m :: rest => (m, rest.filterMap String.toNat?)
    | [] => ("", [])
  if mode != "milestones" && mode != "general" then
    return ← emit <| Json.mkObj [("ok", false), ("error", s!"unknown mode {mode}")]
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanUnitary.Claims }] {}
  let modules := env.header.moduleNames
  -- Statements must come from the frozen module, not from anywhere the submission controls.
  let specDecls := ["Synthesizable", "GeneralBound"] ++ milestones.map (·.2)
  for s in specDecls do
    let fromSpec := match env.getModuleIdxFor? (specName s) with
      | some idx => modules[idx.toNat]? == some `LeanUnitary.Spec
      | none => false
    if !fromSpec then
      return ← emit <| Json.mkObj [("ok", false),
        ("error", s!"{specName s} must be defined in module LeanUnitary.Spec")]
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if modules[idx.toNat]?.any isProjectModule then
        newConstants := newConstants.insert n ci
  let baseImports := modules.filter (!isProjectModule ·) |>.map ({ module := · })
  let base ← importModules baseImports {}
  -- Replay only certifies the declarations; lookups below use `env`, which holds the same ones.
  try discard <| base.replay newConstants catch e =>
    return ← emit <| Json.mkObj [("ok", false), ("error", s!"kernel replay failed: {e}")]
  let result := if mode == "milestones" then
      toJson (milestones.toArray.map (checkMilestone env))
    else checkGeneral env ns
  emit <| Json.mkObj [("ok", true), ("replayed", newConstants.size), ("result", result)]
