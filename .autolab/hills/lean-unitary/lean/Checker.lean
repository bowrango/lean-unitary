import Lean

/-!
# Claim checker (lean-unitary hills)

Run by `eval.py` inside the evaluation build directory, in one of two modes:

    lake env lean --run Checker.lean milestones
    lake env lean --run Checker.lean general 3 4 5 6 7 8

1. Reads the compiled `LeanUnitary.*` modules reachable from `LeanUnitary.Claims` straight from
   their `.olean` files, and imports only their dependencies (Mathlib, Quantumlib, ...), once.
2. Re-checks every `LeanUnitary.*` declaration in the kernel on top of those dependencies.
   Elaborator tricks cannot survive this.
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

/-- Constant lookup: the submission's declarations, then the dependencies. -/
abbrev Lookup := Name → Option ConstantInfo

/-- Axioms (and unknown constants) that `root` transitively depends on. -/
def axiomsOf (find? : Lookup) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack := #[root]
  let mut found := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match find? n with
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
def findTheorem (find? : Lookup) (name : Name) : Except (String × String) ConstantInfo :=
  match find? name with
  | none => .error ("missing", s!"no declaration {name}")
  | some ci =>
    if ci matches .thmInfo _ then .ok ci else .error ("rejected", s!"{name} must be a theorem")

def axiomProblem (find? : Lookup) (name : Name) : Option String :=
  let bad := (axiomsOf find? name).filter (!allowedAxioms.contains ·)
  if bad.isEmpty then none else some s!"{name} depends on disallowed axioms {bad.toList}"

def status (fields : List (String × Json)) (st msg : String) : Json :=
  Json.mkObj (fields ++ [("status", toJson st), ("message", toJson msg)])

def checkMilestone (env : Environment) (find? : Lookup) : String × String → Json
  | (claim, spec) =>
    let name := claimName claim
    let fields := [("milestone", toJson spec)]
    match findTheorem find? name with
    | .error (st, msg) => status fields st msg
    | .ok ci =>
      if !Kernel.isDefEqGuarded env {} ci.type (mkConst (specName spec)) then
        status fields "rejected" s!"statement of {name} must be `{specName spec}`"
      else match axiomProblem find? name with
        | some msg => status fields "rejected" msg
        | none => Json.mkObj (fields ++ [("status", toJson "proved")])

def checkGeneral (env : Environment) (find? : Lookup) (ns : List Nat) : Json :=
  let name := claimName "synth"
  match findTheorem find? name with
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
        match axiomProblem find? name with
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
  -- Walk the project's modules from their .olean files, without importing them.
  let mut todo := #[`LeanUnitary.Claims]
  let mut seen : NameSet := {}
  let mut baseImports : NameSet := {}
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut specConstants : NameSet := {}
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    let (data, _) ← readModuleData (← findOLean m)
    for ci in data.constants do
      newConstants := newConstants.insert ci.name ci
      if m == `LeanUnitary.Spec then specConstants := specConstants.insert ci.name
    for i in data.imports do
      if isProjectModule i.module then todo := todo.push i.module
      else baseImports := baseImports.insert i.module
  -- Statements must come from the frozen module, not from anywhere the submission controls.
  let specDecls := ["Synthesizable", "GeneralBound"] ++ milestones.map (·.2)
  for s in specDecls do
    if !specConstants.contains (specName s) then
      return ← emit <| Json.mkObj [("ok", false),
        ("error", s!"{specName s} must be defined in module LeanUnitary.Spec")]
  let base ← importModules (baseImports.toArray.map ({ module := · })) {}
  let env ← try base.replay newConstants catch e =>
    return ← emit <| Json.mkObj [("ok", false), ("error", s!"kernel replay failed: {e}")]
  let find? : Lookup := fun n => newConstants[n]? <|> base.find? n
  let result := if mode == "milestones" then
      toJson (milestones.toArray.map (checkMilestone env find?))
    else checkGeneral env find? ns
  emit <| Json.mkObj [("ok", true), ("replayed", newConstants.size), ("result", result)]
