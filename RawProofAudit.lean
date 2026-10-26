import CurrentV42
import Lean.Util.CollectAxioms

/-! Check all actual rows owned by CurrentAdditive or CurrentV42, including
private/generated rows. Check the effective declarations and all transitive
proof dependencies. When a raw row differs from its effective declaration,
inspect its actual type/value dependencies separately. Only propext,
Classical.choice and Quot.sound may be proof dependencies.

Other project libraries are inventoried as providers and their reachable proof
dependencies are checked. Unused inherited citation axioms are not assertions
of this release and are not promoted into its checked theorem scope. -/
open Lean Elab Command
set_option maxHeartbeats 0
set_option linter.style.longLine false

def releaseOwned (owner : Name) : Bool :=
  (`CurrentAdditive).isPrefixOf owner || (`CurrentV42).isPrefixOf owner

def rawRowKind : ConstantInfo → Nat
  | .axiomInfo _ => 0 | .defnInfo _ => 1 | .thmInfo _ => 2
  | .opaqueInfo _ => 3 | .quotInfo _ => 4 | .inductInfo _ => 5
  | .ctorInfo _ => 6 | .recInfo _ => 7

def auditActualDependency (dep : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless (env.checked.get.find? dep).isSome do
    throwError "Unresolved actual row-expression dependency {dep}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in (← collectAxioms dep) do
    unless allowed.contains ax do throwError "Actual row dependency {dep} uses forbidden axiom {ax}"

def auditActualExpr (e : Expr) : CommandElabM Nat := do
  let deps := e.getUsedConstants
  for dep in deps do auditActualDependency dep
  return deps.size

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut owners := 0
  let mut v42Owners := 0
  let mut rows := 0
  let mut theorems := 0
  let mut identical := 0
  let mut different := 0
  let mut actualDeps := 0
  for owner in env.header.moduleNames do
    if releaseOwned owner then
      owners := owners+1
      if owner.toString.startsWith "CurrentAdditive.V42" then v42Owners := v42Owners+1
      let some idx := env.getModuleIdx? owner | throwError "Missing owner {owner}"
      let md := env.header.moduleData[idx.toNat]!
      unless md.constNames.size == md.constants.size do
        throwError "Inconsistent raw module-table arrays for {owner}"
      for name in md.constNames, info in md.constants do
        rows := rows+1
        if info.isTheorem then theorems := theorems+1
        if info.isUnsafe then throwError "Unsafe actual row {name}"
        if info.isAxiom && !allowed.contains name then throwError "Forbidden actual axiom row {name}"
        let some checked := env.checked.get.find? name | throwError "Missing effective checked declaration {name}"
        for ax in (← collectAxioms name) do
          unless allowed.contains ax do throwError "Forbidden axiom {ax} in {name}"
        let sameKind := rawRowKind info == rawRowKind checked
        let sameLevels := info.levelParams == checked.levelParams
        let sameType := info.type == checked.type
        let sameValue := info.value? true == checked.value? true
        if sameKind && sameLevels && sameType && sameValue then
          identical := identical+1
        else
          different := different+1
          let mut count ← auditActualExpr info.type
          if let some value := info.value? true then count := count+(← auditActualExpr value)
          if let .inductInfo value := info then
            for ctor in value.ctors do
              auditActualDependency ctor
              count := count+1
          actualDeps := actualDeps+count
          logInfo m!"RAW_ROW_DIFFERENT|{owner}|{name}|kind={sameKind}|levels={sameLevels}|type={sameType}|value={sameValue}|actualDependencies={count}"
  unless owners > 0 && v42Owners > 0 && rows > 0 && theorems > 0 && identical+different == rows do
    throwError "Empty or inconsistent current proof-row inventory"
  logInfo m!"RAW_ROW_COUNTS owners={owners} v42Owners={v42Owners} rows={rows} theorems={theorems} identical={identical} different={different} actualDependencies={actualDeps}; standard3; no unsafe; kernelMissing=0"
  for name in env.header.moduleNames do
    logInfo m!"RAW_ROW_RESOLVED|{name}|{← findOLean name}"
  logInfo "RAW_PROOF_AUDIT_COMPLETE"
