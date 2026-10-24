import CurrentAdditive
import Lean.Util.CollectAxioms

/-!
Portable release audit derived from the successful 22 October 2026 recovery02
`audit-sources/RawModuleRowReadback.lean`, recorded in
`formalization/current-v27/verification/fresh-v40-completion-20261022/SUCCESS.json`.
Original source SHA256:
EB3A1A32915C77A642B75047EAD5C4AEE9DD5D6AD5577A0FEADB15F68FDDED31.

This copy preserves the original raw-row, checked-declaration, unsafe, axiom,
count, actual-expression and provider checks. It additionally incorporates the
successful preceding module-table audit's transitive axiom check for every raw
row name. Equal raw type/proof expressions are thereby covered by that checked
declaration; different expressions are inspected directly, including duplicate
generated theorem rows. Only propext, Classical.choice and Quot.sound are allowed.

The audit uses the imported environment and logs resolved providers; it reads no
historical private files. It is specific to the frozen v40 proof snapshot. It
does not certify manuscript correspondence or external source-record fidelity.
-/

open Lean Elab Command
set_option maxHeartbeats 0
set_option linter.style.longLine false

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
  let mut rows := 0
  let mut theorems := 0
  let mut identical := 0
  let mut different := 0
  let mut actualDeps := 0
  for owner in env.header.moduleNames do
    if (`CurrentAdditive).isPrefixOf owner then
      let some idx := env.getModuleIdx? owner | throwError "Missing owner {owner}"
      let md := env.header.moduleData[idx.toNat]!
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
  unless rows == 56544 && theorems == 37175 && identical+different == rows do
    throwError "Unexpected actual module-table row counts"
  logInfo m!"RAW_ROW_COUNTS rows={rows} theorems={theorems} identical={identical} different={different} actualDependencies={actualDeps}; standard3; no unsafe; kernelMissing=0"
  for name in env.header.moduleNames do
    logInfo m!"RAW_ROW_RESOLVED|{name}|{← findOLean name}"
