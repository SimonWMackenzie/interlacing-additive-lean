import CurrentV42
import Lean.Util.CollectAxioms

/-! Every effective CurrentV42 / CurrentAdditive declaration and its transitive
proof dependencies, including reused project dependencies. A successful audit
does not establish manuscript correspondence or external source fidelity. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx =>
        let owner := env.header.moduleNames[idx]!
        (`CurrentAdditive).isPrefixOf owner || (`CurrentV42).isPrefixOf owner
      | none => false
    if owned then
      declarations := declarations+1
      if info.isTheorem then theorems := theorems+1
      if info.isUnsafe then throwError "Unsafe project declaration {name}"
      if info.isAxiom && !allowed.contains name then throwError "Forbidden owned axiom {name}"
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do throwError "Forbidden axiom {ax} in {name}"
  unless declarations > 0 && theorems > 0 do throwError "Empty current-source proof import"
  logInfo m!"V42_EFFECTIVE_AXIOM_AUDIT declarations={declarations} theorems={theorems}; standard3; no unsafe"
