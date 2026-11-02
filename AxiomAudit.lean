import CurrentV43
import Lean.Util.CollectAxioms

/-! Check the imported project declarations and their actual dependencies.
This audit does not establish manuscript correspondence by itself. -/
open Lean Elab Command
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  let mut currentModules := 0
  for owner in env.header.moduleNames do
    if (`CurrentV43).isPrefixOf owner then
      currentModules := currentModules + 1
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some index =>
        let owner := env.header.moduleNames[index]!
        (`CurrentAdditive).isPrefixOf owner || (`CurrentV42).isPrefixOf owner || (`CurrentV43).isPrefixOf owner
      | none => false
    if owned then
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      if info.isUnsafe then throwError "Unsafe project declaration {name}"
      if info.isAxiom && !allowed.contains name then
        throwError "Unapproved project axiom {name}"
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Forbidden axiom {ax} in {name}"
  unless currentModules > 0 && declarations > 0 && theorems > 0 do
    throwError "Empty current-source proof import"
  logInfo m!"V43_AUDIT modules={currentModules} declarations={declarations} theorems={theorems}; standard3; no unsafe"
