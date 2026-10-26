import CurrentV42
import Lean.Util.CollectAxioms

/-! Run only after the root has completed its shared CurrentV42 build.
This records the complete imported provider closure, including meta imports.
It does not certify manuscript correspondence or fresh project compilation. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    logInfo m!"RELEASE_MODULE|{name}|{← findOLean name}"
  logInfo m!"RELEASE_INVENTORY_COMPLETE modules={env.header.moduleNames.size}"
