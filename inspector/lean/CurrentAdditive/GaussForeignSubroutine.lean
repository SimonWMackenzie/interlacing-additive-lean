import CurrentAdditive.GaussBranchQuotientBridge
import EthInapproximability.CurrentPaper.BitMachineSubroutine

namespace CurrentAdditive.GaussPhysical.GaussForeignSubroutine

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachine BitMachineComposition BitMachineSubroutine BitMachineEncoding

abbrev Stack (M : BitMachine.Machine) := Fin M.stackCount ⊕ Fin 12
abbrev Label (M : BitMachine.Machine) := Fin M.labelCount ⊕ Fin 1
abbrev Control (M : BitMachine.Machine) := Fin M.controlCount × Unit

def program (M : BitMachine.Machine) : Label M →
    TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some (0 : Fin 1)) (M.program l)
  | .inr _ => halt

def startCfg (M : BitMachine.Machine) (input : List Bool)
    (context : Fin 12 → List Bool) :
    TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M) :=
  liftCfg (some (0 : Fin 1)) () context (M.init input)

/-- Run any checked physical arithmetic packet with twelve foreign context
words, retaining each word exactly and reaching a fixed next-stage label. -/
theorem run_preserves_context (M : BitMachine.Machine)
    (input output : List Bool) (context : Fin 12 → List Bool)
    (bound : ℕ) (h : M.OutputsWithin input output bound) :
    ∃ u ≤ bound,
      let c := ((advance (program M))^[u]) (startCfg M input context)
      c.l = some (.inr 0) ∧
      (∀ j : Fin 12, c.stk (.inr j) = context j) ∧
      c.stk (.inl M.output) = output := by
  have hh := (BitMachine.outputsWithin_at_bound M h).1
  obtain ⟨u,hu,hr⟩ := lift_outputs M.program (program M)
    (some (0 : Fin 1)) (by intro l; rfl) () context
    (M.init input) bound hh
  refine ⟨u,hu,?_⟩
  have hout := (BitMachine.outputsWithin_at_bound M h).2
  dsimp only
  rw [startCfg]
  rw [hr]
  change (((advance M.program)^[bound]) (M.init input)).l = none at hh
  change (((advance M.program)^[bound]) (M.init input)).stk M.output = output at hout
  simp [liftCfg, hh, hout]

theorem signed_product_preserves_context
    (input : List Bool) (context : Fin 12 → List Bool) :
    ∃ u ≤ 1300 * (input.length + 1) ^ 2,
      let M := EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine
      let c := ((advance (program M))^[u]) (startCfg M input context)
      c.l = some (.inr 0) ∧
      (∀ j : Fin 12, c.stk (.inr j) = context j) ∧
      c.stk (.inl M.output) =
        EthInapproximability.CurrentPaper.RationalProductSignedPhysical.result
          input := by
  apply run_preserves_context
  exact EthInapproximability.CurrentPaper.RationalProductSignedPhysical.outputs input

#print axioms run_preserves_context
#print axioms signed_product_preserves_context

end CurrentAdditive.GaussPhysical.GaussForeignSubroutine
