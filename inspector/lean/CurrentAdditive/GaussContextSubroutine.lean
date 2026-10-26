import CurrentAdditive.GaussFirstQuotientSpec
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
A concrete finite-control embedding of a signed rational arithmetic machine
with one foreign stack. The foreign stack holds cell context through an
arithmetic call. This does not yet concatenate the calls into the entire
Gauss clear-cell controller.
-/

namespace CurrentAdditive.GaussPhysical.GaussContextSubroutine

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachine BitMachineComposition BitMachineSubroutine BitMachineEncoding

abbrev Stack (M : BitMachine.Machine) := Fin M.stackCount ⊕ Fin 1
abbrev Label (M : BitMachine.Machine) := Fin M.labelCount ⊕ Fin 1
abbrev Control (M : BitMachine.Machine) := Fin M.controlCount × Unit

def program (M : BitMachine.Machine) : Label M →
    TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some (0 : Fin 1)) (M.program l)
  | .inr _ => halt

def startCfg (M : BitMachine.Machine) (input context : List Bool) :
    TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M) :=
  liftCfg (some (0 : Fin 1)) () (fun _ : Fin 1 => context) (M.init input)

/-- An actual arithmetic run is transported without changing the foreign
context word. The target label is the next fixed Gauss controller stage. -/
theorem run_preserves_context (M : BitMachine.Machine)
    (input output context : List Bool) (bound : ℕ)
    (h : M.OutputsWithin input output bound) :
    ∃ u ≤ bound,
      ((advance (program M))^[u]) (startCfg M input context) =
        liftCfg (some (0 : Fin 1)) () (fun _ : Fin 1 => context)
          (M.run bound (M.init input)) := by
  have hh := (BitMachine.outputsWithin_at_bound M h).1
  exact lift_outputs M.program (program M) (some (0 : Fin 1))
    (by intro l; rfl) () (fun _ : Fin 1 => context)
    (M.init input) bound hh

theorem signed_product_run_preserves_context
    (input context : List Bool) :
    ∃ u ≤ 1300 * (input.length + 1) ^ 2,
      ((advance (program
        EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine))^[u])
        (startCfg
          EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine
          input context) =
        liftCfg (some (0 : Fin 1)) () (fun _ : Fin 1 => context)
          ((EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine).run
            (1300 * (input.length + 1) ^ 2)
            ((EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine).init
              input)) := by
  apply run_preserves_context
  exact EthInapproximability.CurrentPaper.RationalProductSignedPhysical.outputs input

/-- Observable controller state after the signed product/quotient packet:
the original context word survives while the exact arithmetic result is
available on the designated machine output stack. -/
theorem signed_product_context_and_output
    (input context : List Bool) :
    ∃ u ≤ 1300 * (input.length + 1) ^ 2,
      let M := EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine
      let c := ((advance (program M))^[u]) (startCfg M input context)
      c.l = some (.inr 0) ∧
      c.stk (.inr 0) = context ∧
      c.stk (.inl M.output) =
        EthInapproximability.CurrentPaper.RationalProductSignedPhysical.result input := by
  obtain ⟨u, hu, hr⟩ := signed_product_run_preserves_context input context
  refine ⟨u, hu, ?_⟩
  have hout := (BitMachine.outputsWithin_at_bound
    EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine
    (EthInapproximability.CurrentPaper.RationalProductSignedPhysical.outputs input)).2
  have hhalt := (BitMachine.outputsWithin_at_bound
    EthInapproximability.CurrentPaper.RationalProductSignedPhysical.machine
    (EthInapproximability.CurrentPaper.RationalProductSignedPhysical.outputs input)).1
  dsimp only
  rw [hr]
  simp [liftCfg, hhalt, hout]

end CurrentAdditive.GaussPhysical.GaussContextSubroutine
