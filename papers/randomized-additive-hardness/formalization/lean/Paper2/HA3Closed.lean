import Paper2.A3FrontFinal
import Paper2.A3LConsumer
import Paper2.A3L3None

/-!
# Unit 3 closure, segment 1: `H_A3` with no open specification (Paper A, lock v12)

Lane `owner:a-h-a3-close-1` (private, 26 September 2026). Pure composition, no new machine.
`A3LConsumer.H_A3_of_front_none` (lane a-h-a3-lift-owner-2: `A3H3Run.H_A3_R12` applied to `hProbe_spec`,
`hSucc_spec` and the owner-1 `hUnsched_spec`) is instantiated at

* the front scratch `FrontLift.FS` and the front `FrontLift.front Δ γ`, `sF Δ γ`, `vF Δ γ` of lane
  a-success-table-owner-13, with `hFront := FrontLift.hFront_final Δ γ hγ hΔ` (Mid1 constants
  `CM Δ γ 2`, `EM (cF Δ γ * 266 * 45)`; clock `2`, exponent `cF Δ γ * 266 * 45`);
* the none branch `Lift3.nProg FrontLift.FS` of lane a-h-a3-lift-owner-3, with `hNone := hNone_spec` at the
  constants the consumer fixes, `PC FS (CM Δ γ 2)` and `PE (EM (cF Δ γ * 266 * 45))`; the consumer's
  precondition `Mid2C … ∧ ¬ Lift.Good …` is converted to `hNone_spec`'s `(Mid2 … ∧ ChecksCond …) ∧ ¬ GoodN …` by
  `Mid2C` unfolding (definitional) and `GoodN = Lift.Good` (definitional).

Frozen private objects imported bare (hash-verified, logs/verify_pred.log). Nothing else is assumed.
-/

set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 16384
set_option synthInstance.maxHeartbeats 400000

namespace Paper2.A3Close

open Turing
open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly

/-- Precondition weakening of a branch specification (pure logic). -/
theorem branch_pre (Δ : ℕ) (γ : ℚ) (a : ℕ) {L V : Type}
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (s : L) (v : V) (j : Fin (a + 3))
    (Pre Pre' : Run.Pred Δ γ a) (C E : ℕ)
    (himp : ∀ g hg hn k t S, Pre' g hg hn k t S → Pre g hg hn k t S)
    (h : Run.BranchSpec Δ γ a P s v j Pre C E) : Run.BranchSpec Δ γ a P s v j Pre' C E :=
  fun g hg hn k hH t S hS => h g hg hn k hH t S (himp g hg hn k t S hS)

/-- The `hNone` argument of `Lift.H_A3_of_front_none` at the front constants of `hFront_final`. -/
theorem hNone_closed (Δ : ℕ) (γ : ℚ) :
    Run.BranchSpec Δ γ (Lift.a FrontLift.FS) (Lift3.nProg FrontLift.FS)
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))) NoneOut.ctlN (Lift.outJ FrontLift.FS)
      (fun g hg hn k t S =>
        Lift.Mid2C FrontLift.FS Δ γ (Lift.PC FrontLift.FS (FrontLift.CM Δ γ 2))
          (Lift.PE (FrontLift.EM (FrontClock13.cF Δ γ * 266 * 45))) g hg hn k t S ∧
        ¬ Lift.Good Δ γ g hg hn k t)
      (Lift3.NC FrontLift.FS (Lift.PC FrontLift.FS (FrontLift.CM Δ γ 2)))
      (max (Lift.PE (FrontLift.EM (FrontClock13.cF Δ γ * 266 * 45))) Clocks.EN) :=
  branch_pre Δ γ (Lift.a FrontLift.FS) _ _ _ _ _ _ _ _
    (fun _ _ _ _ _ _ h => ⟨h.1, fun hG => h.2 hG⟩)
    (Lift3.hNone_spec FrontLift.FS Δ γ (Lift.PC FrontLift.FS (FrontLift.CM Δ γ 2))
      (Lift.PE (FrontLift.EM (FrontClock13.cF Δ γ * 266 * 45))))

/-- **Unit 3 closure: `H_A3` with no open specification.** For every `Δ > 0`, `γ > 0`, the production
`Unit4Shell.Shells.H_A3 Δ γ`, from the five checked specifications (front, probe, success, none,
unscheduled) and nothing else. -/
theorem H_A3_closed (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) : Unit4Shell.Shells.H_A3 Δ γ :=
  Lift.H_A3_of_front_none FrontLift.FS Δ γ hΔ hγ (FrontLift.front Δ γ) (FrontLift.sF Δ γ) (FrontLift.vF Δ γ)
    (Lift3.nProg FrontLift.FS) _ _
    2 (FrontClock13.cF Δ γ * 266 * 45) _ _ (FrontLift.CM Δ γ 2) (FrontLift.EM (FrontClock13.cF Δ γ * 266 * 45))
    (FrontLift.hFront_final Δ γ hγ hΔ) (hNone_closed Δ γ)

end Paper2.A3Close

#print axioms Paper2.A3Close.branch_pre
#print axioms Paper2.A3Close.hNone_closed
#print axioms Paper2.A3Close.H_A3_closed
