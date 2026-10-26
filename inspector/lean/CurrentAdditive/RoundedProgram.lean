import CurrentAdditive.RoundedDraw
import Paper2.RecursiveSamplingCapped

/-! Generic rounded execution of a finite-choice `Program`. This file only
    imports the immutable finite rounded-draw packet and defines the exact
    semantic bridge needed for v38 complete recursive labels. -/

namespace CurrentAdditive.RoundedProgram

open Paper2.RecursiveSamplingProgram
open Paper2.RecursiveSamplingCapped
open CurrentAdditive.RoundedDraw

variable {α : Type*}

def runState {A : ℕ} (b N : ℕ) (s : State α A)
    (bits : BitBlocks b N) : State α A :=
  runBitsRounded stateDenominator stateStep b stateDenominator_pos N s bits

theorem runState_draws_le {A : ℕ} (b N : ℕ) (s : State α A)
    (bits : BitBlocks b N) :
    (runState b N s bits).val.maxDraws ≤ s.val.maxDraws - N := by
  induction N generalizing s with
  | zero => simp [runState, runBitsRounded, runRounded]
  | succ N ih =>
      let i : Fin (stateDenominator s) :=
        draw (stateDenominator s) (2 ^ b) (stateDenominator_pos s)
          (by positivity) (Paper2.CappedSampler.bitsTicketEquiv b bits.1)
      have hstep := step_maxDraws_le s.val i
      have hrec := ih (stateStep s i) bits.2
      change (stateStep s i).val.maxDraws ≤ s.val.maxDraws - 1 at hstep
      change (runState b N (stateStep s i) bits.2).val.maxDraws ≤
        (stateStep s i).val.maxDraws - N at hrec
      change (runState b (N + 1) s bits).val.maxDraws ≤ _
      change (runState b N (stateStep s i) bits.2).val.maxDraws ≤ _
      omega

def leafValue (p : Program α) (h : p.maxDraws = 0) : α :=
  match p with
  | .pure a => a
  | .draw _ _ _ => False.elim (by simp at h)

theorem leafValue_pure (a : α) (h : (Program.pure a).maxDraws = 0) :
    leafValue (.pure a) h = a := rfl

theorem leafValue_of_eq_pure (p : Program α) (h : p.maxDraws = 0)
    (a : α) (hp : p = .pure a) : leafValue p h = a := by
  cases hp
  rfl

def runProgram {A : ℕ} (b N : ℕ) (s : State α A)
    (hN : s.val.maxDraws ≤ N) (bits : BitBlocks b N) : α :=
  leafValue (runState b N s bits).val (by
    have h := runState_draws_le b N s bits
    omega)

theorem runProgram_output_event {A : ℕ} (b N : ℕ) (s : State α A)
    (hN : s.val.maxDraws ≤ N) (bits : BitBlocks b N)
    (E : Set α) :
    E (runProgram b N s hN bits) ↔
      outputEvent E (runState b N s bits).val := by
  have hzero : (runState b N s bits).val.maxDraws = 0 := by
    have h := runState_draws_le b N s bits
    omega
  cases hp : (runState b N s bits).val with
  | pure a =>
      change E (leafValue (runState b N s bits).val _) ↔ a ∈ E
      rw [leafValue_of_eq_pure _ _ a hp]
      rfl
  | draw n hn next => simp [hp] at hzero

/-- An actual reserved `N`-block fair-bit tape produces a complete Program
output whose event law is within the v38 sampling budget of the ideal
finite-choice program. -/
theorem runProgram_event_error_200 {A : ℕ} (b N : ℕ)
    (s : State α A) (hN : s.val.maxDraws ≤ N)
    (hbudget : 200 * A * N ≤ 2 ^ b) (E : Set α) :
    |(bitBlocksLaw b N).prob
        (fun bits => E (runProgram b N s hN bits)) -
      s.val.eventProb E| ≤ (1 : ℝ) / 200 := by
  have hA (t : State α A) : stateDenominator t ≤ A :=
    (denominator_le_maxAlphabet t.val).trans t.property
  have hbase := bitBlocks_adaptive_event_error_200
    stateDenominator stateStep b A N stateDenominator_pos hA hbudget s
      (fun t => outputEvent E t.val)
  have hevent : (bitBlocksLaw b N).prob
      (fun bits => E (runProgram b N s hN bits)) =
      (bitBlocksLaw b N).prob
        (fun bits => outputEvent E (runState b N s bits).val) := by
    apply congrArg
    funext bits
    exact propext (runProgram_output_event b N s hN bits E)
  rw [hevent]
  have hident : Paper2.CappedSampler.Adaptive.idealMass
      stateDenominator stateStep stateDenominator_pos N s
        (fun t => outputEvent E t.val) = s.val.eventProb E :=
    idealMass_eq_eventProb N s hN E
  rw [hident] at hbase
  simpa only [runState] using hbase

#print axioms runState_draws_le
#print axioms runProgram_event_error_200

end CurrentAdditive.RoundedProgram
