import Paper2.RecursiveSamplingProgram
import Paper2.CappedSamplerCouplingAdaptive

/-!
# A fixed fair-bit implementation of finite-choice programs

Frozen v12, `appendices/D-implementation.tex:83--102` (U15).
The state is the residual program. Its current finite alphabet is sampled by
the existing capped rejection sampler; a finished leaf makes only singleton
requests. A syntactic alphabet bound supplies a common tape-block width.
After at least `maxDraws` transitions, the ideal output event has exactly the
program's recursively defined law. The capped execution inherits its proved
event-error bound. No source-specific draw bound or machine runtime is assumed
to follow from this generic compilation.
-/

namespace Paper2.RecursiveSamplingCapped

open RecursiveSamplingProgram
open scoped BigOperators

variable {A : Type*}

def denominator : Program A → ℕ
  | .pure _ => 1
  | .draw n _ _ => n

def step : (p : Program A) → Fin (denominator p) → Program A
  | .pure a, _ => .pure a
  | .draw _ _ next, i => next i

theorem denominator_pos (p : Program A) : 0 < denominator p := by
  cases p with
  | pure a => exact Nat.zero_lt_one
  | draw n hn next => exact hn

theorem denominator_le_maxAlphabet (p : Program A) : denominator p ≤ p.maxAlphabet := by
  cases p with
  | pure a => exact le_rfl
  | draw n hn next => exact Nat.le_max_left _ _

theorem step_maxAlphabet_le (p : Program A) (i : Fin (denominator p)) :
    (step p i).maxAlphabet ≤ p.maxAlphabet := by
  cases p with
  | pure a => exact le_rfl
  | draw n hn next =>
    exact (Finset.le_sup (f := fun j => (next j).maxAlphabet) (Finset.mem_univ i)).trans
      (Nat.le_max_right _ _)

theorem step_maxDraws_le (p : Program A) (i : Fin (denominator p)) :
    (step p i).maxDraws ≤ p.maxDraws - 1 := by
  cases p with
  | pure a => simp [step]
  | draw n hn next =>
    simpa only [step, Program.maxDraws_draw, Nat.add_sub_cancel_left] using
      (Finset.le_sup (f := fun j => (next j).maxDraws) (Finset.mem_univ i))

/-- Closed state space: every residual program uses alphabets of size at most `M`. -/
def State (A : Type*) (M : ℕ) := {p : Program A // p.maxAlphabet ≤ M}

def stateDenominator {M : ℕ} (s : State A M) : ℕ := denominator s.val

def stateStep {M : ℕ} (s : State A M) (i : Fin (stateDenominator s)) : State A M :=
  ⟨step s.val i, (step_maxAlphabet_le s.val i).trans s.property⟩

theorem stateDenominator_pos {M : ℕ} (s : State A M) : 0 < stateDenominator s :=
  denominator_pos s.val

theorem state_width {M B : ℕ} (hMB : Nat.clog 2 M ≤ B) (s : State A M) :
    Nat.clog 2 (stateDenominator s) ≤ B :=
  (Nat.clog_mono_right 2 ((denominator_le_maxAlphabet s.val).trans s.property)).trans hMB

/-- Only a finished leaf satisfies an output event. -/
def outputEvent (E : Set A) : Program A → Prop
  | .pure a => a ∈ E
  | .draw _ _ _ => False

noncomputable def idealMass {M : ℕ} (N : ℕ) (s : State A M) (E : Set A) : ℝ :=
  CappedSampler.Adaptive.idealMass stateDenominator stateStep stateDenominator_pos
    N s (fun t => outputEvent E t.val)

theorem idealMass_eq_eventProb {M : ℕ} (N : ℕ) (s : State A M)
    (hN : s.val.maxDraws ≤ N) (E : Set A) :
    idealMass N s E = s.val.eventProb E := by
  classical
  induction N generalizing s with
  | zero =>
    rcases s with ⟨p, hp⟩
    cases p with
    | pure a => simp [idealMass, CappedSampler.Adaptive.idealMass,
        outputEvent, Program.eventProb, Set.indicator_apply]
    | draw n hn next => simp only [Program.maxDraws_draw] at hN; omega
  | succ N ih =>
    unfold idealMass
    rw [CappedSampler.Adaptive.idealMass]
    have hchild (i : Fin (stateDenominator s)) :
        (stateStep s i).val.maxDraws ≤ N := by
      have hstep := step_maxDraws_le s.val i
      change (step s.val i).maxDraws ≤ N
      omega
    have hrec (i : Fin (stateDenominator s)) := ih (stateStep s i) (hchild i)
    simp only [idealMass] at hrec
    simp_rw [hrec]
    rcases s with ⟨p, hp⟩
    cases p with
    | pure a => simp [stateDenominator, denominator, stateStep, step,
        CappedSampler.uniformTicket]
    | draw n hn next =>
      simp only [stateDenominator, denominator, stateStep, step,
        CappedSampler.uniformTicket, Program.eventProb, Program.expect_draw]
      exact (Finset.mul_sum _ _ _).symm

/-- Execute exactly `N` public blocks, aborting on any exhausted draw. -/
def runState {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N) : Option (State A M) :=
  CappedSampler.Adaptive.run stateDenominator stateStep B R (state_width hMB) N s t

theorem failure_le {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) :
    (CappedSampler.Adaptive.law B R N).prob (fun t => runState B R hMB N s t = none) ≤
      (N : ℝ) * (1 / 2 : ℝ) ^ R :=
  CappedSampler.Adaptive.failure_le stateDenominator stateStep B R (state_width hMB)
    stateDenominator_pos N s

theorem event_error {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s s₀ : State A M) (hN : s.val.maxDraws ≤ N) (E : Set A) :
    |(CappedSampler.Adaptive.law B R N).prob
        (fun t => outputEvent E (CappedSampler.completed (runState B R hMB N s t) s₀).val) -
      s.val.eventProb E| ≤ (N : ℝ) * (1 / 2 : ℝ) ^ R := by
  rw [← idealMass_eq_eventProb N s hN E]
  exact CappedSampler.Adaptive.abort_event_error stateDenominator stateStep B R
    (state_width hMB) stateDenominator_pos N s s₀ (fun u => outputEvent E u.val)

theorem runState_draws_le {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N)
    (u : State A M) (hu : runState B R hMB N s t = some u) :
    u.val.maxDraws ≤ s.val.maxDraws - N := by
  induction N generalizing s u with
  | zero =>
    simp only [runState, CappedSampler.Adaptive.run, Option.some.injEq] at hu
    subst u
    omega
  | succ N ih =>
    change (CappedSampler.runWideBits (stateDenominator s) B R (state_width hMB s) t.1).bind
      (fun i => runState B R hMB N (stateStep s i) t.2) = some u at hu
    cases hd : CappedSampler.runWideBits (stateDenominator s) B R (state_width hMB s) t.1 with
    | none => simp [hd] at hu
    | some i =>
      simp only [hd, Option.bind_some] at hu
      have hi := ih (stateStep s i) t.2 u hu
      have hs := step_maxDraws_le s.val i
      change (stateStep s i).val.maxDraws ≤ s.val.maxDraws - 1 at hs
      omega

theorem pure_of_maxDraws_zero (p : Program A) (hp : p.maxDraws = 0) :
    ∃ a, p = .pure a := by
  cases p with
  | pure a => exact ⟨a, rfl⟩
  | draw n hn next => simp only [Program.maxDraws_draw] at hp; omega

theorem runState_pure {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) (u : State A M)
    (hu : runState B R hMB N s t = some u) : ∃ a, u.val = .pure a := by
  apply pure_of_maxDraws_zero
  have := runState_draws_le B R hMB N s t u hu
  omega

def readResult : Program A → Option A
  | .pure a => some a
  | .draw _ _ _ => none

/-- The actual finite-bit program interpreter; successful execution returns a leaf value. -/
def run {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N) : Option A :=
  (runState B R hMB N s t).bind (fun u => readResult u.val)

theorem run_none_iff {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) :
    run B R hMB N s t = none ↔ runState B R hMB N s t = none := by
  cases hu : runState B R hMB N s t with
  | none => simp [run, hu]
  | some u =>
    obtain ⟨a, ha⟩ := runState_pure B R hMB N s hN t u hu
    simp [run, hu, ha, readResult]

def fallbackState {M : ℕ} (s : State A M) (a₀ : A) : State A M :=
  ⟨.pure a₀, (Nat.succ_le_of_lt s.val.maxAlphabet_pos).trans s.property⟩

theorem completed_output_event {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) (a₀ : A) (E : Set A) :
    CappedSampler.completed (run B R hMB N s t) a₀ ∈ E ↔
      outputEvent E (CappedSampler.completed (runState B R hMB N s t)
        (fallbackState s a₀)).val := by
  cases hu : runState B R hMB N s t with
  | none => simp [run, hu, CappedSampler.completed, fallbackState, outputEvent]
  | some u =>
    obtain ⟨a, ha⟩ := runState_pure B R hMB N s hN t u hu
    simp [run, hu, CappedSampler.completed, ha, readResult, outputEvent]

/-- Every event of the completed output differs from the ideal program by
at most the union bound for the public number of capped uniform requests. -/
theorem output_event_error {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N) (a₀ : A) (E : Set A) :
    |(CappedSampler.Adaptive.law B R N).prob
        (fun t => CappedSampler.completed (run B R hMB N s t) a₀ ∈ E) -
      s.val.eventProb E| ≤ (N : ℝ) * (1 / 2 : ℝ) ^ R := by
  simp_rw [completed_output_event B R hMB N s hN _ a₀ E]
  exact event_error B R hMB N s (fallbackState s a₀) hN E

theorem output_failure_le {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N) :
    (CappedSampler.Adaptive.law B R N).prob (fun t => run B R hMB N s t = none) ≤
      (N : ℝ) * (1 / 2 : ℝ) ^ R := by
  simp_rw [run_none_iff B R hMB N s hN]
  exact failure_le B R hMB N s

theorem scheduled_output_event_error {M : ℕ} (B : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N) (a₀ : A) (E : Set A) :
    |(CappedSampler.Adaptive.law B (rejectionAttemptCap N) N).prob
        (fun t => CappedSampler.completed (run B (rejectionAttemptCap N) hMB N s t) a₀ ∈ E) -
      s.val.eventProb E| ≤ (1 / 2 : ℝ) ^ 13 :=
  (output_event_error B (rejectionAttemptCap N) hMB N s hN a₀ E).trans
    (rejection_cap_error_real N)

theorem scheduled_output_failure_le {M : ℕ} (B : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N) :
    (CappedSampler.Adaptive.law B (rejectionAttemptCap N) N).prob
      (fun t => run B (rejectionAttemptCap N) hMB N s t = none) ≤ (1 / 2 : ℝ) ^ 13 :=
  (output_failure_le B (rejectionAttemptCap N) hMB N s hN).trans
    (rejection_cap_error_real N)

/-- Bit inspections by the same underlying capped state execution. -/
def inspectedBits {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N) : ℕ :=
  CappedSampler.Adaptive.inspectedBits stateDenominator stateStep B R
    (state_width hMB) N s t

/-- All tapes obey this bit-inspection bound; it is not a running-time bound. -/
theorem inspectedBits_le {M : ℕ} (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N) :
    inspectedBits B R hMB N s t ≤ N * (B * R) :=
  CappedSampler.Adaptive.inspectedBits_le stateDenominator stateStep B R
    (state_width hMB) N s t

end Paper2.RecursiveSamplingCapped

#print axioms Paper2.RecursiveSamplingCapped.idealMass_eq_eventProb
#print axioms Paper2.RecursiveSamplingCapped.event_error
#print axioms Paper2.RecursiveSamplingCapped.runState_pure
#print axioms Paper2.RecursiveSamplingCapped.output_event_error
#print axioms Paper2.RecursiveSamplingCapped.scheduled_output_event_error
#print axioms Paper2.RecursiveSamplingCapped.inspectedBits_le
