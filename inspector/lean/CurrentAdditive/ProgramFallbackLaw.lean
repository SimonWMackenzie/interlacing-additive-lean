import CurrentAdditive.AdaptiveFallbackLaw

/-!
Program-level event law and leaf validity for the total per-draw sampler.
The generic `Program A` constructor already carries a positive current
alphabet at every draw. Validity is inherited from all source leaves.
-/

namespace Paper2.RecursiveSamplingCapped

open RecursiveSamplingProgram

variable {A : Type*}

theorem runProgramFallback_event_iff {M : ℕ} (B R : ℕ)
    (hMB : Nat.clog 2 M ≤ B) (N : ℕ) (s : State A M)
    (hN : s.val.maxDraws ≤ N) (t : CappedSampler.Adaptive.Tape B R N)
    (E : Set A) :
    runProgramFallback B R hMB N s hN t ∈ E ↔
      outputEvent E (runStateFallback B R hMB N s t).val := by
  obtain ⟨a, ha⟩ := runStateFallback_pure B R hMB N s hN t
  simp [runProgramFallback_eq_leaf B R hMB N s hN t a ha, ha, outputEvent]

/-- The total sampler has the manuscript's all-event loss bound. The law is
over one fixed product of `N` public bit blocks, including exhausted tapes. -/
theorem runProgramFallback_event_error {M : ℕ} (B R : ℕ)
    (hMB : Nat.clog 2 M ≤ B) (N : ℕ) (s : State A M)
    (hN : s.val.maxDraws ≤ N) (E : Set A) :
    |(CappedSampler.Adaptive.law B R N).prob
        (fun t => runProgramFallback B R hMB N s hN t ∈ E) -
        s.val.eventProb E| ≤ (N : ℝ) * (1 / 2 : ℝ) ^ R := by
  have h := CappedSampler.Adaptive.fallback_event_error
    stateDenominator stateStep B R (state_width hMB) stateDenominator_pos
    N s (fun u => outputEvent E u.val)
  change |(CappedSampler.Adaptive.law B R N).prob
      (fun t => outputEvent E (runStateFallback B R hMB N s t).val) -
      idealMass N s E| ≤ _ at h
  rw [idealMass_eq_eventProb N s hN E] at h
  have he : (CappedSampler.Adaptive.law B R N).prob
      (fun t => outputEvent E (runStateFallback B R hMB N s t).val) =
      (CappedSampler.Adaptive.law B R N).prob
        (fun t => runProgramFallback B R hMB N s hN t ∈ E) := by
    congr 1
    funext t
    exact propext (runProgramFallback_event_iff B R hMB N s hN t E).symm
  rwa [he] at h

theorem scheduled_runProgramFallback_event_error {M : ℕ} (B : ℕ)
    (hMB : Nat.clog 2 M ≤ B) (N : ℕ) (s : State A M)
    (hN : s.val.maxDraws ≤ N) (E : Set A) :
    |(CappedSampler.Adaptive.law B (rejectionAttemptCap N) N).prob
        (fun t => runProgramFallback B (rejectionAttemptCap N) hMB N s hN t ∈ E) -
        s.val.eventProb E| ≤ (1 / 2 : ℝ) ^ 13 :=
  (runProgramFallback_event_error B (rejectionAttemptCap N) hMB N s hN E).trans
    (rejection_cap_error_real N)

/-- A semantic validity invariant on all possible finished labels of a
finite-choice program, independent of which choices the tape makes. -/
def LeavesSatisfy (P : A → Prop) : Program A → Prop
  | .pure a => P a
  | .draw _ _ next => ∀ i, LeavesSatisfy P (next i)

theorem leavesSatisfy_step (P : A → Prop) (p : Program A)
    (hp : LeavesSatisfy P p) (i : Fin (denominator p)) :
    LeavesSatisfy P (step p i) := by
  cases p with
  | pure a => simpa [denominator, step, LeavesSatisfy] using hp
  | draw n hn next => exact hp i

theorem runStateFallback_leavesSatisfy {M : ℕ} (B R : ℕ)
    (hMB : Nat.clog 2 M ≤ B) (N : ℕ) (s : State A M)
    (P : A → Prop) (hs : LeavesSatisfy P s.val)
    (t : CappedSampler.Adaptive.Tape B R N) :
    LeavesSatisfy P (runStateFallback B R hMB N s t).val := by
  induction N generalizing s with
  | zero => simpa [runStateFallback, CappedSampler.Adaptive.runFallback] using hs
  | succ N ih =>
      let i : Fin (stateDenominator s) :=
        (CappedSampler.runWideBits (stateDenominator s) B R
          (state_width hMB s) t.1).getD ⟨0, stateDenominator_pos s⟩
      have hnext := leavesSatisfy_step P s.val hs i
      have hrec := ih (stateStep s i) hnext t.2
      change LeavesSatisfy P (runStateFallback B R hMB N (stateStep s i) t.2).val at hrec
      simpa [runStateFallback, CappedSampler.Adaptive.runFallback, i] using hrec

/-- If every leaf is an original valid label, every tape returns one. -/
theorem runProgramFallback_valid {M : ℕ} (B R : ℕ)
    (hMB : Nat.clog 2 M ≤ B) (N : ℕ) (s : State A M)
    (hN : s.val.maxDraws ≤ N) (P : A → Prop)
    (hs : LeavesSatisfy P s.val)
    (t : CappedSampler.Adaptive.Tape B R N) :
    P (runProgramFallback B R hMB N s hN t) := by
  obtain ⟨a, ha⟩ := runStateFallback_pure B R hMB N s hN t
  have hv := runStateFallback_leavesSatisfy B R hMB N s P hs t
  simpa [ha, LeavesSatisfy, runProgramFallback_eq_leaf B R hMB N s hN t a ha] using hv

end Paper2.RecursiveSamplingCapped

#print axioms Paper2.RecursiveSamplingCapped.runProgramFallback_event_error
#print axioms Paper2.RecursiveSamplingCapped.scheduled_runProgramFallback_event_error
#print axioms Paper2.RecursiveSamplingCapped.runProgramFallback_valid
