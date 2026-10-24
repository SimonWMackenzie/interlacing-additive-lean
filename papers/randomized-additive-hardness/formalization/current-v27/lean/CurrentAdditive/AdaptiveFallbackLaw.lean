import CurrentAdditive.AdaptiveFallback

/-!
The all-event law of the total, adaptive per-draw fallback sampler.
Source: `2026-10-12-proof-exposition-v27/source/appendices/D-implementation.tex:84--105`.
-/

namespace Paper2.CappedSampler.Adaptive

variable {S : Type*} (D : S → ℕ) (next : (s : S) → Fin (D s) → S)
  (B R : ℕ) (hB : ∀ s, Nat.clog 2 (D s) ≤ B) (hD : ∀ s, 0 < D s)

/-- The accepted part of the old execution is contained in every event of the
total execution, because the two outputs agree on those tapes. -/
theorem successMass_le_fallback_event (n : ℕ) (s : S) (E : S → Prop) :
    successMass D next B R hB n s E ≤
      (law B R n).prob (fun t => E (runFallback D next B R hB hD n s t)) := by
  apply (law B R n).prob_mono
  intro t ht
  obtain ⟨u, hu, he⟩ := ht
  simpa [runFallback_eq_of_run_eq_some D next B R hB hD n s t u hu] using he

/-- The only extra event mass can lie on a tape where the old interpreter
aborted at a reached elementary draw. -/
theorem fallback_event_le_successMass_add_failure (n : ℕ) (s : S) (E : S → Prop) :
    (law B R n).prob (fun t => E (runFallback D next B R hB hD n s t)) ≤
      successMass D next B R hB n s E +
        (law B R n).prob (fun t => run D next B R hB n s t = none) := by
  classical
  unfold successMass
  simp only [FiniteLaw.prob]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  rcases Option.eq_none_or_eq_some (run D next B R hB n s t) with hr | ⟨u, hr⟩
  · by_cases he : E (runFallback D next B R hB hD n s t)
    · simp [hr, he]
    · simp [hr, he, (law B R n).nonneg t]
  · have hf := runFallback_eq_of_run_eq_some D next B R hB hD n s t u hr
    by_cases he : E u <;> simp [hr, hf, he]

/-- Local fallback preserves the same `N 2^{-R}` all-event coupling bound.
The denominator and continuation may depend on all previous draw values. -/
theorem fallback_event_error (n : ℕ) (s : S) (E : S → Prop) :
    |(law B R n).prob (fun t => E (runFallback D next B R hB hD n s t)) -
        idealMass D next hD n s E| ≤ (n : ℝ) * (1 / 2 : ℝ) ^ R := by
  let actual := (law B R n).prob
    (fun t => E (runFallback D next B R hB hD n s t))
  let successful := successMass D next B R hB n s E
  let ideal := idealMass D next hD n s E
  have hsa : successful ≤ actual :=
    successMass_le_fallback_event D next B R hB hD n s E
  have has : actual ≤ successful + (n : ℝ) * (1 / 2 : ℝ) ^ R :=
    (fallback_event_le_successMass_add_failure D next B R hB hD n s E).trans
      (by dsimp [successful]; gcongr; exact failure_le D next B R hB hD n s)
  have hsi : successful ≤ ideal := success_le_ideal D next B R hB hD n s E
  have his : ideal ≤ successful + (n : ℝ) * (1 / 2 : ℝ) ^ R :=
    ideal_le_success_add_error D next B R hB hD n s E
  exact abs_le.mpr ⟨by dsimp [actual, ideal] at *; linarith,
    by dsimp [actual, ideal] at *; linarith⟩

theorem scheduled_fallback_event_error (N : ℕ) (s : S) (E : S → Prop) :
    |(law B (Paper2.rejectionAttemptCap N) N).prob
      (fun t => E (runFallback D next B
        (Paper2.rejectionAttemptCap N) hB hD N s t)) -
        idealMass D next hD N s E| ≤ (1 / 2 : ℝ) ^ 13 :=
  (fallback_event_error D next B
    (Paper2.rejectionAttemptCap N) hB hD N s E).trans
    (Paper2.rejection_cap_error_real N)

end Paper2.CappedSampler.Adaptive

#print axioms Paper2.CappedSampler.Adaptive.fallback_event_error
#print axioms Paper2.CappedSampler.Adaptive.scheduled_fallback_event_error
