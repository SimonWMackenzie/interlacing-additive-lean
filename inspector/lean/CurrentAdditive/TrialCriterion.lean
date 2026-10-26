import CurrentAdditive.MonicCandidateCoverage

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

theorem trial_iff_no_encoded_factor (d tail : ℕ) :
    TrialSearch.trialIrreducible d tail = true ↔
      ∀ e, 1 ≤ e → e ≤ d / 2 → ∀ t < 2 ^ e,
        TrialSearch.remainder d e (TrialSearch.monicBits e t)
          (TrialSearch.monicBits d tail) ≠ 0 := by
  simp only [TrialSearch.trialIrreducible, List.all_eq_true, List.mem_range]
  constructor
  · intro h e he hed t ht
    have hx : e - 1 < d / 2 := by omega
    have heq : e - 1 + 1 = e := by omega
    simpa [heq] using h (e - 1) hx t (by simpa only [heq] using ht)
  · intro h x hx t ht
    simpa using h (x + 1) (by omega) (by omega) t ht

#print axioms trial_iff_no_encoded_factor

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
