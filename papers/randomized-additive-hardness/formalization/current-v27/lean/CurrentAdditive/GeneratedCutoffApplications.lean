import CurrentAdditive.GeneratedCutoff

namespace GeneratedCutoff

open V38Schedule V38Cutoff

/-- A dyadic source-coordinate width actually divides the generated width. -/
theorem source_width_dvd (L n m Δ : ℕ)
    (hn : n ≤ generatedN L) (hdegree : 2 * m ≤ Δ * n)
    (hL : 4 * Δ + 4 ≤ L) :
    pow2Ceil (4 * generatedS L * m) ∣ generatedQ₂ L := by
  have hwidth := generated_source_width L n m Δ hn hdegree hL
  have hq : generatedQ₂ L = 2 ^ (4 * L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  have hcount : 4 * generatedS L * m ≤ generatedQ₂ L :=
    (Nat.le_pow_clog (by decide) _).trans hwidth
  have hclog : Nat.clog 2 (4 * generatedS L * m) ≤ 4 * L :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (by simpa only [hq] using hcount)
  unfold pow2Ceil
  rw [hq]
  exact Nat.pow_dvd_pow 2 hclog

/-- A concrete passing exponent at or above the input's dyadic ceiling. -/
def chosenLog (n Δ : ℕ) (c : ℚ) : ℕ :=
  max (Nat.clog 2 n) (cutoffLog Δ c)

theorem chosenLog_size (n Δ : ℕ) (c : ℚ) :
    n ≤ generatedN (chosenLog n Δ c) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) n
  exact h.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))

/-- The existential required by the old first-passing search is now derived
from the fixed source promise, rather than supplied as a premise. -/
theorem exists_passing (γ c : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ / (4 * Δ)) (sourceZeta γ / 256)) / 2 ^ 16)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ Δ * n) :
    ∃ L, Nat.clog 2 n ≤ L ∧
      GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ) := by
  refine ⟨chosenLog n Δ c, le_max_left _ _, ?_⟩
  exact all_large_sources γ c Δ hγ hΔ hc hcmax _ n m (le_max_right _ _)
    hn (chosenLog_size n Δ c) hlow hdegree

/-- The first passing exponent cannot exceed the explicit passing exponent. -/
theorem first_passing_le (γ c : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ / (4 * Δ)) (sourceZeta γ / 256)) / 2 ^ 16)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ Δ * n) :
    firstGeneratedExponent c n m (sourceDeltaV γ Δ n m) (sourceZeta γ)
      (exists_passing γ c Δ n m hγ hΔ hc hcmax hn hlow hdegree) ≤
      chosenLog n Δ c := by
  apply Nat.find_min'
  exact ⟨le_max_left _ _, all_large_sources γ c Δ hγ hΔ hc hcmax _ n m
    (le_max_right _ _) hn (chosenLog_size n Δ c) hlow hdegree⟩

theorem chosen_dyadic_bound (n Δ : ℕ) (c : ℚ) (hn : 0 < n) :
    generatedN (chosenLog n Δ c) ≤ 2 * max n (generatedN (cutoffLog Δ c)) := by
  let k := cutoffLog Δ c
  let t := Nat.clog 2 n
  rcases le_total k t with hkt | htk
  · have hchoose : chosenLog n Δ c = t := max_eq_left hkt
    rw [hchoose]
    have hceil : generatedN t < 2 * n := by
      exact Paper2.SourcePadding.powTwoCeil_lt_two_mul hn
    exact hceil.le.trans (Nat.mul_le_mul_left 2 (le_max_left _ _))
  · have hchoose : chosenLog n Δ c = k := max_eq_right htk
    rw [hchoose]
    have hmax : generatedN k ≤ max n (generatedN k) := le_max_right _ _
    change generatedN k ≤ 2 * max n (generatedN k)
    omega

theorem first_passing_dyadic_bound (γ c : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ / (4 * Δ)) (sourceZeta γ / 256)) / 2 ^ 16)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ Δ * n) :
    generatedN (firstGeneratedExponent c n m (sourceDeltaV γ Δ n m) (sourceZeta γ)
      (exists_passing γ c Δ n m hγ hΔ hc hcmax hn hlow hdegree)) ≤
      2 * max n (generatedN (cutoffLog Δ c)) := by
  exact (Nat.pow_le_pow_right (by decide)
    (first_passing_le γ c Δ n m hγ hΔ hc hcmax hn hlow hdegree)).trans
      (chosen_dyadic_bound n Δ c hn)

#print axioms source_width_dvd
#print axioms chosenLog_size
#print axioms exists_passing
#print axioms first_passing_le
#print axioms chosen_dyadic_bound
#print axioms first_passing_dyadic_bound

end GeneratedCutoff
