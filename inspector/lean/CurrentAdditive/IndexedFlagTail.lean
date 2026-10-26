import CurrentAdditive.IndexedFlagMoment256

/-! Appendix I `det:incoming`: Markov's inequality for the actual indexed
metadata flags, with the manuscript's order-256 constant. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]
  {D w m : ℕ} {μ : PositiveRationalLaw A}
  (source : CodeSource D w A μ)

private theorem probability_le_even_moment
    {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    (Bad : Ω → Prop) (S : Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (hbad : ∀ ω, Bad ω → t ≤ |S ω|) :
    ν.prob Bad ≤ expectation ν (fun ω => |S ω| ^ 256) / t ^ 256 := by
  have hpow : 0 < t ^ 256 := pow_pos ht _
  apply (le_div_iff₀ hpow).2
  unfold FiniteLaw.prob expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : Bad ω
  · simp only [h, ite_true]
    have hp := pow_le_pow_left₀ ht.le (hbad ω h) 256
    nlinarith [mul_nonneg (ν.nonneg ω) (sub_nonneg.mpr hp)]
  · simp only [h, ite_false, zero_mul]
    exact mul_nonneg (ν.nonneg ω) (pow_nonneg (abs_nonneg _) _)

/-- If every selected metadata flag has mean `λ>1/2`, the probability of
fewer than half template positions has precisely the moment-order bound
used in `det:incoming`. The hypothesis on one-point means is proved from
the actual metadata mixture in the next adapter. -/
theorem indexed_flag_half_tail (hD : 8*256 ≤ D)
    (e : Fin m → Fin w) (he : Function.Injective e)
    (P : A → Bool) (lam : ℝ) (hlam : 1/2 < lam)
    (hmean : ∀ i : Fin m,
      source.law.toFiniteLaw.prob
        (fun seed => P (source.decode seed (e i)) = true) = lam) :
    source.law.toFiniteLaw.prob (fun seed =>
      (∑ i : Fin m, if P (source.decode seed (e i)) then (1 : ℝ) else 0) <
        (m : ℝ) / 2) ≤
      2 * ((64 : ℝ) * m) ^ 128 /
        (((lam - 1/2) * m) ^ 256) := by
  let ν := source.law.toFiniteLaw
  let S : source.Label → ℝ := fun seed =>
    ∑ i : Fin m, ((if P (source.decode seed (e i)) then (1 : ℝ) else 0) -
      ν.prob (fun seed' => P (source.decode seed' (e i)) = true))
  let t : ℝ := (lam - 1/2) * m
  by_cases hm : m = 0
  · subst m
    simp [ν, S, t]
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have ht : 0 < t := by dsimp [t]; positivity
  have hbad (seed : source.Label)
      (hb : (∑ i : Fin m,
        if P (source.decode seed (e i)) then (1 : ℝ) else 0) <
          (m : ℝ) / 2) : t ≤ |S seed| := by
    have hS : S seed =
        (∑ i : Fin m,
          if P (source.decode seed (e i)) then (1 : ℝ) else 0) -
          (m : ℝ) * lam := by
      have hmean' (i : Fin m) :
          ν.prob (fun seed' => P (source.decode seed' (e i)) = true) = lam :=
        hmean i
      simp [S, Finset.sum_sub_distrib, hmean']
    rw [hS]
    have hneg :
        (∑ i : Fin m,
          if P (source.decode seed (e i)) then (1 : ℝ) else 0) -
          (m : ℝ) * lam ≤ 0 := by nlinarith [mul_pos hmpos (sub_pos.mpr hlam)]
    rw [abs_of_nonpos hneg]
    dsimp [t]
    linarith
  have hmarkov := probability_le_even_moment ν
    (fun seed => (∑ i : Fin m,
      if P (source.decode seed (e i)) then (1 : ℝ) else 0) <
        (m : ℝ) / 2) S t ht hbad
  have hmoment := indexed_flag_moment_256 source hD e he P
  calc
    _ ≤ expectation ν (fun seed => |S seed| ^ 256) / t ^ 256 := hmarkov
    _ ≤ (2 * ((64 : ℝ) * m) ^ 128) / t ^ 256 := by
      apply div_le_div_of_nonneg_right (by simpa [S, ν] using hmoment)
      positivity
    _ = _ := rfl

#print axioms indexed_flag_half_tail

end CurrentAdditive.DeterministicIndexedMatrix
