import CurrentAdditive.SmallBiasExactCoefficient

/-!
# Literal v27 Appendix G list-size coefficient

Source: `appendices/G-small-bias.tex`, `yao:deterministic-list-size`.
The labelled count bound is finite mathematical size accounting; no
bit-operation clock is asserted.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- The manuscript's exact fixed-`t` coefficient `E_t=2^(12st+3t+1)`
and exponent `8s+4` in `H=2^b`. -/
theorem source_list_count_polynomial_exact (b t d : ℕ) (ht : 4 ≤ t)
    (hleast : (((2 ^ d) ^ 2 : ℕ) : ℚ) <
      4 * (((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
        sourceBiasQ b t) ^ 2) :
    (((2 ^ d) ^ 2 : ℕ) : ℚ) <
      4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
        ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
        ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) := by
  let H : ℚ := (2 : ℚ) ^ b
  let A : ℚ := (2 ^ t * 2 ^ t + 1 : ℕ)
  let C : ℚ := (2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)
  let p : ℕ := 4 * 2 ^ t + 1
  let x : ℚ := ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t
  let M : ℚ := A * C * H ^ (p + 1)
  have hInv : (1 : ℚ) / sourceBiasQ b t < C * H ^ p := by
    simpa only [sourceBiasQ, C, H, p] using
      source_inverse_bias_polynomial_exact b t ht
  have hn0 : (0 : ℚ) < (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) := by positivity
  have hx : x < M := by
    calc
      x = (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) *
          ((1 : ℚ) / sourceBiasQ b t) := by dsimp [x]; ring
      _ < (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) * (C * H ^ p) :=
        mul_lt_mul_of_pos_left hInv hn0
      _ = M := by dsimp [M, A, H, p]; push_cast; rw [pow_succ]; ring
  have hxpos : 0 ≤ x := by dsimp [x, sourceBiasQ]; positivity
  have hsq : x ^ 2 < M ^ 2 := by
    have hprod : 0 < (M - x) * (M + x) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hsize : (((2 ^ d) ^ 2 : ℕ) : ℚ) < 4 * M ^ 2 := by
    calc
      _ < 4 * x ^ 2 := hleast
      _ < 4 * M ^ 2 := by nlinarith
  have hpower : (H ^ (p + 1)) ^ 2 = H ^ (8 * 2 ^ t + 4) := by
    rw [← pow_mul]
    congr 1
    dsimp [p]
    omega
  dsimp [M, A, C] at hsize
  rw [mul_pow, mul_pow, hpower] at hsize
  convert hsize using 1
  ring

/-- An actual full-selector matrix gap together with the displayed
strict list-size bound, for the least adequate binary field order. -/
theorem exists_exact_polynomial_size_field_matrix_gap
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      (((2 ^ d) ^ 2 : ℕ) : ℚ) <
        4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) ∧
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) := by
  obtain ⟨d, hd, _, hsize, hgap⟩ :=
    exists_least_field_matrix_gap b t ht edges index hno
  exact ⟨d, hd, source_list_count_polynomial_exact b t d ht hsize, hgap⟩

#print axioms CurrentAdditive.SmallBias.source_list_count_polynomial_exact
#print axioms CurrentAdditive.SmallBias.exists_exact_polynomial_size_field_matrix_gap

end CurrentAdditive.SmallBias
