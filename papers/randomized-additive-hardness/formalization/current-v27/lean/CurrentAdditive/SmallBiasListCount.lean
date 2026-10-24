import CurrentAdditive.SmallBiasLeastPower

/-!
# Polynomial label count for the abstract array list

Source: v27 `appendices/G-small-bias.tex`,
`yao:deterministic-list-size`. This controls the number of labelled columns;
the executable irreducible-polynomial search and bit-operation clock are
still distinct obligations.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- A fixed-`t` polynomial bound on the number of field-seed labels. The
right side has degree `8·2^t+4` in `H=2^b`; the constant is slightly
larger than the source's displayed `E_t`. -/
theorem source_list_count_polynomial (b t d : ℕ) (ht : 4 ≤ t)
    (hleast : (((2 ^ d) ^ 2 : ℕ) : ℚ) <
      4 * (((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
        sourceBiasQ b t) ^ 2) :
    (((2 ^ d) ^ 2 : ℕ) : ℚ) <
      4 *
        (((((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) *
          (2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 2)) *
          ((2 : ℚ) ^ b) ^ (4 * 2 ^ t + 2)) ^ 2) := by
  let H : ℚ := (2 : ℚ) ^ b
  let A : ℚ := (2 ^ t * 2 ^ t + 1 : ℕ)
  let C : ℚ := (2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 2)
  let p : ℕ := 4 * 2 ^ t + 1
  let x : ℚ := ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t
  let M : ℚ := A * C * H ^ (p + 1)
  have hInv : (1 : ℚ) / sourceBiasQ b t ≤ C * H ^ p := by
    simpa only [sourceBiasQ, C, H, p] using source_inverse_bias_polynomial b t ht
  have hn0 : (0 : ℚ) ≤ (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) := by positivity
  have hx : x ≤ M := by
    calc
      x = (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) *
          ((1 : ℚ) / sourceBiasQ b t) := by dsimp [x]; ring
      _ ≤ (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) * (C * H ^ p) :=
        mul_le_mul_of_nonneg_left hInv hn0
      _ = M := by dsimp [M, A, H, p]; push_cast; rw [pow_succ]; ring
  have hεpos : 0 < sourceBiasQ b t := by
    unfold sourceBiasQ
    positivity
  have hxpos : 0 ≤ x := by dsimp [x]; positivity
  have hsq : x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hxpos hx 2
  change (((2 ^ d) ^ 2 : ℕ) : ℚ) < 4 * M ^ 2
  linarith

/-- A finite field list with polynomially many labelled columns and the
actual v27 NO communication gap exists for every source instance. The
choice is mathematical; no executable list printer is asserted. -/
theorem exists_polynomial_size_field_matrix_gap
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      (((2 ^ d) ^ 2 : ℕ) : ℚ) <
        4 *
          (((((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) *
            (2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 2)) *
            ((2 : ℚ) ^ b) ^ (4 * 2 ^ t + 2)) ^ 2) ∧
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) := by
  obtain ⟨d, hd, _, hsize, hgap⟩ :=
    exists_least_field_matrix_gap b t ht edges index hno
  exact ⟨d, hd, source_list_count_polynomial b t d ht hsize, hgap⟩

#print axioms CurrentAdditive.SmallBias.source_list_count_polynomial
#print axioms CurrentAdditive.SmallBias.exists_polynomial_size_field_matrix_gap

end CurrentAdditive.SmallBias
