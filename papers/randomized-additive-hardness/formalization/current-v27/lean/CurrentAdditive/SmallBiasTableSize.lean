import CurrentAdditive.SmallBiasMidpoint

/-!
# Effective finite table dimensions and scalar output length

Source: v27 Appendix G `yao:deterministic-table-size`. This is an
arithmetic upper bound on the number of Boolean entries in the exact
table shape, conditional on the already checked list-size inequality.
The physical program and its bit-operation clock remain separate.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- The actual number of row/column pairs is bounded by multiplying the
exact full-selector and field-list counts. The nonempty vertex premise
matches the source and makes the strict bound meaningful. -/
theorem printed_pair_table_entries_bound
    {V : Type} [Fintype V] [Nonempty V]
    (b t d : ℕ)
    (hsize : (((2 ^ d) ^ 2 : ℕ) : ℚ) <
      4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
        ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
        ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4)) :
    ((Fintype.card (V × Fin (Fintype.card
        (Fin (2 ^ (t - 1)) → Fin (2 ^ b)))) *
      Fintype.card (Fin (2 ^ (t - 1)) × Fin (2 ^ b) ×
        Fin ((2 ^ d) ^ 2)) : ℕ) : ℚ) <
      ((Fintype.card V : ℕ) : ℚ) *
        ((2 : ℚ) ^ b) ^ (2 ^ (t - 1)) *
        (2 ^ (t - 1) : ℕ) * ((2 : ℚ) ^ b) *
        (4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4)) := by
  obtain ⟨hrows, hcols⟩ := printed_pair_matrix_dimensions (V := V) b t d
  let factor : ℚ := (Fintype.card V : ℚ) *
    ((2 : ℚ) ^ b) ^ (2 ^ (t - 1)) *
    (2 ^ (t - 1) : ℕ) * ((2 : ℚ) ^ b)
  have hfactor : 0 < factor := by
    dsimp [factor]
    positivity
  have heq :
      ((Fintype.card (V × Fin (Fintype.card
          (Fin (2 ^ (t - 1)) → Fin (2 ^ b)))) *
        Fintype.card (Fin (2 ^ (t - 1)) × Fin (2 ^ b) ×
          Fin ((2 ^ d) ^ 2)) : ℕ) : ℚ) =
        factor * (((2 ^ d) ^ 2 : ℕ) : ℚ) := by
    rw [hrows, hcols]
    dsimp [factor]
    push_cast
    ring
  rw [heq]
  exact mul_lt_mul_of_pos_left hsize hfactor

#print axioms CurrentAdditive.SmallBias.printed_pair_table_entries_bound

end CurrentAdditive.SmallBias
