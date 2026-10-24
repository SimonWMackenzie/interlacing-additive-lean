import CurrentAdditive.SmallBiasFieldMatrix

/-!
# Existence of a sufficient finite field for the v27 finite gap

This file closes the purely finite mathematical choice `R=2^d≥n₀/ε`.
It does not establish the least such `R` or the manuscript's polynomial
printer and bit-operation bound.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

theorem exists_sufficient_binary_field (b t : ℕ) :
    ∃ d : ℕ, 0 < d ∧
      ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
        (2 ^ d : ℚ) := by
  obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt
    (((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t)
    (by norm_num : (1 : ℚ) < 2)
  refine ⟨d + 1, by omega, ?_⟩
  have hp : (2 : ℚ) ^ d ≤ (2 : ℚ) ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact hd.le.trans hp

/-- The finite mathematical NO gap for some explicitly sized binary field
list, with every vector/field seed as a distinct column label. The witness
is abstract, so this does not claim a uniform printing algorithm. -/
theorem exists_indexed_field_matrix_gap
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) := by
  obtain ⟨d, hd, hR⟩ := exists_sufficient_binary_field b t
  exact ⟨d, hd, lower_bound_indexed_field_matrix b t d ht hd hR edges index hno⟩

#print axioms CurrentAdditive.SmallBias.exists_sufficient_binary_field
#print axioms CurrentAdditive.SmallBias.exists_indexed_field_matrix_gap

end CurrentAdditive.SmallBias
