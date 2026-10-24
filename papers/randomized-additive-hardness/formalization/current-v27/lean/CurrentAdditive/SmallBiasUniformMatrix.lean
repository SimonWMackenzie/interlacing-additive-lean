import CurrentAdditive.SmallBiasYes

/-!
# One matrix chosen independently of the source promise

Source: v27 `sections/07-yao.tex`, `yao:entry` and `yao:lift`;
`appendices/G-small-bias.tex`, `yao:deterministic-list-size`.
The least adequate field size depends only on `b,t`, not on whether the
source is a YES or NO instance.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- Select the least sufficient dyadic order solely from the public
parameters, with the source's exact displayed list-size coefficient. -/
theorem exists_v27_field_parameters (b t : ℕ) (ht : 4 ≤ t) :
    ∃ d : ℕ, ∃ _hd : 0 < d,
      ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
          sourceBiasQ b t ≤ (2 : ℚ) ^ d ∧
      (((2 ^ d) ^ 2 : ℕ) : ℚ) <
        4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) := by
  let x : ℚ :=
    ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t
  obtain ⟨d, hd, hlow, hhigh⟩ :=
    exists_least_binary_power x (source_field_target_gt_one b t)
  have hRpos : 0 < (2 : ℚ) ^ d := by positivity
  have hxpos : 0 < x := lt_trans (by norm_num) (source_field_target_gt_one b t)
  have hmul : 0 < (2 * x - (2 : ℚ) ^ d) *
      (2 * x + (2 : ℚ) ^ d) := by positivity
  have hcast : (((2 ^ d) ^ 2 : ℕ) : ℚ) = ((2 : ℚ) ^ d) ^ 2 := by
    norm_cast
  have hleast : (((2 ^ d) ^ 2 : ℕ) : ℚ) < 4 * x ^ 2 := by
    rw [hcast]
    nlinarith [hmul]
  exact ⟨d, hd, hlow,
    source_list_count_polynomial_exact b t d ht hleast⟩

/-- The exact public matrix selected without inspecting a colouring or
protocol. YES and NO implications apply to that same matrix. -/
theorem exists_uniform_v27_field_matrix
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b)) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      (((2 ^ d) ^ 2 : ℕ) : ℚ) <
        4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
          ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
          ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) ∧
      (∀ colour : V → Fin (2 ^ t),
        (∀ e c, 2 ^ t - 1 ≤
          colourFiberCard (fun i => colour (edges e i)) c) →
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) ≤
          2 * b + 4 * t + 2) ∧
      ((∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
          ∃ e c, ∀ i, colour (edges e i) = c) →
        (2 * b + 4 * t + 2) + 2 * t - 6 ≤
          Dalt .alice (matrix (placeEdges edges index)
            (fullSelector (2 ^ (t - 1)) (2 ^ b))
            (indexedFieldWord b t d hd (binaryBasis d hd)))) := by
  obtain ⟨d, hd, hR, hsize⟩ := exists_v27_field_parameters b t ht
  refine ⟨d, hd, hsize, ?_, ?_⟩
  · intro colour hbalanced
    exact balanced_yes_indexed_field_matrix b t d ht hd
      edges index colour hbalanced
  · intro hno
    exact lower_bound_indexed_field_matrix b t d ht hd hR
      edges index hno

#print axioms CurrentAdditive.SmallBias.exists_v27_field_parameters
#print axioms CurrentAdditive.SmallBias.exists_uniform_v27_field_matrix

end CurrentAdditive.SmallBias
