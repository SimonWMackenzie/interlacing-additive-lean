import CurrentAdditive.SmallBiasEpsilonSize
import CurrentAdditive.SmallBiasFieldExistence

/-!
# The least sufficient dyadic field size

Source: v27 `appendices/G-small-bias.tex`, choice of the least power of two
`R≥n₀/ε`. This concerns the mathematical size of the abstract field, not
the search, quotient arithmetic, or bit-operation implementation.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

/-- A positive rational target above one has a least sufficient power of
two. That power is strictly less than twice the target. -/
theorem exists_least_binary_power (x : ℚ) (hx : 1 < x) :
    ∃ d : ℕ, 0 < d ∧ x ≤ (2 : ℚ) ^ d ∧ (2 : ℚ) ^ d < 2 * x := by
  have hex : ∃ d : ℕ, x ≤ (2 : ℚ) ^ d := by
    obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℚ) < 2)
    exact ⟨d, hd.le⟩
  let d := Nat.find hex
  have hgood : x ≤ (2 : ℚ) ^ d := Nat.find_spec hex
  have hd : 0 < d := by
    by_contra hn
    have hz : d = 0 := by omega
    rw [hz] at hgood
    norm_num at hgood
    linarith
  have hprev : (2 : ℚ) ^ (d - 1) < x := by
    by_contra hn
    have hm : x ≤ (2 : ℚ) ^ (d - 1) := le_of_not_gt hn
    exact (Nat.find_min hex (show d - 1 < d by omega)) hm
  have he : d - 1 + 1 = d := by omega
  have hpow : (2 : ℚ) ^ d = 2 * (2 : ℚ) ^ (d - 1) := by
    calc
      _ = (2 : ℚ) ^ (d - 1 + 1) := congrArg _ he.symm
      _ = 2 * (2 : ℚ) ^ (d - 1) := by rw [pow_succ]; ring
  exact ⟨d, hd, hgood, by rw [hpow]; linarith⟩

/-- The source target `n₀/ε` is above one, so the least-power estimate
applies without an asymptotic lower bound on `H`. -/
theorem source_field_target_gt_one (b t : ℕ) :
    (1 : ℚ) <
      ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t := by
  have hεpos : 0 < sourceBiasQ b t := by
    unfold sourceBiasQ
    positivity
  have hεle : sourceBiasQ b t ≤ 1 := by
    unfold sourceBiasQ
    exact pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℚ) ≤ 1)
  have hb : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by decide)
  have hs : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by decide)
  have hn : 2 ≤ 2 ^ b * (2 ^ t * 2 ^ t + 1) := by nlinarith
  have hnq : (2 : ℚ) ≤ (2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) := by
    exact_mod_cast hn
  apply (lt_div_iff₀ hεpos).2
  linarith

/-- The mathematical matrix gap can use the *least* sufficient dyadic field
size. Its number of labelled array columns obeys the source's first
size inequality `R²<4(n₀/ε)²`. -/
theorem exists_least_field_matrix_gap
    {V E : Type*} [Fintype V]
    (b t : ℕ) (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    ∃ d : ℕ, ∃ hd : 0 < d,
      let x : ℚ :=
        ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t
      x ≤ (2 : ℚ) ^ d ∧
      (((2 ^ d) ^ 2 : ℕ) : ℚ) < 4 * x ^ 2 ∧
      (2 * b + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrix (placeEdges edges index)
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (indexedFieldWord b t d hd (binaryBasis d hd))) := by
  let x : ℚ :=
    ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t
  obtain ⟨d, hd, hlow, hhigh⟩ :=
    exists_least_binary_power x (source_field_target_gt_one b t)
  refine ⟨d, hd, ?_, ?_, ?_⟩
  · exact hlow
  · have hRpos : 0 < (2 : ℚ) ^ d := by positivity
    have hxpos : 0 < x := lt_trans (by norm_num) (source_field_target_gt_one b t)
    have hmul : 0 < (2 * x - (2 : ℚ) ^ d) *
        (2 * x + (2 : ℚ) ^ d) := by positivity
    have hcast : (((2 ^ d) ^ 2 : ℕ) : ℚ) = ((2 : ℚ) ^ d) ^ 2 := by
      norm_cast
    rw [hcast]
    nlinarith [hmul]
  · exact lower_bound_indexed_field_matrix b t d ht hd hlow edges index hno

#print axioms CurrentAdditive.SmallBias.exists_least_binary_power
#print axioms CurrentAdditive.SmallBias.source_field_target_gt_one
#print axioms CurrentAdditive.SmallBias.exists_least_field_matrix_gap

end CurrentAdditive.SmallBias
