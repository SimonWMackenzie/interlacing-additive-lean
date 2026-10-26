import CurrentAdditive.SmallBiasStopping

/-!
# The maximal cut keeps the finite-field list parameter small

Source: v27 `appendices/G-small-bias.tex`, `yao:deterministic-materialization`,
first displayed inequality `Q < 4s(a+t-1)`. This is numerical size control,
not an implementation or physical runtime bound.
-/

namespace CurrentAdditive.SmallBias

/-- The source's maximal feasible cut leaves a suffix with
`Q=2^h<4·2^t·(a+t−1)`. -/
theorem source_suffix_size_bound (b t : ℕ) (ht : 4 ≤ t) :
    2 ^ sourceSuffixDepth b t <
      4 * 2 ^ t * (sourcePairDepth b t + t - 1) := by
  let i := sourceCutIndex b t
  let h := sourceSuffixDepth b t
  let r := 2 ^ (h - t - 1)
  obtain ⟨hf, hi, hmax⟩ := sourceCutIndex_spec b t ht
  have ha : i + h = b + 2 * t - 2 := by
    dsimp [i, h, sourceSuffixDepth, sourcePairDepth] at *
    omega
  have hh : t + 2 ≤ h := feasible_cut_suffix b t i h ht ha hf
  have hsum : i + (h - t - 1) = t + b - 3 := by omega
  have hsurplus : 2 ^ i * r = 2 ^ (t + b - 3) := by
    dsimp only [r]
    rw [← pow_add, hsum]
  have hnot : ¬ sourceCutFeasible b t (i + 1) := by
    intro h
    have hle := hmax (i + 1) h
    omega
  have hstrict : 2 ^ i * r < 2 ^ (i + 1) * (t + i - 1) := by
    have he : t + (i + 1) - 2 = t + i - 1 := by omega
    unfold sourceCutFeasible at hnot
    rw [he] at hnot
    omega
  have hr : r < 2 * (t + i - 1) := by
    have he : 2 ^ (i + 1) * (t + i - 1) =
        2 ^ i * (2 * (t + i - 1)) := by rw [pow_succ]; ring
    rw [he] at hstrict
    exact Nat.lt_of_mul_lt_mul_left hstrict
  have hpow : 2 ^ h = r * (2 * 2 ^ t) := by
    dsimp only [r]
    have he : (h - t - 1) + (t + 1) = h := by omega
    rw [mul_comm 2 (2 ^ t), ← pow_succ, ← pow_add, he]
  have hlast : t + i - 1 ≤ sourcePairDepth b t + t - 1 := by
    dsimp [i, sourcePairDepth] at *
    omega
  calc
    2 ^ sourceSuffixDepth b t = r * (2 * 2 ^ t) := hpow
    _ < (2 * (t + i - 1)) * (2 * 2 ^ t) :=
      Nat.mul_lt_mul_of_pos_right hr (by positivity)
    _ = 4 * 2 ^ t * (t + i - 1) := by ring
    _ ≤ 4 * 2 ^ t * (sourcePairDepth b t + t - 1) :=
      Nat.mul_le_mul_left _ hlast

#print axioms CurrentAdditive.SmallBias.source_suffix_size_bound

end CurrentAdditive.SmallBias
