import CurrentAdditive.V39PublicSchedule

/-! Consequences of the literal v39 integer schedule. No semantic matrix
iteration, promise test termination, or machine-resource claim is hidden. -/

namespace V39PublicSchedule

open V38Schedule

theorem rankBound_zero (L : ℕ) : rankBound L 0 = seedWidth L := by
  unfold rankBound
  rw [B_zero, seedWidth_exact]
  unfold seedCost
  congr 1
  omega

theorem B_le_linear (L k : ℕ) (hseed : seedCost L ≤ L)
    (hhead : fullOverhead L ≤ 7 * L) : B L k ≤ (7 * k + 1) * L := by
  unfold B
  have h := Nat.mul_le_mul_left k hhead
  nlinarith only [hseed, h]

theorem H_le_linear (L k : ℕ) (hL : 1 ≤ L)
    (hseed : seedCost L ≤ L) (hhead : fullOverhead L ≤ 7 * L) :
    H L k ≤ (8 * k + 1) * L := by
  have hb := B_le_linear L k hseed hhead
  have hk : k ≤ k * L := Nat.le_mul_of_pos_right k hL
  unfold H
  nlinarith only [hb, hk]

theorem fullTests_iteration_bounds (c : ℚ) (L m k : ℕ) (δv ζ : ℚ)
    (htest : FullTests c L m δv ζ) :
    B L k ≤ (7 * k + 1) * L ∧ H L k ≤ (8 * k + 1) * L := by
  obtain ⟨_, _, hL, hseed, hhead⟩ := htest
  have hseed' : seedCost L ≤ L := hseed
  have hhead' : fullOverhead L ≤ 7 * L := hhead
  exact ⟨B_le_linear L k hseed' hhead',
    H_le_linear L k (by omega) hseed' hhead'⟩

theorem generatedOverhead_le_linear (L : ℕ) :
    generatedOverhead L ≤ 13 * L + 2 := by
  have h := quarterCeil_rounding L
  unfold generatedOverhead
  omega

theorem sample_square_dyadic (L k : ℕ) :
    ∃ z : ℕ, sampleSide L k = 2 ^ z ∧
      sampleEntries L k = 2 ^ (2 * z) ∧
      Nat.clog 2 (sampleEntries L k) = 2 * z := by
  let z := Nat.clog 2 (16 * (rankBound L k + 1) *
    Nat.clog 2 (rankBound L k + 2) * 2 ^ H L k)
  have hm : sampleSide L k = 2 ^ z := rfl
  have hT : sampleEntries L k = 2 ^ (2 * z) := by
    unfold sampleEntries
    rw [hm, ← pow_mul]
    congr 1
    omega
  exact ⟨z, hm, hT, by rw [hT, Nat.clog_pow 2 _ (by decide)]⟩

#print axioms rankBound_zero
#print axioms B_le_linear
#print axioms H_le_linear
#print axioms fullTests_iteration_bounds
#print axioms generatedOverhead_le_linear
#print axioms sample_square_dyadic

end V39PublicSchedule
