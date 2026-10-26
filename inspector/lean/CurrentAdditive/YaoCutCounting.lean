import CurrentAdditive.YaoDegreeArithmetic

/-! The exact cut is the number of positive feasible candidates encountered
in the finite scan. This prepares the invariant for a physical unary-fuel loop. -/

namespace CurrentAdditive.SmallBias.YaoCutCounting

theorem feasible_antitone (b t j k : ℕ) (hjk : j ≤ k)
    (hk : sourceCutFeasible b t k) : sourceCutFeasible b t j := by
  unfold sourceCutFeasible at *
  have hp : 2 ^ j ≤ 2 ^ k :=
    pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hjk
  have hf : t + j - 2 ≤ t + k - 2 := by omega
  exact (Nat.mul_le_mul hp hf).trans hk

def cutCount (b t : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => cutCount b t m + if sourceCutFeasible b t (m + 1) then 1 else 0

theorem feasible_iff_le_cut (b t j : ℕ) (ht : 4 ≤ t) :
    sourceCutFeasible b t j ↔ j ≤ sourceCutIndex b t := by
  constructor
  · intro hj
    exact (sourceCutIndex_spec b t ht).2.2 j hj
  · intro hj
    exact feasible_antitone b t j (sourceCutIndex b t) hj
      (sourceCutIndex_spec b t ht).1

theorem cutCount_min (b t m : ℕ) (ht : 4 ≤ t) :
    cutCount b t m = min m (sourceCutIndex b t) := by
  induction m with
  | zero => simp [cutCount]
  | succ m ih =>
      rw [cutCount, ih]
      by_cases h : m + 1 ≤ sourceCutIndex b t
      · have hf := (feasible_iff_le_cut b t (m + 1) ht).2 h
        rw [Nat.min_eq_left (by omega : m ≤ sourceCutIndex b t),
          Nat.min_eq_left h]
        simp [hf]
      · have hf : ¬ sourceCutFeasible b t (m + 1) := by
          intro hh
          exact h ((feasible_iff_le_cut b t (m + 1) ht).1 hh)
        have hi : sourceCutIndex b t ≤ m := by omega
        rw [Nat.min_eq_right hi,
          Nat.min_eq_right (by omega : sourceCutIndex b t ≤ m + 1)]
        simp [hf]

theorem cutCount_full (b t : ℕ) (ht : 4 ≤ t) :
    cutCount b t (sourcePairDepth b t) = sourceCutIndex b t := by
  rw [cutCount_min b t _ ht]
  exact Nat.min_eq_right (Nat.le_of_lt (sourceCutIndex_spec b t ht).2.1)

#print axioms feasible_antitone
#print axioms cutCount_full

end CurrentAdditive.SmallBias.YaoCutCounting
