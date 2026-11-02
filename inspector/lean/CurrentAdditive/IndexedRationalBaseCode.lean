import Paper2.GeneratorSource

/-! Physical syntax for rational weighted indexed choices. The index,
not the decoded label, is the sampled outcome, so duplicate labels remain
distinct. -/

namespace Paper2.IndexedRationalBaseCode

open Paper2.GeneratorCode Paper2.RecursiveSamplingProgram

private theorem sum_if_lt (a b : ℕ) (x y : ℝ) :
    (∑ i : Fin (a + b), if i.val < a then x else y) =
      (a : ℝ) * x + (b : ℝ) * y := by
  rw [Fin.sum_univ_add]
  simp [Fin.castAdd, Fin.natAdd, Finset.sum_const]

/-- Two positive integer masses, with values kept as indexed encoded words. -/
def binaryCode (a b : ℕ) (bits₀ bits₁ : List Bool) : Code :=
  .branch3 (a + b) a (a + b) (.emit bits₀) (.emit bits₁) (.emit [])

theorem binaryCode_expect (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (bits₀ bits₁ : List Bool) (f : List Bool → ℝ) :
    Program.expect (meaning (binaryCode a b bits₀ bits₁)) f =
      ((a : ℝ) * f bits₀ + (b : ℝ) * f bits₁) / (a + b) := by
  have hab : 0 < a + b := by omega
  cases h : a + b with
  | zero => omega
  | succ z =>
    simp only [binaryCode, meaning, h, Program.expect_draw]
    have hs : (∑ i : Fin (a + b),
        if i.val < a then f bits₀ else if i.val < a + b then f bits₁ else f []) =
        (a : ℝ) * f bits₀ + (b : ℝ) * f bits₁ := by
      simp only [Fin.isLt, ↓reduceIte]
      exact sum_if_lt a b (f bits₀) (f bits₁)
    rw [← h]
    have hs' : (∑ i : Fin (a + b),
        (if i.val < a then Program.pure bits₀
          else if i.val < a + b then Program.pure bits₁ else Program.pure []).expect f) =
        (∑ i : Fin (a + b),
          if i.val < a then f bits₀ else if i.val < a + b then f bits₁ else f []) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    rw [hs', hs]
    simp only [Nat.cast_add, div_eq_mul_inv]
    rw [← one_div]
    ring

/-- Exact rational branch for two arbitrary continuation programs. -/
def branchCode (a b : ℕ) (first second : Code) : Code :=
  .branch3 (a + b) a (a + b) first second (.emit [])

theorem branchCode_expect (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (first second : Code) (f : List Bool → ℝ) :
    Program.expect (meaning (branchCode a b first second)) f =
      ((a : ℝ) * Program.expect (meaning first) f +
        (b : ℝ) * Program.expect (meaning second) f) / (a + b) := by
  have hab : 0 < a + b := by omega
  cases h : a + b with
  | zero => omega
  | succ z =>
    simp only [branchCode, meaning, h, Program.expect_draw]
    have hs : (∑ i : Fin (a + b),
        if i.val < a then Program.expect (meaning first) f
        else if i.val < a + b then Program.expect (meaning second) f else f []) =
        (a : ℝ) * Program.expect (meaning first) f +
          (b : ℝ) * Program.expect (meaning second) f := by
      simp only [Fin.isLt, ↓reduceIte]
      exact sum_if_lt a b _ _
    rw [← h]
    have hs' : (∑ i : Fin (a + b),
        (if i.val < a then meaning first
          else if i.val < a + b then meaning second else Program.pure []).expect f) =
        (∑ i : Fin (a + b),
          if i.val < a then Program.expect (meaning first) f
          else if i.val < a + b then Program.expect (meaning second) f else f []) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    rw [hs', hs]
    simp only [Nat.cast_add, div_eq_mul_inv]
    rw [← one_div]
    ring

#print axioms binaryCode_expect
#print axioms branchCode_expect

end Paper2.IndexedRationalBaseCode
