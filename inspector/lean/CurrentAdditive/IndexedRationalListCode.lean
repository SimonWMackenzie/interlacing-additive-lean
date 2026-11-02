import CurrentAdditive.IndexedRationalBaseCode

/-! An arbitrary finite indexed list of positive integer masses compiled
into first-order rational-choice syntax. Values are bit words and may repeat;
the intended use emits an index word, then decodes its label separately. -/

namespace Paper2.IndexedRationalListCode

open Paper2.GeneratorCode Paper2.RecursiveSamplingProgram
open Paper2.IndexedRationalBaseCode

def total : List (ℕ × List Bool) → ℕ
  | [] => 0
  | x :: xs => x.1 + total xs

def payoff (f : List Bool → ℝ) : List (ℕ × List Bool) → ℝ
  | [] => 0
  | x :: xs => (x.1 : ℝ) * f x.2 + payoff f xs

def compile : List (ℕ × List Bool) → Code
  | [] => .emit []
  | [x] => .emit x.2
  | x :: y :: ys => branchCode x.1 (total (y :: ys))
      (.emit x.2) (compile (y :: ys))

theorem total_pos {xs : List (ℕ × List Bool)} (hne : xs ≠ [])
    (hp : ∀ x ∈ xs, 0 < x.1) : 0 < total xs := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
    have hx := hp x (by simp)
    simp only [total]
    omega

/-- Exact weighted expectation of any payoff under the compiled code. -/
theorem compile_expect {xs : List (ℕ × List Bool)} (hne : xs ≠ [])
    (hp : ∀ x ∈ xs, 0 < x.1) (f : List Bool → ℝ) :
    Program.expect (meaning (compile xs)) f = payoff f xs / total xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hx : 0 < x.1 := hp x (by simp)
      simp only [compile, meaning, Program.expect_pure, payoff, total,
        add_zero]
      have hxn : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hx)
      field_simp
    | cons y ys =>
      have hx : 0 < x.1 := hp x (by simp)
      have htailp : ∀ z ∈ y :: ys, 0 < z.1 := by
        intro z hz
        exact hp z (by simp [hz])
      have htail : 0 < total (y :: ys) := total_pos (by simp) htailp
      have htailR : (total (y :: ys) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt htail)
      have ih' := ih (by simp) htailp
      rw [compile, branchCode_expect x.1 (total (y :: ys)) hx htail,
        meaning, Program.expect_pure, ih']
      have hc : (total (y :: ys) : ℝ) *
          (payoff f (y :: ys) / (total (y :: ys) : ℝ)) =
          payoff f (y :: ys) := by
        field_simp
      rw [hc]
      simp only [payoff, total, Nat.cast_add]

#print axioms compile_expect

end Paper2.IndexedRationalListCode
