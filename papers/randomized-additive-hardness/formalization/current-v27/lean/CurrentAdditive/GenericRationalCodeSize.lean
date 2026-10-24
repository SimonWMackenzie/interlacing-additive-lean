import CurrentAdditive.GenericRationalPacketGenerator

/-! An explicit size estimate for the first-order indexed rational code.
The code serializes integer masses in unary, so its size is charged to
the mass values and emitted index words, not merely to the carrier count. -/

namespace Paper2.GenericRationalCodeSize

open Paper2.IndexedRationalListCode
open Paper2.GeneratorSerialization
open Paper2.GeneratorCode

set_option maxHeartbeats 2000000

def budget : List (ℕ × List Bool) → ℕ
  | [] => 0
  | x :: xs => x.1 + x.2.length + budget xs

theorem total_le_budget (xs : List (ℕ × List Bool)) :
    total xs ≤ budget xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total, budget]; omega

/-- A direct polynomial syntax bound before any logarithmic estimate on
the rational masses is applied. -/
theorem compile_size_le_budget (xs : List (ℕ × List Bool)) :
    codeSize (compile xs) ≤ 20 * (xs.length + 1) * (budget xs + 1) := by
  induction xs with
  | nil => simp [compile, codeSize, budget]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [compile, codeSize, List.length_cons, List.length_nil,
        budget, Nat.add_zero]
      omega
    | cons y ys =>
      have htail := total_le_budget (y :: ys)
      let B := budget (y :: ys)
      let X := x.1 + x.2.length
      have hstep :
          codeSize (compile (x :: y :: ys)) ≤
            20 * (X + B + 1) + codeSize (compile (y :: ys)) := by
        have htail' : y.1 + total ys ≤ y.1 + y.2.length + budget ys := by
          simpa only [total, budget] using htail
        simp only [compile, Paper2.IndexedRationalBaseCode.branchCode,
          codeSize, total]
        dsimp [X, B, budget]
        omega
      have hfactor : B + 1 ≤ X + B + 1 := by omega
      have hmul := Nat.mul_le_mul_left (20 * (ys.length + 2)) hfactor
      calc
        codeSize (compile (x :: y :: ys))
            ≤ 20 * (X + B + 1) + codeSize (compile (y :: ys)) := hstep
        _ ≤ 20 * (X + B + 1) + 20 * (ys.length + 2) * (B + 1) := by
          apply Nat.add_le_add_left
          simpa only [List.length_cons, List.length_nil, Nat.add_assoc] using ih
        _ ≤ 20 * (X + B + 1) + 20 * (ys.length + 2) * (X + B + 1) :=
          Nat.add_le_add_left hmul _
        _ = 20 * ((x :: y :: ys).length + 1) *
              (budget (x :: y :: ys) + 1) := by
          change 20 * (X + B + 1) + 20 * (ys.length + 2) * (X + B + 1) =
            20 * (ys.length + 3) * (X + B + 1)
          ring

theorem budget_le_length_mul (xs : List (ℕ × List Bool)) (M : ℕ)
    (h : ∀ x ∈ xs, x.1 + x.2.length ≤ M) :
    budget xs ≤ xs.length * M := by
  induction xs with
  | nil => simp [budget]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, y.1 + y.2.length ≤ M := by
        intro y hy
        exact h y (by simp [hy])
      have hxs := ih ht
      simp only [budget, List.length_cons]
      have hm : (xs.length + 1) * M = xs.length * M + M := by ring
      omega

/-- If the expanded integer masses and compact index words are individually
bounded, the whole weighted source code has an explicit polynomial bound.
The separate denominator-clearing step must establish the mass premise from
the original rational input bytes. -/
theorem compile_size_le_fields (xs : List (ℕ × List Bool))
    (N M : ℕ) (hlen : xs.length ≤ N)
    (hfields : ∀ x ∈ xs, x.1 + x.2.length ≤ M) :
    codeSize (compile xs) ≤ 20 * (N + 1) * (N * M + 1) := by
  have hb := budget_le_length_mul xs M hfields
  calc
    codeSize (compile xs) ≤ 20 * (xs.length + 1) * (budget xs + 1) :=
      compile_size_le_budget xs
    _ ≤ 20 * (N + 1) * (N * M + 1) := by
      have hb' : budget xs ≤ N * M :=
        hb.trans (Nat.mul_le_mul_right M hlen)
      gcongr

#print axioms compile_size_le_budget
#print axioms compile_size_le_fields

end Paper2.GenericRationalCodeSize
