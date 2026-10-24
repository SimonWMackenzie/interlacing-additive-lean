import Paper2.RecursiveEntries
import Paper2.SourceProtocols
import Paper2.SourceRank

/-!
# Upper and rank bounds for the actual recursively constructed matrices

Frozen v12, `sections/03-amplification.tex`, `prop:iteration` and
`eq:iteration`. These are the universal upper, YES upper and rank parts.
The NO equality and regenerated profile require the pending amplifier
lower-bound proof and are deliberately not assumed here.

Every step is `SourceMatrix.successor` on the preceding literal carrier.
The hypotheses are public width equalities and the combinatorial collision
condition proved for a proper source coloring in `SourceConstruction`.
No lower-bound certificate or arbitrary sequence of matrices is substituted.
-/

namespace Paper2.RecursiveEntries

open Workspace.Types.CommComplexity RankLeaves SourceMatrix

variable {X₀ Y₀ I : Type} [Fintype X₀] [Fintype Y₀] [Fintype I]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₂]

theorem iteration_upper (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d) (k : ℕ) :
    D (matrix F activity ξ k) ≤ D F + k * (a + a + b + c + d + 1) := by
  induction k with
  | zero => simpa only [matrix, Nat.zero_mul, Nat.add_zero] using (le_refl (D F))
  | succ k ih =>
      have h := (successor_upper_budgets activity (matrix F activity ξ k) (ξ k)
        w Q a b c d hq₁ hs hq₂ hw hQ).1
      change D (successor (matrix F activity ξ k) activity (ξ k) w Q) ≤ _
      apply h.trans
      rw [Nat.succ_mul]
      omega

theorem iteration_yes_upper (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d)
    (assign : I → Fin s) (hc : CollisionFree assign activity) (k : ℕ) :
    D (matrix F activity ξ k) ≤ D F + k * (a + a + b + c + d) := by
  induction k with
  | zero => simpa only [matrix, Nat.zero_mul, Nat.add_zero] using (le_refl (D F))
  | succ k ih =>
      have h := (successor_upper_budgets activity (matrix F activity ξ k) (ξ k)
        w Q a b c d hq₁ hs hq₂ hw hQ).2 assign hc
      change D (successor (matrix F activity ξ k) activity (ξ k) w Q) ≤ _
      apply h.trans
      rw [Nat.succ_mul]
      omega

theorem iteration_rank (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (a b c d : ℕ)
    (hI : Fintype.card I ≤ 2 * s * q₂)
    (hq₁ : q₁ + 2 = s) (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d) (k : ℕ) :
    (realMatrix (matrix F activity ξ k)).rank ≤
      2 ^ (k * (a + a + b + c + d)) * (realMatrix F).rank := by
  induction k with
  | zero =>
      simpa only [matrix, Nat.zero_mul, pow_zero, one_mul] using
        (le_refl (realMatrix F).rank)
  | succ k ih =>
      have h := successor_rank_le_pow (matrix F activity ξ k) activity (ξ k)
        w Q a b c d hI hq₁ hs hq₂ hw hQ
      change (realMatrix (successor (matrix F activity ξ k) activity (ξ k) w Q)).rank ≤ _
      apply h.trans
      calc
        _ ≤ 2 ^ (a + a + b + c + d) *
            (2 ^ (k * (a + a + b + c + d)) * (realMatrix F).rank) :=
          Nat.mul_le_mul_left _ ih
        _ = _ := by rw [Nat.succ_mul, pow_add]; ring

/-- Every concrete sampled output computed by the recursive evaluator
inherits the YES budget, whether its input labels repeat or not. -/
theorem table_yes_upper (F : X₀ → Y₀ → Bool)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails X₀ Y₀ I s q₁ q₂ w Q) (a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d)
    (assign : I → Fin s) (hc : CollisionFree assign activity) (k : ℕ) {m n : ℕ}
    (xs : Fin m → Row X₀ Y₀ I s q₁ q₂ w Q k)
    (ys : Fin n → Column X₀ Y₀ I s q₁ q₂ w Q k) :
    D (table F activity ξ k xs ys) ≤ D F + k * (a + a + b + c + d) := by
  rw [table_eq_sampleMatrix]
  exact (sample_D_le _ xs ys).trans
    (iteration_yes_upper F activity ξ a b c d hq₁ hs hq₂ hw hQ assign hc k)

end Paper2.RecursiveEntries
