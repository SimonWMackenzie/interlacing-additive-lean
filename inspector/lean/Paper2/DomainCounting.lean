import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Counting complete union/intersection formulas

Source: Paper 2, v12, `sections/02-compression.tex`, `thm:rank-count`.
This is the formula-counting step only. The separate rank argument must
supply the leaf-domain bound, and protocol semantics must supply coverage.
-/

namespace Paper2

/-- A complete binary expression with leaves in `A`; the Boolean at each
internal node selects union or intersection. -/
def CompleteFormula (A : Type*) : ℕ → Type _
  | 0 => A
  | t + 1 => Bool × CompleteFormula A t × CompleteFormula A t

instance completeFormulaFintype (A : Type*) [Fintype A] :
    (t : ℕ) → Fintype (CompleteFormula A t)
  | 0 => inferInstanceAs (Fintype A)
  | t + 1 => @instFintypeProd _ _ inferInstance
      (@instFintypeProd _ _ (completeFormulaFintype A t) (completeFormulaFintype A t))

/-- Interpret the syntax as an actual set. A `false` node is union. -/
def CompleteFormula.eval {A Y : Type*} (leaf : A → Set Y) :
    {t : ℕ} → CompleteFormula A t → Set Y
  | 0, a => leaf a
  | _ + 1, (b, p, q) =>
      if b then p.eval leaf ∩ q.eval leaf else p.eval leaf ∪ q.eval leaf

/-- Number of syntactic formulas with a leaf alphabet of size at most `2^a`.
The subtraction is natural subtraction, including the depth-zero case. -/
theorem completeFormula_card_le (A : Type*) [Fintype A] (a t : ℕ)
    (hleaf : Fintype.card A ≤ 2 ^ a) :
    Fintype.card (CompleteFormula A t) ≤ 2 ^ ((a + 1) * 2 ^ t - 1) := by
  induction t with
  | zero => simpa [CompleteFormula] using hleaf
  | succ t ih =>
    have hz : 1 ≤ (a + 1) * 2 ^ t := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have he : (((a + 1) * 2 ^ t - 1) + ((a + 1) * 2 ^ t - 1)) + 1 =
        (a + 1) * 2 ^ (t + 1) - 1 := by
      rw [pow_succ, ← Nat.mul_assoc]
      omega
    change Fintype.card (Bool × CompleteFormula A t × CompleteFormula A t) ≤ _
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool]
    calc
      2 * (Fintype.card (CompleteFormula A t) *
          Fintype.card (CompleteFormula A t)) ≤
          2 * (2 ^ ((a + 1) * 2 ^ t - 1) * 2 ^ ((a + 1) * 2 ^ t - 1)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul ih ih)
      _ = 2 ^ ((a + 1) * 2 ^ (t + 1) - 1) := by
        rw [← pow_add, ← pow_succ', he]

/-- Evaluation can identify syntactically different formulas, never increase
their number. This is a count of sets, not a count of Alice's strategies. -/
theorem formula_domains_card_le {A Y : Type*} [Fintype A] (leaf : A → Set Y)
    (a t : ℕ) (hleaf : Fintype.card A ≤ 2 ^ a) :
    (Set.range (CompleteFormula.eval leaf (t := t))).ncard ≤
      2 ^ ((a + 1) * 2 ^ t - 1) := by
  have hcount : (Set.range (CompleteFormula.eval leaf (t := t))).ncard ≤
      Fintype.card (CompleteFormula A t) := by
    simpa [Set.image_univ, Nat.card_eq_fintype_card] using
      (Set.ncard_image_le (s := Set.univ) (f := CompleteFormula.eval leaf (t := t)))
  exact hcount.trans (completeFormula_card_le A a t hleaf)

/-- The numerical exponent occurring in the manuscript, conditional only on
the separately stated leaf alphabet bound. This does not itself prove that
all protocol-compatible domains belong to the formula family. -/
theorem manuscript_formula_bound {A Y : Type*} [Fintype A]
    (leaf : A → Set Y) (r t : ℕ)
    (hleaf : Fintype.card A ≤ 2 ^ (r * (r + 1) + 1)) :
    (Set.range (CompleteFormula.eval leaf (t := t))).ncard ≤
      2 ^ ((r * (r + 1) + 2) * 2 ^ t - 1) := by
  simpa [Nat.add_assoc] using formula_domains_card_le leaf (r * (r + 1) + 1) t hleaf

end Paper2
