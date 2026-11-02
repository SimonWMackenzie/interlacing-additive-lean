import CurrentAdditive.FiniteFieldBias
import CurrentAdditive.SmallBiasPatterns
import Paper2.ClassicalSeparation

/-!
Adapter from the v27 finite-field powering list to the frozen
`CurrentAdditive.SmallBias.IsSmallBiased` pattern interface.

The labels are all pairs `(φ,y)` where `φ` is an F₂-linear functional on the
field and `y` is a field element.  The Bool at coordinate `j` is the actual
binary value `φ (y^j)`, decoded with `0 ↦ false` and `1 ↦ true`.  A chosen
binary basis identifies `φ` with a unique binary vector and makes this Bool
equal to the manuscript's dot-product bit.  This file has no runtime claim.
-/

namespace CurrentAdditive.FiniteFieldAdapter

local instance : DecidableEq (ZMod 2) := ZMod.decidableEq 2
set_option maxHeartbeats 500000

open CurrentAdditive

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev Seed (F : Type*) [Field F] [Algebra (ZMod 2) F] :=
  Module.Dual (ZMod 2) F × F

noncomputable def seedLaw : Paper2.FiniteLaw (Seed F) :=
  Paper2.FiniteLaw.uniform (Seed F)

def decodeBit (b : ZMod 2) : Bool := decide (b = 1)

def word {n : ℕ} (seed : Seed F) (j : Fin n) : Bool :=
  decodeBit (seed.1 (seed.2 ^ (j : ℕ)))

theorem decodeBit_eq_dot {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (ZMod 2) F) (x : ι → ZMod 2)
    (y : F) {n : ℕ} (j : Fin n) :
    word (b.dualBasis.equivFun.symm x, y) j =
      decide ((∑ i, x i * b.equivFun (y ^ (j : ℕ)) i) = 1) := by
  simp [word, decodeBit, basisFunctional_eq_dot]

private theorem sign_decode (z : ZMod 2) :
    SmallBias.bitSign (decodeBit z) = (CurrentAdditive.bitSign z : ℝ) := by
  have hz : z = 0 ∨ z = 1 := by fin_cases z <;> decide
  rcases hz with rfl | rfl
  · have h01 : (0 : ZMod 2) ≠ 1 := by decide
    simp [decodeBit, SmallBias.bitSign, CurrentAdditive.bitSign, h01]
  · have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp [decodeBit, SmallBias.bitSign, CurrentAdditive.bitSign, h10]

private theorem sign_add (a b : ZMod 2) :
    (CurrentAdditive.bitSign (a + b) : ℝ) =
      (CurrentAdditive.bitSign a : ℝ) * (CurrentAdditive.bitSign b : ℝ) := by
  have ha : a = 0 ∨ a = 1 := by fin_cases a <;> decide
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> decide
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp [CurrentAdditive.bitSign, h10, h11]

private theorem parityChar_word (seed : Seed F) {n : ℕ} (I : Finset (Fin n)) :
    SmallBias.parityChar I (word seed) =
      (CurrentAdditive.bitSign (parityBit I seed.1 seed.2) : ℝ) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [SmallBias.parityChar, parityBit, CurrentAdditive.bitSign]
  | @insert j I hj ih =>
      simp only [SmallBias.parityChar, Finset.prod_insert hj, parityBit,
        Finset.sum_insert hj] at *
      change SmallBias.bitSign (decodeBit (seed.1 (seed.2 ^ (j : ℕ)))) *
          (∏ j ∈ I, SmallBias.bitSign (word seed j)) = _
      rw [sign_decode, ih, sign_add]

theorem parityCorr_eq_average {n : ℕ} (I : Finset (Fin n)) :
    SmallBias.parityCorr (seedLaw (F := F)) (word (F := F)) I =
      (paritySignedAverage (F := F) I : ℝ) := by
  classical
  unfold SmallBias.parityCorr seedLaw Paper2.FiniteLaw.uniform
  simp_rw [parityChar_word]
  rw [← Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Prod.fst, Prod.snd, ← Int.cast_sum]
  simp [paritySignedAverage, Seed, Fintype.card_prod, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

/-- The actual labelled Bool word list supplies the exact small-bias premise
used by the frozen v27 pattern argument. -/
theorem seedLaw_isSmallBiased {n : ℕ} (hn : 1 ≤ n)
    (ε : ℚ) (hε : 0 < ε)
    (hR : (n : ℚ) / ε ≤ (Fintype.card F : ℚ)) :
    SmallBias.IsSmallBiased (seedLaw (F := F)) (word (F := F) (n := n))
      (ε : ℝ) := by
  intro I hI
  rw [parityCorr_eq_average]
  exact_mod_cast finiteFieldPowering_epsilonBias (F := F) hn ε hε hR I hI


#print axioms decodeBit_eq_dot
#print axioms parityCorr_eq_average
#print axioms seedLaw_isSmallBiased

end CurrentAdditive.FiniteFieldAdapter
