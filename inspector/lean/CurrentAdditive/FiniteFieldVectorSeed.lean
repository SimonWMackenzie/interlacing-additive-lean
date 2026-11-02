import CurrentAdditive.FiniteFieldSmallBiasBase
/-!
The literal binary-vector labels for the finite-field powering list. A basis
identifies each vector with one binary linear functional, so the uniform
vector-labelled law is the same law as the checked dual-labelled adapter.
This is an algebraic bridge; it asserts no search or printing runtime.
-/

namespace CurrentAdditive.FiniteFieldAdapter

local instance : DecidableEq (ZMod 2) := ZMod.decidableEq 2
open CurrentAdditive
set_option maxHeartbeats 500000

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The manuscript's literal seed label: a binary vector and a field element. -/
abbrev VectorSeed (d : ℕ) (F : Type*) := (Fin d → ZMod 2) × F

noncomputable def vectorWord {d n : ℕ} (b : Module.Basis (Fin d) (ZMod 2) F)
    (seed : VectorSeed d F) (j : Fin n) : Bool :=
  word (b.dualBasis.equivFun.symm seed.1, seed.2) j

noncomputable def vectorSeedLaw (d : ℕ) : Paper2.FiniteLaw (VectorSeed d F) :=
  Paper2.FiniteLaw.uniform (VectorSeed d F)

noncomputable def vectorToDualSeed {d : ℕ} (b : Module.Basis (Fin d) (ZMod 2) F) :
    VectorSeed d F ≃ Seed F :=
  b.dualBasis.equivFun.symm.toEquiv.prodCongr (Equiv.refl F)

/-- Every binary vector occurs once for each field element. -/
theorem vectorSeed_card_eq_square {d : ℕ}
    (b : Module.Basis (Fin d) (ZMod 2) F) :
    Fintype.card (VectorSeed d F) = (Fintype.card F) ^ 2 := by
  rw [Fintype.card_congr (vectorToDualSeed b)]
  exact seed_card_eq_square (F := F)

omit [Fintype F] [CharP F 2] in
theorem vectorWord_eq_word {d n : ℕ} (b : Module.Basis (Fin d) (ZMod 2) F)
    (seed : VectorSeed d F) (j : Fin n) :
    vectorWord b seed j = word (vectorToDualSeed b seed) j := by
  rfl

omit [CharP F 2] in
theorem vectorCorr_eq_dualCorr {d n : ℕ} (b : Module.Basis (Fin d) (ZMod 2) F)
    (I : Finset (Fin n)) :
    SmallBias.parityCorr (vectorSeedLaw (F := F) d) (vectorWord b) I =
      SmallBias.parityCorr (seedLaw (F := F)) (word (F := F)) I := by
  classical
  unfold SmallBias.parityCorr vectorSeedLaw seedLaw
  change (∑ ℓ : VectorSeed d F,
      ((Fintype.card (VectorSeed d F) : ℝ)⁻¹) *
        SmallBias.parityChar I (vectorWord b ℓ)) =
    ∑ ℓ : Seed F,
      ((Fintype.card (Seed F) : ℝ)⁻¹) *
        SmallBias.parityChar I (word ℓ)
  have hcard : Fintype.card (VectorSeed d F) = Fintype.card (Seed F) :=
    Fintype.card_congr (vectorToDualSeed b)
  rw [hcard]
  apply Fintype.sum_equiv (vectorToDualSeed b)
  intro seed
  have hword : vectorWord (n := n) b seed =
      word (n := n) ((vectorToDualSeed b) seed) := by
    funext j
    exact vectorWord_eq_word b seed j
  simp [hword]

theorem vectorSeedLaw_isSmallBiased {d n : ℕ}
    (b : Module.Basis (Fin d) (ZMod 2) F) (hn : 1 ≤ n)
    (ε : ℚ) (hε : 0 < ε)
    (hR : (n : ℚ) / ε ≤ (Fintype.card F : ℚ)) :
    SmallBias.IsSmallBiased (vectorSeedLaw (F := F) d) (vectorWord b (n := n))
      (ε : ℝ) := by
  intro I hI
  rw [vectorCorr_eq_dualCorr]
  exact seedLaw_isSmallBiased (F := F) hn ε hε hR I hI

#print axioms vectorWord_eq_word
#print axioms vectorSeed_card_eq_square
#print axioms vectorCorr_eq_dualCorr
#print axioms vectorSeedLaw_isSmallBiased

end CurrentAdditive.FiniteFieldAdapter
