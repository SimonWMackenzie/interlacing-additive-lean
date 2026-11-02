import CurrentAdditive.V38LocalDiagram
import CurrentAdditive.GeneratedWitnessProjection
import CurrentAdditive.DeterministicIndexedCoordinates

/-!
Selected v39/v38 det:construction and det:raw-entries. The finite sources
are the existing exact indexed lists, but the legal column alphabet has
exactly the selected ordinary and diagonal families, weighted 255/256 and
1/256. The old fixedTail constructor is never a legal input here.
-/

namespace CurrentAdditive.V38IndexedTwoTag

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceProjectionDiagonal
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

abbrev Column := (src.outer.Label × src.gamma.Label) ⊕ (Fin q₂ × src.gamma.Label)

def oldTag : Column src → Sources.Column src
  | .inl z => .ordinary z
  | .inr z => .diagonal z

def matrix (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) : Column src → Row (I := I) src → Bool :=
  fun c a => Sources.N src R activity ξ₀ (oldTag src c) a

/-- Distinct source indices, including duplicate decoded values, remain
distinct legal labels in their original family. -/
noncomputable def law : PositiveRationalLaw (Column src) where
  weight
    | .inl z => (255 / 256) * (src.outer.law.prod src.gamma.law).weight z
    | .inr z => (1 / 256) *
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).weight z
  positive z := by
    cases z with
    | inl z => exact mul_pos (by norm_num) ((src.outer.law.prod src.gamma.law).positive z)
    | inr z =>
      exact mul_pos (by norm_num)
        (((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).positive z)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum, PositiveRationalLaw.total, mul_one]
    norm_num

theorem prob_split (P : Column src → Prop) :
    (law src).toFiniteLaw.prob P =
      (255 / 256 : ℝ) * (src.outer.law.prod src.gamma.law).toFiniteLaw.prob
        (fun z => P (.inl z)) +
      (1 / 256 : ℝ) *
        ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw.prob
          (fun z => P (.inr z)) := by
  classical
  unfold FiniteLaw.prob
  rw [Fintype.sum_sum_type]
  simp only [PositiveRationalLaw.toFiniteLaw, law, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Finset.mul_sum, mul_ite, mul_zero]

theorem diagonal_template_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (z : src.inner.Label) (α : Fin q₂) (γ : src.gamma.Label) :
    matrix src R activity ξ₀ (.inr (α, γ)) (.inl (p, z)) =
      R (src.inner.decode z α).2
        (head (src.gamma.decode γ) (src.inner.decode z α).1) := rfl

/-- Literal diagonal/template diagram used by local suppliers (i),(ii).
No source law or profile premise enters this entry identity. -/
theorem diagonal_template_diagram (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (z : src.inner.Label) (γ : src.gamma.Label) (α : Fin q₂) :
    matrix src R activity ξ₀ (.inr (α, γ)) (.inl (p, z)) =
      Sources.A src R γ (src.inner.decode z α) := rfl

/-- The actual indexed head-plus-three-tail source, with original gamma
labels, lies inside the selected two-tag matrix. No product law for the
whole gamma word is required or inferred. -/
theorem witness_source_cost_le
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (bin : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (B : Fin 3 → Set X) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none) (S : Set src.gamma.Label)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t → Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (hS : ∀ γ ∈ S, Sum.inr (α, γ) ∈ U) :
    Compression.restrictionD
      (fun (a : Fin (q₁+3) × X) γ => R a.2 (selectedGamma src p p' γ a.1))
      (indexedWitnessRows src α K B) S ≤
    Compression.restrictionD (matrix src R activity ξ₀) U V := by
  classical
  let realized := fun a : indexedWitnessRows src α K B =>
    indexedWitnessRow_realized src R activity ξ₀ bin α K B
      i₁ i₂ i₀ p p' h₁ h₂ h₀ V hK hB a
  let row : indexedWitnessRows src α K B → V := fun a =>
    ⟨Classical.choose (realized a), (Classical.choose_spec (realized a)).1⟩
  let col : S → U := fun γ => ⟨.inr (α, γ.val), hS γ.val γ.property⟩
  have heq : (fun (a : indexedWitnessRows src α K B) (γ : S) =>
      R a.val.2 (selectedGamma src p p' γ.val a.val.1)) =
      fun a γ => matrix src R activity ξ₀ (col γ).val (row a).val := by
    funext a γ
    exact ((Classical.choose_spec (realized a)).2 γ.val).symm
  change Workspace.Types.CommComplexity.D
    (fun (a : indexedWitnessRows src α K B) (γ : S) =>
    R a.val.2 (selectedGamma src p p' γ.val a.val.1)) ≤ _
  rw [heq]
  have hm := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : V) (c : U) => matrix src R activity ξ₀ c.val a.val) row col
  exact hm.trans_eq (restrictionD_transpose (matrix src R activity ξ₀) U V)

end CurrentAdditive.V38IndexedTwoTag

#print axioms CurrentAdditive.V38IndexedTwoTag.law
#print axioms CurrentAdditive.V38IndexedTwoTag.prob_split
#print axioms CurrentAdditive.V38IndexedTwoTag.diagonal_template_entry
#print axioms CurrentAdditive.V38IndexedTwoTag.diagonal_template_diagram
#print axioms CurrentAdditive.V38IndexedTwoTag.witness_source_cost_le
