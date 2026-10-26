import CurrentAdditive.GeneratedSelectedDWise
import Paper2.SourceProjectionWitness

/-!
The collision witness uses one representative of each retained indexed inner
coordinate, fixed before the gamma label varies. The selected head and three
tail positions are actual positions in the decoded complete gamma source.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceProjectionDiagonal
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def indexedWitnessRows (α : Fin q₂) (K : Set src.inner.Label)
    (B : Fin 3 → Set X) : Set (Fin (q₁ + 3) × X) :=
  fun a => match finSumFinEquiv.symm a.1 with
    | .inl r => (r, a.2) ∈ (fun z => src.inner.decode z α) '' K
    | .inr t => a.2 ∈ B t

def selectedGamma (p p' : Fin s) (γ : src.gamma.Label) :
    Fin (q₁ + 3) → Y :=
  fun i => src.gamma.decode γ (selectedCoordinateFin p p' i)

theorem indexedWitnessRow_realized
    (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (bin : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (B : Fin 3 → Set X) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t →
      Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (a : indexedWitnessRows src α K B) :
    ∃ row : Row (I := I) src, row ∈ V ∧
      ∀ γ : src.gamma.Label,
        N src R activity ξ₀ (.diagonal (α, γ)) row =
          R a.val.2 (selectedGamma src p p' γ a.val.1) := by
  rcases a with ⟨⟨i,u⟩, ha⟩
  change (match finSumFinEquiv.symm i with
    | .inl r => (r, u) ∈ (fun z => src.inner.decode z α) '' K
    | .inr t => u ∈ B t) at ha
  cases h : finSumFinEquiv.symm i with
  | inl r =>
    simp only [h] at ha
    obtain ⟨z, hz, hzu⟩ := ha
    refine ⟨.inl (bin, z), hK z hz, ?_⟩
    intro γ
    have he := diagonal_template_selected_entry R activity ξ₀
      α bin p p' (src.inner.decode z) r u hzu (src.gamma.decode γ)
    change SourceMatrix.N R activity ξ₀
      (.diagonal (α, src.gamma.decode γ)) (.inl (bin, src.inner.decode z)) =
      R u (src.gamma.decode γ (selectedCoordinate p p' (finSumFinEquiv.symm i)))
    rw [h]
    exact he
  | inr t =>
    simp only [h] at ha
    refine ⟨.inr (collisionItem i₁ i₂ i₀ t, u), hB t u ha, ?_⟩
    intro γ
    have he := diagonal_source_selected_entry R activity ξ₀
      α i₁ i₂ i₀ p p' h₁ h₂ h₀ t u (src.gamma.decode γ)
    change SourceMatrix.N R activity ξ₀
      (.diagonal (α, src.gamma.decode γ))
      (.inr (collisionItem i₁ i₂ i₀ t, u)) =
      R u (src.gamma.decode γ (selectedCoordinate p p' (finSumFinEquiv.symm i)))
    rw [h]
    exact he

/-- The full selected collision interlace is realized by surviving rows and
diagonal gamma labels of the literal generated matrix. Representatives of
inner-label projections and gamma projections are fixed for all entries. -/
theorem indexed_witness_interlace_cost_le
    (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (bin : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (B : Fin 3 → Set X) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (W : Set src.gamma.Label)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t →
      Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (hW : ∀ γ ∈ W, Column.diagonal (α, γ) ∈ U) :
    Paper2.Compression.restrictionD (Paper2.fullInterlace R (q₁ + 3))
      (indexedWitnessRows src α K B)
      (selectedGamma src p p' '' W) ≤
    Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  classical
  let rows := indexedWitnessRows src α K B
  let select := selectedGamma src p p'
  let realized : ∀ a : rows, ∃ row : Row (I := I) src, row ∈ V ∧
      ∀ γ : src.gamma.Label,
        N src R activity ξ₀ (.diagonal (α, γ)) row =
          R a.val.2 (select γ a.val.1) :=
    fun a => indexedWitnessRow_realized src R activity ξ₀ bin α K B
      i₁ i₂ i₀ p p' h₁ h₂ h₀ V hK hB a
  let row : rows → V := fun a =>
    ⟨Classical.choose (realized a), (Classical.choose_spec (realized a)).1⟩
  let col : (select '' W) → U := fun w =>
    ⟨.diagonal (α, (representative select W w).val),
      hW _ (representative_survives select W w)⟩
  have heq : (fun (a : rows) (w : select '' W) =>
      Paper2.fullInterlace R (q₁ + 3) a.val w.val) =
      fun a w => N src R activity ξ₀ (col w).val (row a).val := by
    funext a w
    have h := (Classical.choose_spec (realized a)).2
      (representative select W w).val
    change R a.val.2 (w.val a.val.1) =
      N src R activity ξ₀
        (.diagonal (α, (representative select W w).val))
        (Classical.choose (realized a))
    rw [h]
    exact congrArg (R a.val.2)
      (congrFun (representative_maps select W w) a.val.1).symm
  change Workspace.Types.CommComplexity.D
    (fun (a : rows) (w : select '' W) =>
      Paper2.fullInterlace R (q₁ + 3) a.val w.val) ≤ _
  rw [heq]
  have h := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (k : V) (Z : U) => N src R activity ξ₀ Z.val k.val) row col
  exact h.trans_eq (restrictionD_transpose (N src R activity ξ₀) U V)
end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexedWitnessRow_realized
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_witness_interlace_cost_le
