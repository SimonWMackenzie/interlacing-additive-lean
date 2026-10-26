import CurrentAdditive.GeneratedWitnessProjection
import CurrentAdditive.ExactBoost

/-!
The current schedule has many more selected head coordinates than source-wise
independence.  Apply the arbitrary-prefix theorem directly to the eight-wise
gamma source on its own labels.  This needs eight-wise independence of every
small selected subset, not independence of the whole selected word.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem selected_gamma_dwise (hD : 8 ≤ D)
    (p p' : Fin s) (hpp : p ≠ p') :
    IsDWise 8 src.gamma.law.toFiniteLaw
      (selectedGamma src p p') μY.toFiniteLaw := by
  classical
  intro J hJ E
  let e : Fin (q₁+3) → Fin (q₁+s+1) := selectedCoordinateFin p p'
  let T : Finset (Fin (q₁+s+1)) := J.image e
  have hT : T.card ≤ D :=
    (Finset.card_image_le).trans (hJ.trans hD)
  have hemem (j : J) : e j.val ∈ T :=
    Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩
  let f : J → T := fun j => ⟨e j.val, hemem j⟩
  have hf : Function.Injective f := by
    intro j k h
    exact Subtype.ext ((selectedCoordinateFin_injective p p' hpp)
      (congrArg Subtype.val h))
  let E' : (T → Y) → Prop := fun z => E (fun j => z (f j))
  calc
    src.gamma.law.toFiniteLaw.prob
        (fun γ => E (fun j : J => src.gamma.decode γ (e j.val))) =
        (FiniteLaw.pi (fun _ : T => μY.toFiniteLaw)).prob E' := by
          simpa only [E', f, selectedGamma, e] using
            src.gamma.exactLaw T hT E'
    _ = (FiniteLaw.pi (fun _ : J => μY.toFiniteLaw)).prob E := by
          simpa only [E', FiniteLaw.iid] using
            (FiniteLaw.pi_prob_restrict
              (fun _ : T => μY.toFiniteLaw) f hf E)

/-- The selected exact-source rectangle is a literal submatrix of the
indexed generated matrix, with complete gamma labels as columns. -/
theorem indexed_witness_source_cost_le
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
    Paper2.Compression.restrictionD
      (fun (a : Fin (q₁+3) × X) γ =>
        R a.2 (selectedGamma src p p' γ a.1))
      (indexedWitnessRows src α K B) W ≤
    Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  classical
  let rows := indexedWitnessRows src α K B
  let realized : ∀ a : rows, ∃ row : Row (I := I) src, row ∈ V ∧
      ∀ γ : src.gamma.Label,
        N src R activity ξ₀ (.diagonal (α, γ)) row =
          R a.val.2 (selectedGamma src p p' γ a.val.1) :=
    fun a => indexedWitnessRow_realized src R activity ξ₀ bin α K B
      i₁ i₂ i₀ p p' h₁ h₂ h₀ V hK hB a
  let row : rows → V := fun a =>
    ⟨Classical.choose (realized a), (Classical.choose_spec (realized a)).1⟩
  let col : W → U := fun γ => ⟨.diagonal (α, γ.val), hW γ.val γ.property⟩
  have heq : (fun (a : rows) (γ : W) =>
      R a.val.2 (selectedGamma src p p' γ.val a.val.1)) =
      fun a γ => N src R activity ξ₀ (col γ).val (row a).val := by
    funext a γ
    exact ((Classical.choose_spec (realized a)).2 γ.val).symm
  change Workspace.Types.CommComplexity.D (fun (a : rows) (γ : W) =>
      R a.val.2 (selectedGamma src p p' γ.val a.val.1)) ≤ _
  rw [heq]
  have h := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (k : V) (Z : U) => N src R activity ξ₀ Z.val k.val) row col
  exact h.trans_eq (Paper2.SourceProjection.restrictionD_transpose
    (N src R activity ξ₀) U V)

/-- Appendix I collision surplus from the *actual eight-wise* gamma source.
The current width may exceed D; only eight selected coordinates are ever
requested at a time by `exactboost`. -/
theorem indexed_collision_cost_exact
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a : ℕ) (ρ : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      ρ (d : ℤ))
    (bin : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (B : Fin 3 → Set X) (W : Set src.gamma.Label)
    (i₁ i₂ i₀ : I) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hB : ∀ t u, u ∈ B t →
      Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)
    (hW : ∀ γ ∈ W, Column.diagonal (α, γ) ∈ U)
    (hhead : ∀ r, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z => src.inner.decode z α) '' K))
    (hsource : ∀ t, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob (· ∈ B t))
    (hWmass : (1/2 : ℝ) < src.gamma.law.toFiniteLaw.prob (· ∈ W)) :
    d + a + 1 ≤
      Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  classical
  let Rows : Fin (q₁+3) → Set X := fun i u =>
    match finSumFinEquiv.symm i with
    | .inl r => (r,u) ∈ (fun z => src.inner.decode z α) '' K
    | .inr t => u ∈ B t
  have hwise8 := selected_gamma_dwise src hD p p' hpp
  have hcount : 2^((a+1)-1)+1 ≤
      (Finset.univ : Finset (Fin (q₁+3))).card := by
    simpa only [Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel_right] using (by omega : 2^a+1 ≤ q₁+3)
  have hp : (2 : ℝ)^(a+1) = 2 * (s : ℝ) := by
    rw [hs, pow_succ]
    push_cast
    ring
  have hrow : ∀ i ∈ (Finset.univ : Finset (Fin (q₁+3))),
      (2 : ℝ)^(a+1)*ρ ≤ μX.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _
    have hmass : 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob (· ∈ Rows i) := by
      change 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
        (fun u => match finSumFinEquiv.symm i with
          | .inl r => (r,u) ∈ (fun z => src.inner.decode z α) '' K
          | .inr t => u ∈ B t)
      rcases h : finSumFinEquiv.symm i with r | t
      · simpa only [h] using hhead r
      · simpa only [h] using hsource t
    simpa only [hp] using hmass
  have hKmass : (9/25 : ℝ) ≤ src.gamma.law.toFiniteLaw.prob (· ∈ W) := by
    linarith
  have hscale' : (2 : ℝ)^(a+1)*ρ ≤ 1 := by
    rw [hp]
    exact hscale
  have hl := CurrentAdditive.ArbitraryPrefix.exactboost μX μY R
    src.gamma.law.toFiniteLaw (selectedGamma src p p') hwise8
    Finset.univ Rows W d (a+1) ρ (by omega) hd hρ hscale'
    hprofile hcount hrow hKmass
  have heq : Paper2.Compression.restrictionD
      (fun (a : Fin (q₁+3) × X) γ =>
        R a.2 (selectedGamma src p p' γ a.1))
      (CurrentAdditive.ArbitraryPrefix.rowRectangle Finset.univ Rows) W =
      Paper2.Compression.restrictionD
        (fun (a : Fin (q₁+3) × X) γ =>
          R a.2 (selectedGamma src p p' γ a.1))
        (indexedWitnessRows src α K B) W := by
    congr 1
    ext a
    change (a.1 ∈ (Finset.univ : Finset (Fin (q₁+3))) ∧
      a.2 ∈ Rows a.1) ↔
      (match finSumFinEquiv.symm a.1 with
        | .inl r => (r,a.2) ∈ (fun z => src.inner.decode z α) '' K
        | .inr t => a.2 ∈ B t)
    simp only [Finset.mem_univ, true_and]
    rfl
  have hp := indexed_witness_source_cost_le src R activity ξ₀ bin α K B
    i₁ i₂ i₀ p p' h₁ h₂ h₀ W U V hK hB hW
  have hl' : d+a+1 ≤ Paper2.Compression.restrictionD
      (fun (a : Fin (q₁+3) × X) γ =>
        R a.2 (selectedGamma src p p' γ a.1))
      (indexedWitnessRows src α K B) W := by
    simpa only [heq, Nat.add_assoc] using hl
  exact hl'.trans hp

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_witness_source_cost_le
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_collision_cost_exact
