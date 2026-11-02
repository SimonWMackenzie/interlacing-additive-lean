import CurrentAdditive.V39SelectorLaws
import CurrentAdditive.V38RestrictionProfiles

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

namespace CurrentAdditive.V39SelectorTransport
noncomputable section
open Paper2 SourceMatrix SourceCoordinateConjugacy V39RecursiveGenerator
open Workspace.Types.CommComplexity Paper2.RankLeaves

variable {n p q₁ q₂ s w Q : ℕ} [NeZero s]

theorem matrix_fun_map (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k : ℕ) :
    (fun x y => V39RecursiveTable.matrix (activityNew π A) k
      (eR n p q₁ q₂ s w Q π k x) (eC n p q₁ q₂ s w Q π k y)) =
      V39RecursiveTable.matrix A k := by
  funext x y
  exact matrix_map π A k x y

theorem D_map (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k : ℕ) :
    D (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q) (activityNew π A) k) =
      D (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q) A k) := by
  have h := pullback_D_eq_of_surjective (V39RecursiveTable.matrix (activityNew π A) k)
    (eR n p q₁ q₂ s w Q π k) (eC n p q₁ q₂ s w Q π k)
    (eR n p q₁ q₂ s w Q π k).surjective (eC n p q₁ q₂ s w Q π k).surjective
  rw [matrix_fun_map] at h
  exact h.symm

theorem rank_map (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k : ℕ) :
    (realMatrix (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q) (activityNew π A) k)).rank =
      (realMatrix (V39RecursiveTable.matrix (p₀:=p) (q₁:=q₁) (w:=w) (Q:=Q) A k)).rank := by
  have h := Matrix.rank_submatrix (realMatrix (V39RecursiveTable.matrix (activityNew π A) k))
    (eR n p q₁ q₂ s w Q π k) (eC n p q₁ q₂ s w Q π k)
  rw [← realMatrix_pullback,matrix_fun_map] at h
  exact h.symm

variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

/-- Exact equivalence of the current two-threshold profiles, for every
threshold and integer lower bound; no hardness assertion is assumed. -/
theorem profile_map_iff (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k : ℕ)
    (ρ : ℝ) (d : ℤ) :
    V38RestrictionProfiles.TwoThresholdProfile (V39RecursiveTable.matrix (activityNew π A) k)
      (laws n p q₁ q₂ s w Q k).1.toFiniteLaw (laws n p q₁ q₂ s w Q k).2.toFiniteLaw ρ d ↔
    V38RestrictionProfiles.TwoThresholdProfile (V39RecursiveTable.matrix A k)
      (laws n p q₁ q₂ s w Q k).1.toFiniteLaw (laws n p q₁ q₂ s w Q k).2.toFiniteLaw ρ d := by
  obtain ⟨hr,hc⟩ := laws_pushes n p q₁ q₂ s w Q π k
  have hh (a b : ℝ) (c : ℤ) := RestrictionLowerBound.pullback_iff
    (V39RecursiveTable.matrix (activityNew π A) k)
    (laws n p q₁ q₂ s w Q k).1.toFiniteLaw (laws n p q₁ q₂ s w Q k).2.toFiniteLaw
    (laws n p q₁ q₂ s w Q k).1.toFiniteLaw (laws n p q₁ q₂ s w Q k).2.toFiniteLaw
    (eR n p q₁ q₂ s w Q π k) (eC n p q₁ q₂ s w Q π k) hr hc
    (eR n p q₁ q₂ s w Q π k).surjective (eC n p q₁ q₂ s w Q π k).surjective a b c
  simp_rw [matrix_fun_map] at hh
  constructor
  · intro h j; exact (hh _ _ _).mpr (h j)
  · intro h j; exact (hh _ _ _).mp (h j)

/-- Corresponding labelled samples give the same serialized finite table. -/
theorem sampledTable_map (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k m : ℕ) (z) :
    V39RecursiveTable.sampledTable (activityNew π A) k m (sampleEquiv n p q₁ q₂ s w Q π k m z) =
      V39RecursiveTable.sampledTable A k m z := by
  unfold V39RecursiveTable.sampledTable
  congr 1
  funext i j
  simp only [V39RecursiveTable.evaluate_eq_matrix]
  exact matrix_map π A k (z.1 i) (z.2 j)

end
end CurrentAdditive.V39SelectorTransport

#print axioms CurrentAdditive.V39SelectorTransport.D_map
#print axioms CurrentAdditive.V39SelectorTransport.rank_map
#print axioms CurrentAdditive.V39SelectorTransport.profile_map_iff
#print axioms CurrentAdditive.V39SelectorTransport.sampledTable_map
