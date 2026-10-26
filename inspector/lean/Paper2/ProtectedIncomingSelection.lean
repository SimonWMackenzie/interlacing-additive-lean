import Paper2.ProtectedIncomingTemplateLaw
import Paper2.ProtectedIncomingColumns

/-!
# Selected original coordinates and whole-tuple template images

The density-group front end supplies `V` and `u * B2 < |V|`; these
lemmas select a single good original `u`-set and pass it through the checked
template-law bridge. No singleton-marginal surrogate is used.
-/

namespace Paper2.ProtectedIncomingSelection

open ProtectedIncomingColumns ProtectedIncomingTemplateLaw
open SourceMatrix SourceLawBinding

variable {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
variable {q₁ q₂ s w k : ℕ} [NeZero q₁]

private noncomputable def enumerateSetEquiv (S : Finset (Fin w))
    (hS : S.card = 2 * k) : Fin (2 * k) ≃ S :=
  (Fintype.equivFinOfCardEq (by simpa using hS)).symm

private noncomputable def enumerateSet (S : Finset (Fin w))
    (hS : S.card = 2 * k) : Fin (2 * k) → Fin w :=
  fun t => (enumerateSetEquiv S hS t).val

private theorem enumerateSet_injective (S : Finset (Fin w))
    (hS : S.card = 2 * k) : Function.Injective (enumerateSet S hS) := by
  intro a b hab
  apply (enumerateSetEquiv S hS).injective
  exact Subtype.ext hab

private theorem enumerateSet_image (S : Finset (Fin w))
    (hS : S.card = 2 * k) :
    Finset.univ.image (enumerateSet S hS) = S := by
  classical
  ext i
  constructor
  · intro h
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h
    exact (enumerateSetEquiv S hS t).property
  · intro hi
    let t := (enumerateSetEquiv S hS).symm ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, by
      change (enumerateSetEquiv S hS t).val = i
      dsimp [t]
      rw [Equiv.apply_symm_apply]
    ⟩

/-- Final-node selected coordinates, bins and exact selector-image mass
from the single original good projection of the actual retained tuple set. -/
theorem final_selection
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (Q : ℕ) (hQ : 0 < Q)
    (Y' : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (G : Finset (Fin w)) (hG : (2 * k) *
      RestorationCoverParameters.B2 Q < G.card)
    (hmass : RestorationCoverParameters.theta Q ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid w).prob
        (· ∈ Y'))
    (hk : 1 ≤ k) :
    ∃ e : Fin k → Fin w, Function.Injective e ∧
      (∀ t, e t ∈ G) ∧ ∃ p : Fin k → Fin s,
      (12 / 25 : ℝ) <
        (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob
          (· ∈ selectorImage Y' e p) := by
  classical
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  obtain ⟨S, hSG, hScard, hgood⟩ := good_projection_in_dense_group
    χ Y' G (2 * k) (RestorationCoverParameters.B2 Q) Q hQ rfl hG hmass
  let e₀ : Fin (2 * k) → Fin w := enumerateSet S hScard
  have he₀ : Function.Injective e₀ := enumerateSet_injective S hScard
  have himage : Finset.univ.image e₀ = S := enumerateSet_image S hScard
  have hgood' : (99 / 100 : ℝ) ≤
      ProductProjections.projectionMass (fun _ : Fin w => χ)
        (· ∈ Y') (Finset.univ.image e₀) := by simpa only [himage] using hgood
  obtain ⟨e, he, hsub, p, hcol⟩ :=
    exists_original_final_selector_image μ hs k hk Y' e₀ he₀ hgood'
  refine ⟨e, he, ?_, p, hcol⟩
  intro t
  exact hSG (himage ▸ hsub t)

/-- First-Bob selection charges the actual query child, while preserving
the original selected labels and one correlated selector-image event. -/
theorem bob_child_selection
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (Q : ℕ) (hQ : 0 < Q)
    (Y' : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (G : Finset (Fin w)) (hG : (2 * k) *
      RestorationCoverParameters.B2 Q < G.card)
    (hmass : RestorationCoverParameters.theta Q ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid w).prob
        (· ∈ Y'))
    (query : (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)) → Bool)
    (hk : 1 ≤ k) :
    ∃ b : Bool, ∃ e : Fin k → Fin w, Function.Injective e ∧
      (∀ t, e t ∈ G) ∧ ∃ p : Fin k → Fin s,
      (12 / 25 : ℝ) <
        (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob
          (· ∈ selectorImage (ReferenceColumnStep.columnChild Y' query b) e p) := by
  classical
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  obtain ⟨S, hSG, hScard, hgood⟩ := good_projection_in_dense_group
    χ Y' G (2 * k) (RestorationCoverParameters.B2 Q) Q hQ rfl hG hmass
  let e₀ : Fin (2 * k) → Fin w := enumerateSet S hScard
  have he₀ : Function.Injective e₀ := enumerateSet_injective S hScard
  have himage : Finset.univ.image e₀ = S := enumerateSet_image S hScard
  have hgood' : (99 / 100 : ℝ) ≤
      ProductProjections.projectionMass (fun _ : Fin w => χ)
        (· ∈ Y') (Finset.univ.image e₀) := by simpa only [himage] using hgood
  obtain ⟨b, e, he, hsub, p, hcol⟩ :=
    exists_original_bob_child_selector_image μ hs k hk Y' e₀ he₀ query hgood'
  refine ⟨b, e, he, ?_, p, hcol⟩
  intro t
  exact hSG (himage ▸ hsub t)

/-- The density-group size cannot be the one-coordinate case: the
displayed lower bound already exceeds that case even at `δ=1`. -/
theorem dyadic_group_even (n s κ : ℕ) (δ : ℝ)
    (hs : 0 < s) (hκ : 0 < κ) (hδ : δ ≤ 1)
    (hsize : 16 * (s : ℝ) * (κ : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) * δ) :
    0 < n ∧ 2 ^ n = 2 * 2 ^ (n - 1) := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hsize
    norm_num at hsize
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hκ1)]
  refine ⟨hn, ?_⟩
  have he : n - 1 + 1 = n := by omega
  conv_lhs => rw [← he, pow_succ]
  ring

/-- Apply final-node template selection directly at the dyadic group
returned by the actual density front end. -/
theorem final_dyadic_selection
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (Q n κ : ℕ) (hQ : 0 < Q) (hκ : 0 < κ)
    (δ : ℝ) (hδ : δ ≤ 1)
    (hsize : 16 * (s : ℝ) * (κ : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) * δ)
    (Y' : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (G : Finset (Fin w))
    (hG : (2 ^ n) * RestorationCoverParameters.B2 Q < G.card)
    (hmass : RestorationCoverParameters.theta Q ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid w).prob
        (· ∈ Y')) :
    ∃ e : Fin (2 ^ (n - 1)) → Fin w, Function.Injective e ∧
      (∀ t, e t ∈ G) ∧ ∃ p : Fin (2 ^ (n - 1)) → Fin s,
      (12 / 25 : ℝ) <
        (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid
          (2 ^ (n - 1))).prob (· ∈ selectorImage Y' e p) := by
  have hspos : 0 < s := by omega
  have ⟨_, heven⟩ := dyadic_group_even n s κ δ hspos hκ hδ hsize
  have hk : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  apply final_selection μ hs Q hQ Y' G
  · simpa only [heven] using hG
  · exact hmass
  · exact hk

/-- The analogous selected image at the charged child of the actual
first Bob query, still using the same original retained tuple event. -/
theorem bob_child_dyadic_selection
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (Q n κ : ℕ) (hQ : 0 < Q) (hκ : 0 < κ)
    (δ : ℝ) (hδ : δ ≤ 1)
    (hsize : 16 * (s : ℝ) * (κ : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) * δ)
    (Y' : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (G : Finset (Fin w))
    (hG : (2 ^ n) * RestorationCoverParameters.B2 Q < G.card)
    (hmass : RestorationCoverParameters.theta Q ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid w).prob
        (· ∈ Y'))
    (query : (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)) → Bool) :
    ∃ b : Bool, ∃ e : Fin (2 ^ (n - 1)) → Fin w, Function.Injective e ∧
      (∀ t, e t ∈ G) ∧ ∃ p : Fin (2 ^ (n - 1)) → Fin s,
      (12 / 25 : ℝ) <
        (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid
          (2 ^ (n - 1))).prob
            (· ∈ selectorImage (ReferenceColumnStep.columnChild Y' query b) e p) := by
  have hspos : 0 < s := by omega
  have ⟨_, heven⟩ := dyadic_group_even n s κ δ hspos hκ hδ hsize
  have hk : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by decide)
  apply bob_child_selection μ hs Q hQ Y' G
  · simpa only [heven] using hG
  · exact hmass
  · exact hk

end Paper2.ProtectedIncomingSelection

#print axioms Paper2.ProtectedIncomingSelection.final_selection
#print axioms Paper2.ProtectedIncomingSelection.bob_child_selection
#print axioms Paper2.ProtectedIncomingSelection.dyadic_group_even
#print axioms Paper2.ProtectedIncomingSelection.final_dyadic_selection
#print axioms Paper2.ProtectedIncomingSelection.bob_child_dyadic_selection
