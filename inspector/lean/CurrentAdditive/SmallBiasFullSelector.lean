import CurrentAdditive.SmallBiasLift

/-!
# The v27 full selector tuple list

Source: v27 `sections/07-yao.tex`, `yao:entry`, `yao:projection-product`,
and `yao:lift`. Every address tuple occurs exactly once; consequently each
product-set test has its exact uniform frequency, with no sampling event.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Canonical enumeration of all selector tuples, using distinct labels. -/
noncomputable def fullSelector (q H : ℕ) :
    Fin (Fintype.card (Fin q → Fin H)) → Fin q → Fin H :=
  (Fintype.equivFin (Fin q → Fin H)).symm

theorem fullSelector_bijective (q H : ℕ) :
    Function.Bijective (fullSelector q H) :=
  (Fintype.equivFin (Fin q → Fin H)).symm.bijective

/-- Exact count of labels in every product of coordinate address sets. -/
theorem fullSelector_rectangle_count (q H : ℕ)
    (J : Fin q → Finset (Fin H)) :
    ((Finset.univ : Finset (Fin (Fintype.card (Fin q → Fin H)))).filter
      (fun z => selectorRectangle J (fullSelector q H z))).card =
      ∏ g, (J g).card := by
  classical
  let U : Finset (Fin (Fintype.card (Fin q → Fin H))) := Finset.univ.filter
    (fun z => selectorRectangle J (fullSelector q H z))
  have himage : U.image (fullSelector q H) = Fintype.piFinset J := by
    ext c
    simp only [Finset.mem_image, U, Finset.mem_filter, Finset.mem_univ,
      true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hc
      obtain ⟨z, rfl⟩ := (fullSelector_bijective q H).2 c
      exact ⟨z, hc, rfl⟩
  calc
    _ = U.card := rfl
    _ = (U.image (fullSelector q H)).card :=
      (Finset.card_image_of_injective U (fullSelector_bijective q H).1).symm
    _ = (Fintype.piFinset J).card := congrArg Finset.card himage
    _ = ∏ g, (J g).card := Fintype.card_piFinset J

/-- Exact product-set frequency implies the inherited selector condition.
The condition's slack is positive, so the exact full list satisfies it. -/
theorem fullSelector_good (q H S : ℕ) (hS : 0 < S) :
    selectorGood q H S (Fintype.card (Fin q → Fin H)) (fullSelector q H) := by
  classical
  intro J
  have hm : Fintype.card (Fin q → Fin H) = H ^ q := by
    simp
  have hcount := fullSelector_rectangle_count q H J
  have heq : selectorEmpirical (Fintype.card (Fin q → Fin H))
      (fullSelector q H) J = selectorVolume J := by
    rw [selectorEmpirical, selectorVolume, hcount, hm]
    push_cast
    rw [Finset.prod_div_distrib]
    simp
  rw [heq]
  have hden : 0 ≤ (1 : ℝ) / (4 * (S : ℝ)) := by positivity
  linarith

/-- The number of full selector labels is exactly `H^q`. -/
theorem fullSelector_size (q H : ℕ) :
    Fintype.card (Fin q → Fin H) = H ^ q := by simp

/-- V27 `yao:lift`, with the exact full selector list rather than a sampled
selector. The only outstanding data premise is that the actual labelled
array list has the required small bias. -/
theorem lower_bound_fullSelector_small_biased
    {V E : Type*} [Fintype V] {b t n : ℕ}
    (ht : 4 ≤ t)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c)
    (W : Fin n → Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool)
    (μ : Paper2.FiniteLaw (Fin n))
    (hμ : IsSmallBiased μ W
      ((1 / 2 : ℝ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2))) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b)) W) := by
  let q := 2 ^ (t - 1)
  let H := 2 ^ b
  let S := 2 ^ (2 ^ t - 1)
  have hm : 0 < Fintype.card (Fin q → Fin H) := by
    rw [fullSelector_size]
    positivity
  have hS : 0 < S := by dsimp [S]; positivity
  exact lower_bound_of_small_biased_payload ht hm edges index hno
    (fullSelector q H) (fullSelector_good q H S hS) W μ hμ

#print axioms CurrentAdditive.SmallBias.fullSelector_rectangle_count
#print axioms CurrentAdditive.SmallBias.fullSelector_good
#print axioms CurrentAdditive.SmallBias.lower_bound_fullSelector_small_biased

end CurrentAdditive.SmallBias
