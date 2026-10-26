import CurrentAdditive.FeatureInputPrep64

/-! The physically copied inputs are precisely the prepared three-word
configuration expected by the checked feature-prepend controller. -/

namespace CurrentAdditive.FeaturePreparedReady64

open EthInapproximability.CurrentPaper
open CurrentAdditive.FeaturePreparedCallback
open CurrentAdditive.FeatureContext64

private def jLocal : FeaturePreparedCallback.Stack :=
  FeaturePreparedCallback.pairSlots (.inl 0)
private def yLocal : FeaturePreparedCallback.Stack :=
  FeaturePreparedCallback.pairSlots (.inl 1)
private def cLocal : FeaturePreparedCallback.Stack :=
  FeaturePreparedCallback.countSource

private theorem j_location : locate jLocal = ⟨16,by omega⟩ := rfl
private theorem y_location : locate yLocal = ⟨17,by omega⟩ := rfl
private theorem c_location : locate cLocal = ⟨21,by omega⟩ := rfl

theorem copied_ready (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat))
    (hblank : ∀ k : FeaturePreparedCallback.Stack, S (locate k) = []) :
    Ready (FeatureInputPrep64.after S j y c) j y c := by
  intro k
  by_cases hj : k = jLocal
  · subst k
    simp [FeatureInputPrep64.after,
      FeaturePreparedCallback.initialBank, jLocal,
      FeaturePreparedCallback.pairSlots, locate, locateMap]
  by_cases hy : k = yLocal
  · subst k
    simp [FeatureInputPrep64.after,
      FeaturePreparedCallback.initialBank, yLocal,
      FeaturePreparedCallback.pairSlots, locate, locateMap]
  by_cases hc : k = cLocal
  · subst k
    simp [FeatureInputPrep64.after,
      FeaturePreparedCallback.initialBank, cLocal,
      FeaturePreparedCallback.pairSlots,
      FeaturePreparedCallback.countSource,
      FeaturePreparedCallback.countSlots, locate, locateMap]
  have h16 : locate k ≠ (⟨16,by omega⟩ : Bank) := by
    intro h
    exact hj (locate.injective (h.trans j_location.symm))
  have h17 : locate k ≠ (⟨17,by omega⟩ : Bank) := by
    intro h
    exact hy (locate.injective (h.trans y_location.symm))
  have h21 : locate k ≠ (⟨21,by omega⟩ : Bank) := by
    intro h
    exact hc (locate.injective (h.trans c_location.symm))
  change k ≠ FeaturePreparedCallback.pairSlots (.inl 0) at hj
  change k ≠ FeaturePreparedCallback.pairSlots (.inl 1) at hy
  change k ≠ FeaturePreparedCallback.countSource at hc
  simpa only [FeatureInputPrep64.after,
    Function.update_of_ne h21, Function.update_of_ne h17,
    Function.update_of_ne h16, FeaturePreparedCallback.initialBank,
    if_neg hj, if_neg hy, if_neg hc] using hblank k

#print axioms copied_ready

end CurrentAdditive.FeaturePreparedReady64
