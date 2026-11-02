import CurrentAdditive.RationalSubtractRouteRun

namespace EthInapproximability.CurrentPaper.RationalSubtractRouteSpec

open EthInapproximability.CurrentPaper
open RationalSubtractRoute RationalSubtractCore
open BitMachineStackEmbedding

theorem copied_update (phase : Fin 7) (S : Bank) :
    copied phase S =
      Function.update
        (Function.update S (copySlots phase 1)
          (S (copySlots phase 0) ++ S (copySlots phase 1)))
        26 [] := by
  funext j
  by_cases hd : j = copySlots phase 1
  · subst j
    have hne : copySlots phase 1 ≠ (26 : Fin 32) := by
      fin_cases phase <;> decide
    rw [copied, bank_at]
    simp [BitMachineCopy.stackContents, Function.update_of_ne hne]
  · by_cases ht : j = (26 : Fin 32)
    · subst j
      rw [copied_scratch]
      simp
    · by_cases hs : j = copySlots phase 0
      · subst j
        have hsd : copySlots phase 0 ≠ copySlots phase 1 :=
          (copySlots phase).injective.ne (by decide)
        have hst : copySlots phase 0 ≠ (26 : Fin 32) := by
          fin_cases phase <;> decide
        rw [copied, bank_at]
        simp [BitMachineCopy.stackContents,
          Function.update_of_ne hsd, Function.update_of_ne hst]
      · have hout : ¬ ∃ k : Fin 3, copySlots phase k = j := by
          intro ⟨k,hk⟩
          fin_cases k
          · exact hs hk.symm
          · exact hd hk.symm
          · have hslot : copySlots phase 2 = (26 : Fin 32) := by
              fin_cases phase <;> rfl
            change copySlots phase 2 = j at hk
            rw [hslot] at hk
            exact ht hk.symm
        rw [copied, bank_outside _ _ _ j hout]
        simp [Function.update_of_ne, hd, ht]

theorem routed_flat_eq_canonical
    (a b : CurrentAdditive.CodeDCodec.RawRat) :
    RationalSubtractRouteRun.routed (RationalFlatPad32.extendedFlatBank a b) =
      RationalSubtractSpec.canonicalBank a b := by
  funext j
  fin_cases j <;>
    simp [RationalSubtractRouteRun.routed, copied_update, RationalFlatPad32.extendedFlatBank,
      RationalProductNestedFlat.flatBank, RationalSubtractSpec.canonicalBank,
      BitMachineBroadcast.contents, BitMachineClearBank.cleared,
      Fin.exists_fin_succ, clearSlots, copySlots] <;> decide

theorem precleared_flat
    (a b : CurrentAdditive.CodeDCodec.RawRat) :
    RationalSubtractRouteRun.precleared
      (RationalFlatPad32.extendedFlatBank a b) =
        RationalFlatPad32.extendedFlatBank a b := by
  apply RationalSubtractRouteRun.precleared_eq
  · rfl
  · rfl

theorem full_routed_flat_eq_canonical
    (a b : CurrentAdditive.CodeDCodec.RawRat) :
    RationalSubtractRouteRun.routed
      (RationalSubtractRouteRun.precleared
        (RationalFlatPad32.extendedFlatBank a b)) =
      RationalSubtractSpec.canonicalBank a b := by
  rw [precleared_flat, routed_flat_eq_canonical]

end EthInapproximability.CurrentPaper.RationalSubtractRouteSpec
