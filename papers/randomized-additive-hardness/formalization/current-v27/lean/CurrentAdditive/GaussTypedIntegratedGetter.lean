import CurrentAdditive.GaussTypedGetterBridge
import CurrentAdditive.GaussGetterIntegratedClock

set_option maxHeartbeats 1000000

/-! The complete single-program nested getter on canonical typed matrices. -/

namespace CurrentAdditive.GaussTypedIntegratedGetter

open CurrentAdditive.GaussPhysical
open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussTypedGetterBridge
open EthInapproximability.CurrentPaper

theorem typed_getter_bank6 {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    let init := GaussGetterIntegrated.firstFrame
      (GaussNestedGetter.firstFrame
        (GaussNestedGetter.inputForeign j.val)
        (CylinderContextScanStep.initial (encodeTypedMatrix B) i.val))
    ∃ t ≤ 140 * ((encodeTypedMatrix B).length + 1)^3,
      (GaussGetterIntegrated.run t init).l = none ∧
      (GaussGetterIntegrated.run t init).stk 6 =
        encodeRawRat (rawOfRat (B i j)) ∧
      (GaussGetterIntegrated.run t init).stk 18 =
        encodeRawRat (rawOfRat (B i j)) ∧
      (GaussGetterIntegrated.run t init).stk 8 = encodeTypedMatrix B := by
  dsimp only
  let rowPre := (rowWords B).take i.val
  let rowSuffix := (rowWords B).drop (i.val+1)
  let cellPre := (cellWords B i).take j.val
  let cellSuffix := (cellWords B i).drop (j.val+1)
  let cell := encodeRawRat (rawOfRat (B i j))
  obtain ⟨hm, hri, hcj⟩ := typed_decomposition B i j
  have h := GaussGetterIntegratedClock.canonical_getter_cubic
    rowPre rowSuffix cellPre cellSuffix cell
  dsimp only at h
  obtain ⟨t, ht, hlabel, hcell6, hcell18, hmatrix⟩ := h
  have hcfg :
      GaussGetterIntegrated.firstFrame
        (GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign j.val)
          (CylinderContextScanStep.initial (encodeTypedMatrix B) i.val)) =
      GaussGetterIntegrated.firstFrame
        (GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign cellPre.length)
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode
              (rowPre ++ SourceListEncoding.encode
                (cellPre ++ cell :: cellSuffix) :: rowSuffix)) rowPre.length)) := by
    simp only [rowPre, rowSuffix, cellPre, cellSuffix, cell,
      hri, hcj, ← hm]
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hm] at ht
    exact ht
  · rw [← hcfg] at hlabel
    exact hlabel
  · rw [← hcfg] at hcell6
    exact hcell6
  · rw [← hcfg] at hcell18
    exact hcell18
  · rw [← hcfg] at hmatrix
    exact hmatrix.trans hm.symm

#print axioms typed_getter_bank6

end CurrentAdditive.GaussTypedIntegratedGetter
