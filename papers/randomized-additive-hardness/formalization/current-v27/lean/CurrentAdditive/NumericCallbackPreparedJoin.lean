import CurrentAdditive.OuterPacketCoordinateRelocate
import CurrentAdditive.IndexedCodeDNatCoordinateStitched
import CurrentAdditive.TypedNumericCodeDJoin

/-! The checked low-cell cleanup supplies the exact input bank of the
three-stage physical Code D coordinate callback. The theorem keeps the
existing callback's all-input machine and produces its actual output cell. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open CurrentAdditive.CodeDCanonicalSourceV2
open Turing

theorem prepared_numeric_callback {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) (T : StackN contextTwoSize → List Bool)
    (h0 : T 0 = codeDGetterPacket (encodedSource out) j.val)
    (h6 : T 6 = List.replicate p.val true)
    (hlow : ∀ k : StackN contextTwoSize,
      1 ≤ k.val → k.val < 32 → k.val ≠ 6 → T k = [])
    (hhigh : ∀ k : StackN contextTwoSize,
      32 ≤ k.val → T k = []) :
    ∃ t,
      (((advance numericCoordinateProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
                recordSlots)))),
          (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots),
            ((((), none), ((), none)), none)),
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              coordinateSlots),
           coordinateReady T (List.replicate p.val true)⟩)).stk
          (6 : StackN contextTwoSize) = (out[j].1 p).bits := by
  let S := coordinateReady T (List.replicate p.val true)
  have hready := coordinateReady_cells T
    (List.replicate p.val true)
    (codeDGetterPacket (encodedSource out) j.val) h0 h6 hlow
  change S 0 = _ ∧ S 4 = _ ∧
    (∀ k : StackN contextTwoSize,
      1 ≤ k.val → k.val < 32 → k.val ≠ 4 → S k = []) at hready
  rcases hready with ⟨hsource, hindex, hrest⟩
  have hlowblank (i : StackN contextTwoSize)
      (hi : 1 ≤ i.val) (hj : i.val < 32) (hk : i.val ≠ 4) :
      S i = [] := hrest i hi hj hk
  have hprivate (i : StackN contextTwoSize) (hi : 32 ≤ i.val) :
      S i = [] := by
    rw [show S i = T i from coordinateReady_high_preserved T
      (List.replicate p.val true) i hi]
    exact hhigh i hi
  have hblank1 : ∀ k, S (recordSlots.machine k) = [] := by
    intro k
    apply hprivate
    dsimp [recordSlots]
    omega
  have hblank2 : ∀ k, S (wordSlots.machine k) = [] := by
    intro k
    apply hprivate
    dsimp [wordSlots]
    omega
  have hpacketblank : ∀ i : Fin 10, i ≠ 7 → i ≠ 8 →
      S (packetAmbient contextTwoSize (packetLocate (.inl i))) = [] := by
    intro i _ _
    apply hlowblank
    all_goals dsimp [packetAmbient, packetLocate]; omega
  obtain ⟨t, _, Sf, hr⟩ := numeric_coordinate_stitched out j p S
    hsource
    (hlowblank 1 (by decide) (by decide) (by decide))
    (hlowblank 3 (by decide) (by decide) (by decide))
    (hlowblank 2 (by decide) (by decide) (by decide))
    hblank1 hblank2 hindex
    (hlowblank 17 (by decide) (by decide) (by decide))
    (hlowblank 18 (by decide) (by decide) (by decide))
    (hlowblank 22 (by decide) (by decide) (by decide))
    hpacketblank
    (hlowblank 21 (by decide) (by decide) (by decide))
    (hlowblank 5 (by decide) (by decide) (by decide))
    (hlowblank 6 (by decide) (by decide) (by decide))
  refine ⟨t, ?_⟩
  change (((advance numericCoordinateProgram)^[t])
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            recordSlots)))),
      (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          recordSlots,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          wordSlots),
        ((((), none), ((), none)), none)),
       CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          coordinateSlots), S⟩)).stk (6 : StackN contextTwoSize) = _
  rw [hr]
  rw [show coordinateSlots.target = (6 : StackN contextTwoSize) by rfl]
  simp

#print axioms prepared_numeric_callback

end CurrentAdditive.IndexedExecutableStepRecovery
