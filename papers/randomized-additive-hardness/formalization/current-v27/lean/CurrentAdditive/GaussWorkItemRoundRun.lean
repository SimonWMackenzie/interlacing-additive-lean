import CurrentAdditive.GaussWorkItemRoundBank

/-! The first literal two-stage join for one physical post-Gauss work item:
produce its Bank3 bytes from retained context, then length-frame them. -/

namespace CurrentAdditive.GaussWorkItemRoundRun

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev Bank := GaussWorkItemRoundBank.Bank

noncomputable abbrev W := SourceListMachineWriter.framingMachine true
def C1 : (((Option Bool × Option Bool) × Option Bool) × Option Bool) :=
  (((none, none), none), none)
noncomputable abbrev C2 :=
  MachineInvokeFull.control GaussWorkItemFrameContext.slots

noncomputable def p01 :=
  BitMachineRawSequence.program GaussWorkItemCallback.program
    GaussWorkItemFrameContext.program
    (MachineInvokeFull.start GaussWorkItemFrameContext.slots)
    C1 C2

theorem physical_item_and_field {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hj : S ⟨5, by omega⟩ = List.replicate j.val true)
    (h6 : S ⟨6, by omega⟩ = [])
    (h7 : S ⟨7, by omega⟩ = [])
    (h8 : S ⟨8, by omega⟩ = [])
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = [])
    (h13 : S ⟨13, by omega⟩ = [])
    (h14 : S ⟨14, by omega⟩ = [])
    (hblank : ∀ i, S (GaussWorkItemFrameContext.slots.machine i) = []) :
    ∃ (t : Nat) (Wbank : BitMachineBankSerialize.Bank 3),
      t ≤ (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
        (2 * f.val + 2) + (2 * j.val + 2) + 2 +
        (2 * (GaussWorkItemContextSerialize.workPacket B f j).length + 2) + 1 +
        MachineInvokeFull.uniformBound W
          (GaussWorkItemContextSerialize.workPacket B f j)
          ((UnaryBinaryEncoding.coefficient + 7) *
            ((GaussWorkItemContextSerialize.workPacket B f j).length + 1)^2) + 1 ∧
      let raw := GaussWorkItemContextSerialize.workPacket B f j
      let S1 := GaussWorkItemCallbackFields.afterItem S
        (GaussPhysical.encodeTypedMatrix B)
        (List.replicate f.val true) (List.replicate j.val true) raw Wbank
      ((advance p01)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          (C1, C2), S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (C1, C2), Function.update S1 ⟨13, by omega⟩
          (SourceListMachineWriter.result true raw)⟩ := by
  let raw := GaussWorkItemContextSerialize.workPacket B f j
  obtain ⟨a, Wbank, ha, hitem⟩ :=
    GaussWorkItemCallbackFields.physical_item_full B f j S
      hmat hf hj h6 h7 h8 h9 h10 h11 h12
  let S1 := GaussWorkItemCallbackFields.afterItem S
    (GaussPhysical.encodeTypedMatrix B)
    (List.replicate f.val true) (List.replicate j.val true) raw Wbank
  have hraw : S1 ⟨8, by omega⟩ = raw :=
    GaussWorkItemCallbackFields.output S _ _ _ raw Wbank
  have htarget : S1 ⟨13, by omega⟩ = [] := by
    exact (GaussWorkItemCallbackFields.preserved_high S _ _ _ raw Wbank
      ⟨13, by omega⟩ (by norm_num)).trans h13
  have hscratch : S1 ⟨14, by omega⟩ = [] := by
    exact (GaussWorkItemCallbackFields.preserved_high S _ _ _ raw Wbank
      ⟨14, by omega⟩ (by norm_num)).trans h14
  have hembed : ∀ i, S1 (GaussWorkItemFrameContext.slots.machine i) = [] := by
    intro i
    have hz : 12 ≤ (GaussWorkItemFrameContext.slots.machine i).val := by
      change 12 ≤ 16 + i.val
      omega
    exact (GaussWorkItemCallbackFields.preserved_high S _ _ _ raw Wbank
      (GaussWorkItemFrameContext.slots.machine i) hz).trans (hblank i)
  obtain ⟨b, hb, hframe⟩ :=
    GaussWorkItemFrameContext.physical_field S1 raw
      hraw htarget hscratch hembed
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    GaussWorkItemCallback.program GaussWorkItemFrameContext.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (MachineInvokeFull.start GaussWorkItemFrameContext.slots)
    C1 C1 C2 C2 S S1
    (Function.update S1 ⟨13, by omega⟩
      (SourceListMachineWriter.result true raw)) a b
    (by simpa only [S1, raw, C1] using hitem)
    (by simpa only [GaussWorkItemFrameContext.program] using hframe)
  refine ⟨t, Wbank, ?_, ?_⟩
  · change b ≤ MachineInvokeFull.uniformBound
      (SourceListMachineWriter.framingMachine true) raw
        ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2) at hb
    dsimp only [W, raw] at hb ⊢
    omega
  · simpa [p01, S1, raw] using hrun

#print axioms physical_item_and_field

end CurrentAdditive.GaussWorkItemRoundRun
