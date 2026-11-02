import CurrentAdditive.GaussWorkItemRoundRun

/-! One fixed three-stage program now prepends the framed work item to the
physical output accumulator, retaining B, f, j and the Gauss state. -/

namespace CurrentAdditive.GaussWorkItemRoundAccum

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev Bank := GaussWorkItemRoundRun.Bank

private noncomputable abbrev W := GaussWorkItemRoundRun.W
noncomputable abbrev C12 :=
  (GaussWorkItemRoundRun.C1,
    GaussWorkItemRoundRun.C2)

noncomputable def program :=
  BitMachineRawSequence.program GaussWorkItemRoundRun.p01
    GaussWorkItemAccumulator.program BitMachineCopy.Label.scan C12 none

theorem physical_item_field_accum {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (old : List Bool)
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
    (h15 : S ⟨15, by omega⟩ = [])
    (h24 : S ⟨24, by omega⟩ = old)
    (hblank : ∀ i, S (GaussWorkItemFrameContext.slots.machine i) = []) :
    ∃ (t : Nat) (Wbank : BitMachineBankSerialize.Bank 3),
      t ≤ (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
        (2 * f.val + 2) + (2 * j.val + 2) + 2 +
        (2 * (GaussWorkItemContextSerialize.workPacket B f j).length + 2) + 1 +
        MachineInvokeFull.uniformBound W
          (GaussWorkItemContextSerialize.workPacket B f j)
          ((UnaryBinaryEncoding.coefficient + 7) *
            ((GaussWorkItemContextSerialize.workPacket B f j).length + 1)^2) + 1 +
        (2 * (SourceListMachineWriter.result true
          (GaussWorkItemContextSerialize.workPacket B f j)).length + 2) + 1 ∧
      let raw := GaussWorkItemContextSerialize.workPacket B f j
      let field := SourceListMachineWriter.result true raw
      let S1 := GaussWorkItemCallbackFields.afterItem S
        (GaussPhysical.encodeTypedMatrix B)
        (List.replicate f.val true) (List.replicate j.val true) raw Wbank
      let S2 := Function.update S1 ⟨13, by omega⟩ field
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
          (C12, none), S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (C12, none), Function.update S2 ⟨24, by omega⟩
          (field ++ old)⟩ := by
  let raw := GaussWorkItemContextSerialize.workPacket B f j
  let field := SourceListMachineWriter.result true raw
  obtain ⟨a, Wbank, ha, h01⟩ :=
    GaussWorkItemRoundRun.physical_item_and_field B f j S
      hmat hf hj h6 h7 h8 h9 h10 h11 h12 h13 h14 hblank
  let S1 := GaussWorkItemCallbackFields.afterItem S
    (GaussPhysical.encodeTypedMatrix B)
    (List.replicate f.val true) (List.replicate j.val true) raw Wbank
  let S2 := Function.update S1 ⟨13, by omega⟩ field
  have hfield : S2 ⟨13, by omega⟩ = field := by simp [S2]
  have haccum : S2 ⟨24, by omega⟩ = old := by
    have hp := GaussWorkItemCallbackFields.preserved_high S
      (GaussPhysical.encodeTypedMatrix B) (List.replicate f.val true)
      (List.replicate j.val true) raw Wbank
      ⟨24, by omega⟩ (by norm_num)
    simpa [S2] using hp.trans h24
  have hscratch : S2 ⟨15, by omega⟩ = [] := by
    have hp := GaussWorkItemCallbackFields.preserved_high S
      (GaussPhysical.encodeTypedMatrix B) (List.replicate f.val true)
      (List.replicate j.val true) raw Wbank
      ⟨15, by omega⟩ (by norm_num)
    simpa [S2] using hp.trans h15
  have hcopy := GaussWorkItemAccumulator.physical_prepend S2 field old
    hfield haccum hscratch
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    GaussWorkItemRoundRun.p01 GaussWorkItemAccumulator.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    BitMachineCopy.Label.scan C12 C12 none none S S2
    (Function.update S2 ⟨24, by omega⟩ (field ++ old))
    a (2 * field.length + 2)
    (by simpa [S2, S1, raw, field, C12] using h01)
    hcopy
  refine ⟨t, Wbank, ?_, ?_⟩
  · change t ≤ (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
        (2 * f.val + 2) + (2 * j.val + 2) + 2 +
        (2 * raw.length + 2) + 1 +
        MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W raw
          ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2) + 1 +
        (2 * field.length + 2) + 1
    change a ≤ (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
        (2 * f.val + 2) + (2 * j.val + 2) + 2 +
        (2 * raw.length + 2) + 1 +
        MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W raw
          ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2) + 1 at ha
    omega
  · simpa [program, S2, S1, raw, field, C12] using hrun

#print axioms physical_item_field_accum

end CurrentAdditive.GaussWorkItemRoundAccum
