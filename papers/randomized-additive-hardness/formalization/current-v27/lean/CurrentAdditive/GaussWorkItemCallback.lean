import CurrentAdditive.GaussWorkItemCopyContext
import CurrentAdditive.GaussWorkItemContextSerialize

/-! A single fixed TM2 callback copies the retained matrix, free column and
current column into disposable banks, then serializes the exact Bank3 work
item.  It preserves the original context, so it can be iterated after the
outer index controller is supplied. -/

namespace CurrentAdditive.GaussWorkItemCallback

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussStateMatrixContext.Bank

noncomputable def program :=
  BitMachineRawSequence.program GaussWorkItemCopyContext.program GaussWorkItemContextSerialize.copiedProgram
    (.emit 0) ((none, none), none) none

theorem physical_item {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (output : List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hj : S ⟨5, by omega⟩ = List.replicate j.val true)
    (h6 : S ⟨6, by omega⟩ = [])
    (h7 : S ⟨7, by omega⟩ = [])
    (h8 : S ⟨8, by omega⟩ = output)
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = []) :
    ∃ (t : Nat) (W : BitMachineBankSerialize.Bank 3),
      t ≤ (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
        (2 * f.val + 2) + (2 * j.val + 2) + 2 +
        (2 * (GaussWorkItemContextSerialize.workPacket B f j).length + 2) + 1 ∧
      let S3 := Function.update
        (Function.update
          (Function.update S ⟨9, by omega⟩
            (GaussPhysical.encodeTypedMatrix B))
          ⟨10, by omega⟩ (List.replicate f.val true))
        ⟨11, by omega⟩ (List.replicate j.val true)
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none, none), none), none), S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (((none, none), none), none),
          (BitMachineStackEmbedding.stackCfg GaussWorkItemContextSerialize.copiedSlot S3
            (BitMachineBankSerialize.cfg none none W [] []
              (GaussWorkItemContextSerialize.workPacket B f j ++ output))).stk⟩ := by
  let matrix := GaussPhysical.encodeTypedMatrix B
  let free := List.replicate f.val true
  let index := List.replicate j.val true
  let S1 := Function.update S ⟨9, by omega⟩ matrix
  let S2 := Function.update S1 ⟨10, by omega⟩ free
  let S3 := Function.update S2 ⟨11, by omega⟩ index
  obtain ⟨a, ha, hcopy⟩ :=
    GaussWorkItemCopyContext.physical_copies S matrix free index
      hmat hf hj h9 h10 h11 h12
  have hmat3 : S3 ⟨9, by omega⟩ = matrix := by simp [S3, S2, S1]
  have hfree3 : S3 ⟨10, by omega⟩ = free := by simp [S3, S2]
  have hindex3 : S3 ⟨11, by omega⟩ = index := by simp [S3]
  have h6_3 : S3 ⟨6, by omega⟩ = [] := by
    simp [S3, S2, S1, h6]
  have h7_3 : S3 ⟨7, by omega⟩ = [] := by
    simp [S3, S2, S1, h7]
  have h8_3 : S3 ⟨8, by omega⟩ = output := by
    simp [S3, S2, S1, h8]
  obtain ⟨b, W, hb, hser⟩ :=
    GaussWorkItemContextSerialize.physical_one_item_copied B f j S3 output
      hmat3 hindex3 hfree3 h6_3 h7_3 h8_3
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    GaussWorkItemCopyContext.program GaussWorkItemContextSerialize.copiedProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (.emit 0)
    ((none, none), none) ((none, none), none)
    none none S S3
    (BitMachineStackEmbedding.stackCfg GaussWorkItemContextSerialize.copiedSlot S3
      (BitMachineBankSerialize.cfg none none W [] []
        (GaussWorkItemContextSerialize.workPacket B f j ++ output))).stk a b
    (by simpa [S3, S2, S1] using hcopy)
    (by simpa only [BitMachineStackEmbedding.stackCfg] using hser)
  refine ⟨t, W, ?_, ?_⟩
  · simp [matrix, free, index] at ha
    omega
  · simpa [program, S3, S2, S1] using hrun

#print axioms physical_item

end CurrentAdditive.GaussWorkItemCallback
