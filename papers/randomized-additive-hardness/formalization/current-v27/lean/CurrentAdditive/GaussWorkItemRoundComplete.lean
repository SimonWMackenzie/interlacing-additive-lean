import CurrentAdditive.GaussWorkItemRoundAccum
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! A single fixed physical program executes one reusable column-request
round: serialize, frame, prepend, and clear all temporary banks. -/

namespace CurrentAdditive.GaussWorkItemRoundComplete

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev Bank := GaussWorkItemRoundAccum.Bank

private noncomputable abbrev C123 :=
  (GaussWorkItemRoundAccum.C12, (none : Option Bool))
private abbrev C4 := (((), none) : Unit × Option Bool)
private abbrev C5 := (((), none) : Unit × Option Bool)

noncomputable def p0123 :=
  BitMachineRawSequence.program GaussWorkItemRoundAccum.program
    GaussWorkItemCleanup.program GaussWorkItemCleanup.Label.raw C123 C4

noncomputable def program :=
  BitMachineRawSequence.program p0123
    GaussWorkItemDisposableCleanup.program
    GaussWorkItemDisposableCleanup.Label.matrix (C123, C4) C5

private abbrev InputLabel {α β : Type} (_ : α → β) : Type := α

def start : InputLabel program :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))))

noncomputable def control := ((C123, C4), C5)

noncomputable def accumClock {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k) : Nat :=
  let raw := GaussWorkItemContextSerialize.workPacket B f j
  let field := SourceListMachineWriter.result true raw
  (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
    (2 * f.val + 2) + (2 * j.val + 2) + 2 +
    (2 * raw.length + 2) + 1 +
    MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W raw
      ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2) + 1 +
    (2 * field.length + 2) + 1

noncomputable def roundPush : Nat :=
  BitMachineStackGrowth.perStep GaussWorkItemRoundAccum.program

noncomputable def roundClock {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k) : Nat :=
  let raw := GaussWorkItemContextSerialize.workPacket B f j
  let field := SourceListMachineWriter.result true raw
  accumClock B f j + raw.length + field.length +
    3 * (roundPush * accumClock B f j) + 11

theorem physical_round {m k : Nat}
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
    ∃ t ≤ roundClock B f j,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))))),
          ((C123, C4), C5), S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, ((C123, C4), C5),
          Function.update S ⟨24, by omega⟩
            (SourceListMachineWriter.result true
                (GaussWorkItemContextSerialize.workPacket B f j) ++ old)⟩ := by
  let raw := GaussWorkItemContextSerialize.workPacket B f j
  let field := SourceListMachineWriter.result true raw
  obtain ⟨a, Wbank, ha, hacc⟩ :=
    GaussWorkItemRoundAccum.physical_item_field_accum B f j S old
      hmat hf hj h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h24 hblank
  let S1 := GaussWorkItemCallbackFields.afterItem S
    (GaussPhysical.encodeTypedMatrix B)
    (List.replicate f.val true) (List.replicate j.val true) raw Wbank
  let S2 := Function.update S1 ⟨13, by omega⟩ field
  let S3 := Function.update S2 ⟨24, by omega⟩ (field ++ old)
  have hraw : S3 ⟨8, by omega⟩ = raw := by
    simp [S3, S2, S1, GaussWorkItemCallbackFields.output]
  have hfield : S3 ⟨13, by omega⟩ = field := by
    simp [S3, S2]
  have hclean1 := GaussWorkItemCleanup.physical_cleanup S3
  let S4 := Function.update (Function.update S3 ⟨8, by omega⟩ [])
    ⟨13, by omega⟩ []
  obtain ⟨u, hu, hfirst⟩ := BitMachineRawSequence.runs
    GaussWorkItemRoundAccum.program GaussWorkItemCleanup.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
    GaussWorkItemCleanup.Label.raw C123 C123 C4 C4 S S3 S4 a
    ((S3 ⟨8, by omega⟩).length + (S3 ⟨13, by omega⟩).length + 4)
    (by simpa only [S3, S2, S1, raw, field, C123] using hacc)
    (by simpa only [S4] using hclean1)
  have hclean2 := GaussWorkItemDisposableCleanup.physical_cleanup S4
  let S5 := BitMachineClearBank.cleared GaussWorkItemDisposableCleanup.cells S4
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    p0123 GaussWorkItemDisposableCleanup.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))))
    GaussWorkItemDisposableCleanup.Label.matrix
    (C123, C4) (C123, C4) C5 C5 S S4 S5 u
    ((S4 ⟨9, by omega⟩).length + (S4 ⟨10, by omega⟩).length +
      (S4 ⟨11, by omega⟩).length + 5)
    (by simpa only [p0123] using hfirst)
    (by simpa only [S5] using hclean2)
  have hacc_clock : a ≤ accumClock B f j := by
    simpa [accumClock, raw, field] using ha
  have hacc_run :
      ((advance GaussWorkItemRoundAccum.program)^[a])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
          C123, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, C123, S3⟩ := by
    simpa only [S3, S2, S1, raw, field, C123] using hacc
  have hg9 := BitMachineStackGrowth.run_growth
    GaussWorkItemRoundAccum.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
      C123, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) a ⟨9, by omega⟩
  have hg10 := BitMachineStackGrowth.run_growth
    GaussWorkItemRoundAccum.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
      C123, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) a ⟨10, by omega⟩
  have hg11 := BitMachineStackGrowth.run_growth
    GaussWorkItemRoundAccum.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
      C123, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) a ⟨11, by omega⟩
  rw [hacc_run] at hg9 hg10 hg11
  have hpa : roundPush * a ≤ roundPush * accumClock B f j :=
    Nat.mul_le_mul_left roundPush hacc_clock
  have hlen8 : (S3 ⟨8, by omega⟩).length = raw.length := by rw [hraw]
  have hlen13 : (S3 ⟨13, by omega⟩).length = field.length := by rw [hfield]
  have hlen9 : (S4 ⟨9, by omega⟩).length ≤ roundPush * a := by
    simpa [S4, roundPush, h9] using hg9
  have hlen10 : (S4 ⟨10, by omega⟩).length ≤ roundPush * a := by
    simpa [S4, roundPush, h10] using hg10
  have hlen11 : (S4 ⟨11, by omega⟩).length ≤ roundPush * a := by
    simpa [S4, roundPush, h11] using hg11
  refine ⟨t, ?_, ?_⟩
  · change t ≤ accumClock B f j + raw.length + field.length +
      3 * (roundPush * accumClock B f j) + 11
    omega
  have hbank := GaussWorkItemRoundBank.clean_round S
    (GaussPhysical.encodeTypedMatrix B)
    (List.replicate f.val true) (List.replicate j.val true)
    raw field (field ++ old) Wbank h6 h7 h8 h9 h10 h11 h13
  change S5 = Function.update S ⟨24, by omega⟩ (field ++ old) at hbank
  simpa [program, raw, field, S5, S4, S3, S2, S1, C123, C4, C5,
    hbank] using hrun

#print axioms physical_round

end CurrentAdditive.GaussWorkItemRoundComplete
