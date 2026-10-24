import CurrentAdditive.GaussWorkListHeader

/-! Complete the V2 counted-list packet by physically prepending its count
field to the ordered item fields. -/

namespace CurrentAdditive.GaussWorkListHeaderJoin

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev Bank := GaussWorkListHeader.Bank
noncomputable abbrev C1 := MachineInvokeFull.control GaussWorkListHeader.slots
noncomputable def program := BitMachineRawSequence.program
  GaussWorkListHeader.program GaussWorkItemAccumulator.program
  BitMachineCopy.Label.scan C1 none

noncomputable def headerClock (k : Nat) : Nat :=
  let header := SourceListMachineWriter.result false (List.replicate k true)
  MachineInvokeFull.uniformBound
    (SourceListMachineWriter.framingMachine false)
    (List.replicate k true)
    ((UnaryBinaryEncoding.coefficient + 7) * (k + 1)^2) +
  (2 * header.length + 2) + 1

theorem physical_header_and_prepend (S : Bank → List Bool) (k : Nat)
    (fields : List Bool)
    (hwidth : S ⟨3, by omega⟩ = List.replicate k true)
    (h13 : S ⟨13, by omega⟩ = [])
    (h14 : S ⟨14, by omega⟩ = [])
    (h15 : S ⟨15, by omega⟩ = [])
    (h24 : S ⟨24, by omega⟩ = fields)
    (hblank : ∀ i, S (GaussWorkListHeader.slots.machine i) = []) :
    ∃ t ≤ headerClock k,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (MachineInvokeFull.start GaussWorkListHeader.slots)),
          (C1, none), S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (C1, none),
          Function.update
            (Function.update S ⟨13, by omega⟩
              (SourceListMachineWriter.result false (List.replicate k true)))
            ⟨24, by omega⟩
            (SourceListMachineWriter.result false (List.replicate k true) ++ fields)⟩ := by
  let header := SourceListMachineWriter.result false (List.replicate k true)
  let S1 := Function.update S ⟨13, by omega⟩ header
  obtain ⟨a, ha, hframe⟩ := GaussWorkListHeader.physical_header S k
    hwidth h13 h14 hblank
  have h13' : S1 ⟨13, by omega⟩ = header := by simp [S1]
  have h24' : S1 ⟨24, by omega⟩ = fields := by
    simp [S1, h24]
  have h15' : S1 ⟨15, by omega⟩ = [] := by
    simp [S1, h15]
  have hprep := GaussWorkItemAccumulator.physical_prepend S1 header fields
    h13' h24' h15'
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    GaussWorkListHeader.program GaussWorkItemAccumulator.program
    (MachineInvokeFull.start GaussWorkListHeader.slots)
    BitMachineCopy.Label.scan C1 C1 none none S S1
    (Function.update S1 ⟨24, by omega⟩ (header ++ fields))
    a (2 * header.length + 2)
    (by simpa only [S1, header, GaussWorkListHeader.program] using hframe)
    hprep
  refine ⟨t, ?_, ?_⟩
  · dsimp only [headerClock, header] at ht ⊢
    have ha' : a ≤ MachineInvokeFull.uniformBound
      (SourceListMachineWriter.framingMachine false)
      (List.replicate k true)
      ((UnaryBinaryEncoding.coefficient + 7) * (k + 1)^2) := ha
    omega
  · simpa only [program, C1, header, S1] using hrun

#print axioms physical_header_and_prepend

end CurrentAdditive.GaussWorkListHeaderJoin
