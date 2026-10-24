import CurrentAdditive.GaussWorkListFuelCopy
import CurrentAdditive.GaussWorkItemAccumulator

/-! A physical count header from the retained unary source width. -/

namespace CurrentAdditive.GaussWorkListHeader

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

private noncomputable abbrev W := SourceListMachineWriter.framingMachine false
abbrev Bank := GaussWorkListFuel.Bank

private theorem eight_stacks : W.stackCount = 8 := rfl

noncomputable def embedded (i : Fin W.stackCount) : Bank :=
  ⟨16 + i.val, by
    have hi : i.val < 8 := by simpa only [eight_stacks] using i.isLt
    omega⟩

theorem embedded_injective : Function.Injective embedded := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [embedded] at hv
  omega

noncomputable def slots : MachineInvokeCore.Slots W
    (GaussStateMatrixContext.Sel.stackCount + GaussStateMatrixContext.Proj.stackCount) where
  machine := ⟨embedded, embedded_injective⟩
  source := ⟨3, by omega⟩
  target := ⟨13, by omega⟩
  scratch := ⟨14, by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega
  target_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega
  scratch_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega

noncomputable def program := MachineInvokeFull.program slots

theorem physical_header (S : Bank → List Bool) (k : Nat)
    (hwidth : S ⟨3, by omega⟩ = List.replicate k true)
    (h13 : S ⟨13, by omega⟩ = [])
    (h14 : S ⟨14, by omega⟩ = [])
    (hblank : ∀ i, S (slots.machine i) = []) :
    ∃ t ≤ MachineInvokeFull.uniformBound W (List.replicate k true)
        ((UnaryBinaryEncoding.coefficient + 7) * (k + 1)^2),
      ((advance program)^[t])
        (⟨some (MachineInvokeFull.start slots),
          MachineInvokeFull.control slots, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, MachineInvokeFull.control slots,
          Function.update S ⟨13, by omega⟩
            (SourceListMachineWriter.result false (List.replicate k true))⟩ := by
  simpa only [program, List.length_replicate] using
    MachineInvokeFull.invoke_run_uniform slots S (List.replicate k true)
      (SourceListMachineWriter.result false (List.replicate k true))
      ((UnaryBinaryEncoding.coefficient + 7) * (k + 1)^2)
      hwidth h13 h14 hblank
      (by simpa only [List.length_replicate] using
        SourceListMachineWriter.outputs false (List.replicate k true))

#print axioms physical_header

end CurrentAdditive.GaussWorkListHeader
