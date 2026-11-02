import CurrentAdditive.GaussWorkItemCallback
import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-! A physical nested-length wrapper for one already serialized work item.
The fixed framing machine is invoked in disposable ambient banks; its output
is the exact V2 item field.  Every source/context bank is preserved. -/

namespace CurrentAdditive.GaussWorkItemFrameContext

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

private noncomputable abbrev W := SourceListMachineWriter.framingMachine true
abbrev Bank := GaussWorkItemCallback.Bank

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
  source := ⟨8, by omega⟩
  target := ⟨13, by omega⟩
  scratch := ⟨14, by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega
  target_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega
  scratch_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega

noncomputable def program := MachineInvokeFull.program slots

theorem physical_field (S : Bank → List Bool) (raw : List Bool)
    (hsource : S ⟨8, by omega⟩ = raw)
    (htarget : S ⟨13, by omega⟩ = [])
    (hscratch : S ⟨14, by omega⟩ = [])
    (hblank : ∀ i, S (slots.machine i) = []) :
    ∃ u ≤ MachineInvokeFull.uniformBound W raw
        ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2),
      ((advance program)^[u])
        (⟨some (MachineInvokeFull.start slots),
          MachineInvokeFull.control slots, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, MachineInvokeFull.control slots,
          Function.update S ⟨13, by omega⟩
            (SourceListMachineWriter.result true raw)⟩ := by
  exact MachineInvokeFull.invoke_run_uniform slots S raw
    (SourceListMachineWriter.result true raw)
    ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2)
    hsource htarget hscratch hblank
    (SourceListMachineWriter.outputs true raw)

#print axioms physical_field

end CurrentAdditive.GaussWorkItemFrameContext
