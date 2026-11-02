import CurrentAdditive.GaussWorkItemFrameContext
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Physically prepend one framed item to the accumulating work-list fields.
The source item is retained and the copy scratch is cleared. -/

namespace CurrentAdditive.GaussWorkItemAccumulator

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open BitMachineStackEmbedding

abbrev Bank := GaussWorkItemFrameContext.Bank

def slots : Fin 3 ↪ Bank :=
  ⟨![⟨13, by omega⟩, ⟨24, by omega⟩, ⟨15, by omega⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def program (l : BitMachineCopy.Label) :=
  stackStmt slots (BitMachineCopy.program l)

theorem physical_prepend (S : Bank → List Bool) (item old : List Bool)
    (hitem : S ⟨13, by omega⟩ = item)
    (hold : S ⟨24, by omega⟩ = old)
    (hscratch : S ⟨15, by omega⟩ = []) :
    ((advance program)^[2 * item.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, none, Function.update S ⟨24, by omega⟩ (item ++ old)⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none item old []
  have hbank : bank slots S c.stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [slots, c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hitem, hold, hscratch]
  have hstart : stackCfg slots S c =
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) := by
    change (⟨c.l, c.var, bank slots S c.stk⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _) = _
    rw [hbank]
    rfl
  have hrun := BitMachineStackRun.run slots S BitMachineCopy.program c
    (2 * item.length + 2)
  change ((advance program)^[2 * item.length + 2]) (stackCfg slots S c) =
    stackCfg slots S (BitMachineCopy.run (2 * item.length + 2) c) at hrun
  rw [hstart, BitMachineCopy.run_correct] at hrun
  have hfinal :
      (BitMachineCopy.cfg none none item (item ++ old) []).stk =
        Function.update c.stk 1 (item ++ old) := by
    funext i
    fin_cases i <;> rfl
  rw [show stackCfg slots S
      (BitMachineCopy.cfg none none item (item ++ old) []) =
      (⟨none, none,
        bank slots S (BitMachineCopy.cfg none none item (item ++ old) []).stk⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) from rfl,
    hfinal, bank_update] at hrun
  rw [hbank] at hrun
  simpa only [slots] using hrun

#print axioms physical_prepend

end CurrentAdditive.GaussWorkItemAccumulator
