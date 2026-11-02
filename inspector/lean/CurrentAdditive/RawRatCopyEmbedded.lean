import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Tactic

/-! A checked ambient-bank form of the source-preserving physical copy. -/
namespace CurrentAdditive.RawRatCopyEmbedded

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding

variable {K : Type*} [DecidableEq K]

def program (ι : Fin 3 ↪ K) : BitMachineCopy.Label →
    TM2.Stmt (fun _ : K => Bool) BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt ι (BitMachineCopy.program l)

theorem local_bank (ι : Fin 3 ↪ K) (S : K → List Bool)
    (htarget : S (ι 1) = []) (htemp : S (ι 2) = []) :
    BitMachineStackEmbedding.bank ι S
      (BitMachineCopy.stackContents (S (ι 0)) [] []) = S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp [BitMachineCopy.stackContents, htarget, htemp]

theorem final_bank (ι : Fin 3 ↪ K) (S : K → List Bool)
    (htarget : S (ι 1) = []) (htemp : S (ι 2) = []) :
    BitMachineStackEmbedding.bank ι S
      (BitMachineCopy.stackContents (S (ι 0)) (S (ι 0)) []) =
    Function.update S (ι 1) (S (ι 0)) := by
  funext k
  by_cases hk : ∃ j : Fin 3, ι j = k
  · obtain ⟨j, rfl⟩ := hk
    fin_cases j <;>
      simp [BitMachineStackEmbedding.bank_at,
        BitMachineCopy.stackContents, Function.update_apply,
        htarget, htemp, ι.injective]
  · have hne : k ≠ ι 1 := by
      intro h; exact hk ⟨1, h.symm⟩
    rw [BitMachineStackEmbedding.bank_outside ι S _ k hk]
    simp [Function.update_of_ne hne]

theorem run_correct (ι : Fin 3 ↪ K) (S : K → List Bool)
    (htarget : S (ι 1) = []) (htemp : S (ι 2) = []) :
    ((advance (program ι))^[2 * (S (ι 0)).length + 2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : K => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S (ι 1) (S (ι 0))⟩ := by
  have h := BitMachineStackRun.run ι S BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none (S (ι 0)) [] [])
    (2 * (S (ι 0)).length + 2)
  change ((advance (program ι))^[2 * (S (ι 0)).length + 2])
      (BitMachineStackEmbedding.stackCfg ι S
        (BitMachineCopy.cfg (some .scan) none (S (ι 0)) [] [])) =
      BitMachineStackEmbedding.stackCfg ι S
        (BitMachineCopy.run (2 * (S (ι 0)).length + 2)
          (BitMachineCopy.cfg (some .scan) none (S (ι 0)) [] [])) at h
  rw [BitMachineCopy.run_correct] at h
  simp only [List.append_nil] at h
  change ((advance (program ι))^[2 * (S (ι 0)).length + 2])
      (⟨some BitMachineCopy.Label.scan, none,
        BitMachineStackEmbedding.bank ι S
          (BitMachineCopy.stackContents (S (ι 0)) [] [])⟩ :
        TM2.Cfg (fun _ : K => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, BitMachineStackEmbedding.bank ι S
        (BitMachineCopy.stackContents (S (ι 0)) (S (ι 0)) [])⟩ at h
  rw [local_bank ι S htarget htemp,
    final_bank ι S htarget htemp] at h
  exact h

end CurrentAdditive.RawRatCopyEmbedded
