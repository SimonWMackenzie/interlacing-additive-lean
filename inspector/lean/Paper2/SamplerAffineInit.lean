import Paper2.SamplerAffineSource
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.BitMachineRawSequence

set_option maxHeartbeats 3000000

namespace Paper2.SamplerAffineInit

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineRawSequence

abbrev Stack := SamplerAffineRound.Stack

def copyIndex : Fin 3 ↪ Stack where
  toFun := ![5,13,20]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp at h ⊢

def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copyIndex
def oneProgram := SourceClauseFixedUnary.program (14 : Stack) 1
abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label
  (SourceClauseFixedUnary.Label 1)
abbrev Control := Option Bool × Unit
def program := BitMachineRawSequence.program copyProgram oneProgram
  (0 : SourceClauseFixedUnary.Label 1) none ()

def finalBank (S : Stack → List Bool) (p : Nat) : Stack → List Bool :=
  Function.update (Function.update S 13 (List.replicate p true)) 14 [true]

theorem run (S : Stack → List Bool) (p : Nat)
    (hp : S 5 = List.replicate p true)
    (h13 : S 13 = []) (h14 : S 14 = []) (h20 : S 20 = []) :
    ∃ t ≤ 2*p+5,
      ((advance program)^[t])
        (⟨some (.inl .scan), (none,()), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, (none,()), finalBank S p⟩ := by
  have hcopy := MatrixStage4ScalarPreparationOps.copy_run copyIndex S
    (by simpa only [copyIndex] using h20)
  have hcopy' :
      ((advance copyProgram)^[2*p+2])
        (⟨some .scan, none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update S 13 (List.replicate p true)⟩ := by
    have hsource : S (copyIndex 0) = List.replicate p true := hp
    have htarget : S (copyIndex 1) = [] := h13
    rw [hsource, List.length_replicate] at hcopy
    rw [htarget, List.append_nil] at hcopy
    simpa only [copyProgram, copyIndex] using hcopy
  let T := Function.update S 13 (List.replicate p true)
  have h14T : T 14 = [] := by
    simpa only [T, Function.update_of_ne (by decide : (14 : Stack) ≠ 13)] using h14
  have hone := SourceClauseFixedUnary.run (14 : Stack) T 1 h14T
  have hone' : ((advance oneProgram)^[2])
      (⟨some (0 : SourceClauseFixedUnary.Label 1), (), T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (), finalBank S p⟩ := by
    simpa only [oneProgram, finalBank, T] using hone
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    copyProgram oneProgram .scan (0 : SourceClauseFixedUnary.Label 1)
    none none () () S T (finalBank S p) (2*p+2) 2 hcopy' hone'
  exact ⟨t, by omega, by simpa only [program] using hr⟩

#print axioms run

end Paper2.SamplerAffineInit
