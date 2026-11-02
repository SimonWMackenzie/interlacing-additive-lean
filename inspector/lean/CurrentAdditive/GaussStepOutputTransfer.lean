import CurrentAdditive.GaussSearchGridInvoke
import EthInapproximability.CurrentPaper.BitMachineClearBank

namespace CurrentAdditive.GaussStepOutputTransfer
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low)

inductive ClearLabel where | scan | done deriving DecidableEq,Fintype
abbrev ClearControl := Unit × Option Bool
def clearProgram : ClearLabel → TM2.Stmt (fun _ : Bank => Bool) ClearLabel ClearControl
  | .scan => BitMachineClearBank.clearStep (low 62) .scan .done
  | .done => .halt

theorem physical_clear (S : Bank → List Bool) :
    ((advance clearProgram)^[(S (low 62)).length+2])
      (⟨some .scan,((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) ClearLabel ClearControl)=
      ⟨none,((),none),Function.update S (low 62) []⟩ := by
  have h := BitMachineClearBank.clear_one_run clearProgram (low 62) .scan .done rfl () S
  rw [show (S (low 62)).length+2=((S (low 62)).length+1)+1 by omega,
    Function.iterate_succ_apply',h]
  rfl

def copyProgram := SourceClausePreservingBroadcast.program (low 14) (low 63) [low 62]
def program := BitMachineRawSequence.program clearProgram copyProgram .scan ((),none) ((),none)
abbrev Label := BitMachineRawSequence.Label ClearLabel SourceClausePreservingBroadcast.Label
abbrev Control := BitMachineRawSequence.Control ClearControl (Unit × Option Bool)
def start : Label := BitMachineRawSequence.leftLabel .scan
def control : Control := (((),none),((),none))
def clock (S : Bank → List Bool) : Nat := (S (low 62)).length+2*(S (low 14)).length+6

theorem physical_transfer (S : Bank → List Bool) (h63 : S (low 63)=[]) :
    ∃ t≤clock S,((advance program)^[t])
      (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control)=
      ⟨none,control,Function.update S (low 62) (S (low 14))⟩ := by
  let R := Function.update S (low 62) []
  have hsource : R (low 14)=S (low 14) := by simp [R,GaussSearchGridInvoke.low]
  have hscratch : R (low 63)=[] := by simpa [R,GaussSearchGridInvoke.low] using h63
  have hcopy := SourceClausePreservingBroadcast.run_halt (low 14) (low 63) [low 62]
    (by intro h; have hv:=congrArg Fin.val h; change 14=63 at hv; omega)
    (by simp) (by simp [GaussSearchGridInvoke.low]) (by simp [GaussSearchGridInvoke.low])
    (S (low 14)) R hsource hscratch
  have hfinal : SourceClausePreservingBroadcast.result (low 14) (low 63) [low 62]
      (S (low 14)) R=Function.update S (low 62) (S (low 14)) := by
    funext z
    by_cases h14 : z=low 14
    · subst z
      rw [SourceClausePreservingBroadcast.source_restored _ _ _
        (by simp [GaussSearchGridInvoke.low])]
      simp [GaussSearchGridInvoke.low]
    · by_cases h63' : z=low 63
      · subst z
        rw [SourceClausePreservingBroadcast.temp_empty]
        simpa [GaussSearchGridInvoke.low] using h63.symm
      · by_cases h62 : z=low 62
        · subst z
          rw [SourceClausePreservingBroadcast.target_written _ _ _
            (by simp [GaussSearchGridInvoke.low]) (by simp [GaussSearchGridInvoke.low])
            (by simp [GaussSearchGridInvoke.low]) _ _ _ (by simp)]
          simp [R]
        · rw [SourceClausePreservingBroadcast.other_preserved _ _ _ _ _ _ h14 h63' (by simpa using h62)]
          simp [R,h62]
  rw [hfinal] at hcopy
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs clearProgram copyProgram .scan .scan
    ((),none) ((),none) ((),none) ((),none) S R
    (Function.update S (low 62) (S (low 14)))
    ((S (low 62)).length+2) (2*(S (low 14)).length+3) (physical_clear S) hcopy
  exact ⟨t,by unfold clock; omega,he⟩

#print axioms physical_transfer
end
end CurrentAdditive.GaussStepOutputTransfer
