import CurrentAdditive.RatioBranchReset
import CurrentAdditive.RatioMinimumMachine
import CurrentAdditive.RatioRequestUpdatePolynomial
import EthInapproximability.CurrentPaper.BitMachineStackRun

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioBranchLayout
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext

abbrev MinM := RatioMinimumMachine.machine
def N := RatioRequestUpdateRun.N+MinM.stackCount
abbrev BigStack := Fin (32+N)
abbrev BigBank := BigStack → List Bool
def wide : RatioRequestUpdateRun.WideStack ↪ BigStack where
  toFun i := ⟨i.val,by have hi := i.isLt; dsimp [N]; omega⟩
  inj' := by intro a b he; apply Fin.ext; exact congrArg (fun k : BigStack => k.val) he
def core : Stack ↪ BigStack where
  toFun i := wide (RatioRequestUpdateRun.embed i)
  inj' := by intro a b he; exact RatioRequestUpdateRun.embed.injective (wide.injective he)
def high : Fin MinM.stackCount ↪ BigStack where
  toFun i := ⟨32+RatioRequestUpdateRun.N+i.val,by have hi := i.isLt; dsimp [N]; omega⟩
  inj' := by
    intro a b he; apply Fin.ext
    have hv := congrArg (fun k : BigStack => k.val) he
    change 32+RatioRequestUpdateRun.N+a.val=32+RatioRequestUpdateRun.N+b.val at hv
    omega
def minSlots : MachineInvokeCore.Slots MinM N where
  machine := high
  source := core (low 9)
  target := core (low 25)
  scratch := core (low 31)
  source_target := by simp [core,wide,RatioRequestUpdateRun.embed,low,Fin.ext_iff]
  source_scratch := by simp [core,wide,RatioRequestUpdateRun.embed,low,Fin.ext_iff]
  target_scratch := by simp [core,wide,RatioRequestUpdateRun.embed,low,Fin.ext_iff]
  source_machine := by
    intro i he
    have hv := congrArg (fun k : BigStack => k.val) he
    change 9=32+RatioRequestUpdateRun.N+i.val at hv; omega
  target_machine := by
    intro i he
    have hv := congrArg (fun k : BigStack => k.val) he
    change 25=32+RatioRequestUpdateRun.N+i.val at hv; omega
  scratch_machine := by
    intro i he
    have hv := congrArg (fun k : BigStack => k.val) he
    change 31=32+RatioRequestUpdateRun.N+i.val at hv; omega

def frame (S : Bank) : BigBank := BitMachineStackEmbedding.bank core (fun _ => []) S
def frameWide (S : RatioRequestUpdateRun.WideBank) : BigBank :=
  BitMachineStackEmbedding.bank wide (fun _ => []) S

theorem frame_compat (S : Bank) : frameWide (RatioRequestUpdateRun.frame S) = frame S := by
  funext j
  by_cases hw : ∃ k,wide k=j
  · obtain ⟨k,rfl⟩ := hw
    rw [frameWide,BitMachineStackEmbedding.bank_at]
    by_cases hk : ∃ i,RatioRequestUpdateRun.embed i=k
    · obtain ⟨i,rfl⟩ := hk
      change RatioRequestUpdateRun.frame S (RatioRequestUpdateRun.embed i) = frame S (core i)
      rw [RatioRequestUpdateRun.frame,BitMachineStackEmbedding.bank_at,frame,
        BitMachineStackEmbedding.bank_at]
    · rw [RatioRequestUpdateRun.frame,BitMachineStackEmbedding.bank_outside _ _ _ k hk]
      symm
      apply BitMachineStackEmbedding.bank_outside
      intro he
      obtain ⟨i,hi⟩ := he
      apply hk
      exact ⟨i,wide.injective hi⟩
  · rw [frameWide,BitMachineStackEmbedding.bank_outside _ _ _ j hw]
    symm
    apply BitMachineStackEmbedding.bank_outside
    intro he
    obtain ⟨i,hi⟩ := he
    exact hw ⟨RatioRequestUpdateRun.embed i,hi⟩

theorem frame_update (S : Bank) (i : Stack) (word : List Bool) :
    frame (Function.update S i word) = Function.update (frame S) (core i) word :=
  BitMachineStackEmbedding.bank_update core _ S i word

def pairProgram l := BitMachineStackEmbedding.stackStmt core (RatioListFullRun.pairProgram l)
def minimumProgram := MachineInvokeFull.program minSlots
def resetProgram l := BitMachineStackEmbedding.stackStmt core (RatioBranchReset.program l)
def updateProgram l := BitMachineStackEmbedding.stackStmt wide (RatioRequestUpdateRun.program l)
abbrev L01 := BitMachineRawSequence.Label RatioListFullRun.PairLabel (MachineInvokeFull.LabelFull MinM)
def p01 := BitMachineRawSequence.program pairProgram minimumProgram
  (MachineInvokeFull.start minSlots) RatioListFullRun.pairFullControl (MachineInvokeFull.control minSlots)
def s01 : L01 := BitMachineRawSequence.leftLabel RatioListFullRun.pairFullStart
def c01 := (RatioListFullRun.pairFullControl,MachineInvokeFull.control minSlots)
abbrev L012 := BitMachineRawSequence.Label L01 RatioBranchReset.Label
def p012 := BitMachineRawSequence.program p01 resetProgram RatioBranchReset.start c01 RatioBranchReset.control
def s012 : L012 := BitMachineRawSequence.leftLabel s01
def c012 := (c01,RatioBranchReset.control)
abbrev Label := BitMachineRawSequence.Label L012 RatioRequestUpdateRun.Label
def program := BitMachineRawSequence.program p012 updateProgram RatioRequestUpdateRun.start
  c012 RatioRequestUpdateRun.control
def start : Label := BitMachineRawSequence.leftLabel s012
def control := (c012,RatioRequestUpdateRun.control)

#print axioms frame_compat
end CurrentAdditive.RatioBranchLayout
