import CurrentAdditive.FeatureMapPairLoader
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed
import CurrentAdditive.FeatureMapHeaders

/-! An actual fixed item evaluator is invoked on its physically loaded
context/item packet. Optional V2 item framing is itself a compiled machine.
All copy, callback, output-copy and reset transitions are charged. -/

namespace CurrentAdditive.FeatureMapInvoke

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
open CurrentAdditive.FeatureMapPairLoader

noncomputable section

def evaluator (M : BitMachine.Machine) (framed : Bool) : BitMachine.Machine :=
 if framed then SourceListMachineOuterFramed.itemMachine M else M

def piece (framed : Bool) (output : List Bool) : List Bool :=
 if framed then EncodedCommunication.natField output.length ++ output else output

def itemTime (framed : Bool) (output : List Bool) (T : Nat) : Nat :=
 if framed then T + 2 * output.length + 2 +
   (UnaryBinaryEncoding.coefficient + 7) * (output.length + 1)^2 else T

theorem evaluator_outputs (M : BitMachine.Machine) (framed : Bool)
 (input output : List Bool) (T : Nat) (h : M.OutputsWithin input output T) :
 (evaluator M framed).OutputsWithin input (piece framed output)
   (itemTime framed output T) := by
 cases framed
 · exact h
 · simpa [evaluator, piece, itemTime, SourceListMachineOuterFramed.framedOutput,
     SourceListMachineOuterFramed.framedBound] using
     SourceListMachineOuterFramed.framed_item M (fun _ => output) (fun _ => T) input h

variable (M : BitMachine.Machine) (framed : Bool)

abbrev count := (evaluator M framed).stackCount +
 FeatureMapListCount.machine.stackCount + (FeatureMapHeaders.machine framed).stackCount
abbrev Bank := Stack (count M framed)

def machineSlots : Fin (evaluator M framed).stackCount ↪ Bank M framed where
 toFun i := ⟨32 + i.val, by have := i.isLt; dsimp [count]; omega⟩
 inj' := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp only at hh
  omega

def slots : MachineInvokeCore.Slots (evaluator M framed) (count M framed) where
 machine := machineSlots M framed
 source := low 4
 target := low 5
 scratch := low 14
 source_target := by simp [low, Fin.ext_iff]
 source_scratch := by simp [low, Fin.ext_iff]
 target_scratch := by simp [low, Fin.ext_iff]
 source_machine := by intro i h; have hh := congrArg Fin.val h; change 4 = 32 + i.val at hh; omega
 target_machine := by intro i h; have hh := congrArg Fin.val h; change 5 = 32 + i.val at hh; omega
 scratch_machine := by intro i h; have hh := congrArg Fin.val h; change 14 = 32 + i.val at hh; omega

def invokeProgram := MachineInvokeFull.program (slots M framed)

def budget (input output : List Bool) (T : Nat) : Nat :=
 MachineInvokeFull.uniformBound (evaluator M framed) input
   (itemTime framed output T)

theorem invoke_run (S : Bank M framed → List Bool)
 (input output : List Bool) (T : Nat)
 (h4 : S (low 4) = input) (h5 : S (low 5) = [])
 (h14 : S (low 14) = [])
 (hblank : ∀ i, S (machineSlots M framed i) = [])
 (hM : M.OutputsWithin input output T) :
 ∃ t ≤ budget M framed input output T,
 ((advance (invokeProgram M framed))^[t])
   (⟨some (MachineInvokeFull.start (slots M framed)),
     MachineInvokeFull.control (slots M framed), S⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none, MachineInvokeFull.control (slots M framed),
     Function.update S (low 5) (piece framed output)⟩ := by
 exact MachineInvokeFull.invoke_run_uniform (slots M framed) S input
   (piece framed output) (itemTime framed output T) h4 h5 h14 hblank
   (evaluator_outputs M framed input output T hM)

def loadedProgram := BitMachineRawSequence.program
 (FeatureMapPairLoader.program (N := count M framed)) (invokeProgram M framed)
 (MachineInvokeFull.start (slots M framed)) (none,none)
 (MachineInvokeFull.control (slots M framed))

abbrev LoadedLabel := BitMachineRawSequence.Label
 (BitMachineRawSequence.Label BitMachineCopy.Label (BitMachineBankSerialize.Label 2))
 (MachineInvokeFull.LabelFull (evaluator M framed))
abbrev LoadedControl := (Option Bool × Option Bool) ×
 MachineInvokeFull.ControlFull (evaluator M framed)
def loadedStart : LoadedLabel M framed :=
 BitMachineRawSequence.leftLabel FeatureMapPairLoader.start
def loadedControl : LoadedControl M framed :=
 ((none,none), MachineInvokeFull.control (slots M framed))

def loadedBudget (context item output : List Bool) (T : Nat) : Nat :=
 ((2 * context.length + 2) + (2 * (packet context item).length + 2) + 1) +
   budget M framed (packet context item) output T + 1

theorem loaded_run (S : Bank M framed → List Bool) (context item output : List Bool)
 (T : Nat)
 (h12 : S (low 12) = context) (h6 : S (low 6) = item)
 (h7 : S (low 7) = []) (h4 : S (low 4) = [])
 (h5 : S (low 5) = []) (h11 : S (low 11) = []) (h14 : S (low 14) = [])
 (hblank : ∀ i, S (machineSlots M framed i) = [])
 (hM : M.OutputsWithin (packet context item) output T) :
 ∃ t ≤ loadedBudget M framed context item output T,
 ((advance (loadedProgram M framed))^[t])
   (⟨some (loadedStart M framed), loadedControl M framed, S⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none, loadedControl M framed,
     Function.update (prepared S (packet context item)) (low 5) (piece framed output)⟩ := by
 obtain ⟨a,ha,hr⟩ := load_run S context item h12 h6 h7 h4 h11 h14
 have h5' : prepared S (packet context item) (low 5) = [] := by
   simpa [prepared, low, Fin.ext_iff] using h5
 have h14' : prepared S (packet context item) (low 14) = [] := by
   simpa [prepared, low, Fin.ext_iff] using h14
 have hblank' : ∀ i, prepared S (packet context item) (machineSlots M framed i) = [] := by
   intro i
   have h7n : machineSlots M framed i ≠ low 7 := by intro h; have hh := congrArg Fin.val h; change 32+i.val=7 at hh;omega
   have h6n : machineSlots M framed i ≠ low 6 := by intro h; have hh := congrArg Fin.val h; change 32+i.val=6 at hh;omega
   have h4n : machineSlots M framed i ≠ low 4 := by intro h; have hh := congrArg Fin.val h; change 32+i.val=4 at hh;omega
   simp [prepared, Function.update_of_ne, h7n, h6n, h4n, hblank]
 obtain ⟨b,hb,hs⟩ := invoke_run M framed (prepared S (packet context item))
   (packet context item) output T (by simp [prepared]) h5' h14' hblank' hM
 obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
   (FeatureMapPairLoader.program (N := count M framed)) (invokeProgram M framed)
   FeatureMapPairLoader.start (MachineInvokeFull.start (slots M framed))
   (none,none) (none,none) (MachineInvokeFull.control (slots M framed))
   (MachineInvokeFull.control (slots M framed)) S _ _ a b hr hs
 exact ⟨t, by dsimp [loadedBudget];omega, he⟩

#print axioms evaluator_outputs
#print axioms invoke_run
#print axioms loaded_run

end
end CurrentAdditive.FeatureMapInvoke
