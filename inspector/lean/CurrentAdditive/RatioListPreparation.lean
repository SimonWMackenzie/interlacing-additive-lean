import CurrentAdditive.GaussRowCount
import CurrentAdditive.MinimumRatioCallbackLayout
import EthInapproximability.CurrentPaper.SourceFieldWriter

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
noncomputable section
namespace CurrentAdditive.RatioListPreparation
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext

theorem count_stacks : GaussRowCount.machine.stackCount = 17 := by
  simp [GaussRowCount.machine,GaussRowCount.oneMachine,GaussHeaderStrip.machine,
    BitMachineComposition.composition,BitMachineComposition.Stack,
    SourceListMachineOuter.machine,ofFinite,
    SourceListMachineOuter.Stack,SourceListMachineItem.Stack]

theorem header_stacks : SourceFieldWriter.unaryFieldMachine.stackCount ≤ 17 := by
  simp [SourceFieldWriter.unaryFieldMachine,SourceFieldWriter.fieldMachine,
    BitMachineComposition.composition,BitMachineComposition.Stack,UnaryBinaryEncoding.machine,
    BinarySuccessorMachine.machine,ofFinite]

def localSlot : Fin 17 → Fin 32 := ![0,1,2,3,4,5,6,7,11,14,15,16,17,18,19,20,21]
def reserve : Fin 17 ↪ Stack where
  toFun i := low (localSlot i)
  inj' := by
    intro a b h
    have hv := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> simp_all [localSlot,low]

theorem reserved_ne (i : Fin 17) (j : Fin 32)
    (hj : j = 8 ∨ j = 9 ∨ j = 13 ∨ j = 31) : reserve i ≠ low j := by
  intro he
  have hv := congrArg Fin.val he
  rcases hj with rfl | rfl | rfl | rfl <;>
    fin_cases i <;> norm_num [reserve,localSlot,low] at hv

def slots (M : BitMachine.Machine) (hm : M.stackCount ≤ 17)
    (s t : Fin 32) (hst : s ≠ t)
    (hs : s = 8 ∨ s = 13) (ht : t = 9 ∨ t = 13) :
    MachineInvokeCore.Slots M extraCount where
  machine :=
    { toFun := fun i => reserve ⟨i.val,Nat.lt_of_lt_of_le i.isLt hm⟩
      inj' := by
        intro a b he
        apply Fin.ext
        exact congrArg (fun k : Fin 17 => k.val) (reserve.injective he) }
  source := low s
  target := low t
  scratch := low 31
  source_target := by
    intro he; apply hst; apply Fin.ext; exact congrArg (fun k : Stack => k.val) he
  source_scratch := by
    rcases hs with rfl | rfl <;> simp [low,Fin.ext_iff]
  target_scratch := by
    rcases ht with rfl | rfl <;> simp [low,Fin.ext_iff]
  source_machine := by
    intro i he
    exact reserved_ne _ s (hs.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr (Or.inl h)))) he.symm
  target_machine := by
    intro i he
    exact reserved_ne _ t (ht.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h)))) he.symm
  scratch_machine := by
    intro i he
    exact reserved_ne _ 31 (Or.inr (Or.inr (Or.inr rfl))) he.symm

def countSlots := slots GaussRowCount.machine (by rw [count_stacks])
  8 13 (by decide) (Or.inl rfl) (Or.inr rfl)
def headerSlots := slots SourceFieldWriter.unaryFieldMachine header_stacks
  13 9 (by decide) (Or.inr rfl) (Or.inl rfl)
abbrev CountLabel := MachineInvokeFull.LabelFull GaussRowCount.machine
abbrev CountControl := MachineInvokeFull.ControlFull GaussRowCount.machine
abbrev HeaderLabel := MachineInvokeFull.LabelFull SourceFieldWriter.unaryFieldMachine
abbrev HeaderControl := MachineInvokeFull.ControlFull SourceFieldWriter.unaryFieldMachine
def countProgram := MachineInvokeFull.program countSlots
def headerProgram := MachineInvokeFull.program headerSlots
abbrev Label := BitMachineRawSequence.Label CountLabel HeaderLabel
abbrev Control := CountControl × HeaderControl
def program := BitMachineRawSequence.program countProgram headerProgram
  (MachineInvokeFull.start headerSlots) (MachineInvokeFull.control countSlots)
  (MachineInvokeFull.control headerSlots)
def start : Label := BitMachineRawSequence.leftLabel (MachineInvokeFull.start countSlots)
def control : Control := (MachineInvokeFull.control countSlots,MachineInvokeFull.control headerSlots)
def clock (xs : List (List Bool)) : Nat :=
  MachineInvokeFull.uniformBound GaussRowCount.machine (SourceListEncoding.encode xs)
    (GaussRowCount.polynomialClock (SourceListEncoding.encode xs).length) +
  MachineInvokeFull.uniformBound SourceFieldWriter.unaryFieldMachine
    (List.replicate xs.length true)
    ((UnaryBinaryEncoding.coefficient+10)*(xs.length+1)^2)+1

/-- The source list supplies its own count. Both the unary loop fuel and
the output header are physically produced; no count is an input premise. -/
theorem outputs (S : Bank) (xs : List (List Bool))
    (hsource : S (low 8) = SourceListEncoding.encode xs)
    (h9 : S (low 9) = []) (h13 : S (low 13) = [])
    (h31 : S (low 31) = []) (hblank : ∀ i,S (reserve i) = []) :
    ∃ t ≤ clock xs,
      ((advance program)^[t]) (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,control,Function.update
        (Function.update S (low 13) (List.replicate xs.length true))
        (low 9) (EncodedCommunication.natField xs.length)⟩ := by
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he; apply h; apply Fin.ext; exact congrArg (fun k : Stack => k.val) he
  let S1 := Function.update S (low 13) (List.replicate xs.length true)
  obtain ⟨a,ha,hrA⟩ := MachineInvokeFull.invoke_run_uniform countSlots S
    (SourceListEncoding.encode xs) (List.replicate xs.length true)
    (GaussRowCount.polynomialClock (SourceListEncoding.encode xs).length)
    hsource h13 h31 (by intro i; exact hblank _) (GaussRowCount.outputs_polynomial xs)
  have h9S1 : S1 (low 9) = [] := by
    simp [S1,Function.update_of_ne,hne 9 13 (by decide),h9]
  have h31S1 : S1 (low 31) = [] := by
    simp [S1,Function.update_of_ne,hne 31 13 (by decide),h31]
  have hblankS1 : ∀ i,S1 (headerSlots.machine i) = [] := by
    intro i
    change S1 (reserve _) = []
    dsimp only [S1]
    rw [Function.update_of_ne (reserved_ne _ 13 (Or.inr (Or.inr (Or.inl rfl))))]
    exact hblank _
  obtain ⟨b,hb,hrB⟩ := MachineInvokeFull.invoke_run_uniform headerSlots S1
    (List.replicate xs.length true) (EncodedCommunication.natField xs.length)
    ((UnaryBinaryEncoding.coefficient+10)*(xs.length+1)^2)
    (by simp [headerSlots,slots,S1]) h9S1 h31S1 hblankS1
    (by simpa using SourceFieldWriter.unary_field_outputs (List.replicate xs.length true))
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs countProgram headerProgram
    (MachineInvokeFull.start countSlots) (MachineInvokeFull.start headerSlots)
    (MachineInvokeFull.control countSlots) (MachineInvokeFull.control countSlots)
    (MachineInvokeFull.control headerSlots) (MachineInvokeFull.control headerSlots)
    S S1 _ a b hrA hrB
  exact ⟨t,by unfold clock; omega,by simpa only [program,start,control] using hr⟩

#print axioms outputs
end CurrentAdditive.RatioListPreparation
