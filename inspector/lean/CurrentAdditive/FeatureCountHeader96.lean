import CurrentAdditive.FeatureOldDescriptorSemantics96
import CurrentAdditive.MachineInvokeFull

/-! A retained unary feature count is physically converted to the canonical
count header. The source, finite-machine invocation and cleanup are charged. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeatureCountHeader96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev M := SourceListMachineWriter.framingMachine false
theorem stack_count : M.stackCount=8 := by rfl

def slots : MachineInvokeCore.Slots M 64 where
  machine := ⟨fun i => ⟨32+i.val,by have hi:=i.isLt; change i.val<8 at hi; omega⟩,
    by intro i j h; apply Fin.ext; have hv:=congrArg Fin.val h; simp at hv; omega⟩
  source := 12
  target := 16
  scratch := 19
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro k h; have hv:=congrArg Fin.val h; simp at hv; omega
  target_machine := by intro k h; have hv:=congrArg Fin.val h; simp at hv; omega
  scratch_machine := by intro k h; have hv:=congrArg Fin.val h; simp at hv; omega

def program := MachineInvokeFull.program slots
def start := MachineInvokeFull.start slots
def control := MachineInvokeFull.control slots
def clock (count : List Bool) := MachineInvokeFull.uniformBound M count
  ((UnaryBinaryEncoding.coefficient+7)*(count.length+1)^2)

theorem run (S : Fin 96 → List Bool) (count : List Bool)
    (h12 : S 12=count) (h16 : S 16=[]) (h19 : S 19=[])
    (hhigh : ∀ k : Fin 96, 32≤k.val → S k=[]) :
    ∃ t≤clock count,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,Function.update S 16 (EncodedCommunication.natField count.length)⟩ := by
  apply MachineInvokeFull.invoke_run_uniform slots S count
    (EncodedCommunication.natField count.length)
    ((UnaryBinaryEncoding.coefficient+7)*(count.length+1)^2) h12 h16 h19
    (fun k => hhigh _ (by simp [slots]))
  simpa [SourceListMachineWriter.result] using SourceListMachineWriter.outputs false count

#print axioms run
end CurrentAdditive.FeatureCountHeader96
