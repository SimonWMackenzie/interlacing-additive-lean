import CurrentAdditive.FeatureEligibleDescriptor96
import CurrentAdditive.FeatureDepthPacketGuard
import CurrentAdditive.MachineInvokeFull

/-! The actual descriptor depth test embedded in the outer bank, with
source-preserving input/output copies and complete machine-bank cleanup. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeatureGuardInvoke96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev M := FeatureDepthPacketGuard.machine

theorem stack_count : M.stackCount=8 := by rfl

def slots : MachineInvokeCore.Slots M 64 where
  machine := ⟨fun i => ⟨19+i.val,by have := i.isLt; change i.val<8 at this; omega⟩,
    by intro i j h; apply Fin.ext; have hv:=congrArg Fin.val h; simp at hv; omega⟩
  source := 6
  target := 27
  scratch := 28
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro k h; have hv:=congrArg Fin.val h; simp at hv; omega
  target_machine := by intro k h; have hv:=congrArg Fin.val h; have hk:=k.isLt; change k.val<8 at hk; simp at hv; omega
  scratch_machine := by intro k h; have hv:=congrArg Fin.val h; have hk:=k.isLt; change k.val<8 at hk; simp at hv; omega

def program := MachineInvokeFull.program slots
def start := MachineInvokeFull.start slots
def control := MachineInvokeFull.control slots

def clock (c : List (Nat × Nat)) : Nat :=
  MachineInvokeFull.uniformBound M (CylinderFeatureCodec.encodeFeature c)
    (6*((CylinderFeatureCodec.encodeFeature c).length+1)+20)

theorem physical_feature_linear (c : List (Nat × Nat)) :
    M.OutputsWithin (CylinderFeatureCodec.encodeFeature c)
      [decide (c.length<8192)]
      (6*((CylinderFeatureCodec.encodeFeature c).length+1)+20) := by
  have h := FeatureDepthPacketGuard.physical_total_linear
    (CylinderFeatureCodec.encodeFeature c)
  rw [FeatureDepthPacketGuard.header_result_feature] at h
  have hsize : c.length.bits.length≤13 ↔ c.length<8192 := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
  simpa only [List.tail_cons,hsize] using h

theorem run (S : Fin 96 → List Bool) (c : List (Nat × Nat))
    (h6 : S 6=CylinderFeatureCodec.encodeFeature c)
    (hblank : ∀ k : Fin 96, 19≤k.val → k.val≤28 → S k=[]) :
    ∃ t≤clock c,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,Function.update S 27 [decide (c.length<8192)]⟩ := by
  apply MachineInvokeFull.invoke_run_uniform slots S
    (CylinderFeatureCodec.encodeFeature c) [decide (c.length<8192)]
    (6*((CylinderFeatureCodec.encodeFeature c).length+1)+20) h6
    (hblank 27 (by decide) (by decide))
    (hblank 28 (by decide) (by decide))
    (fun k => hblank _ (by simp [slots]) (by
      have hk:=k.isLt; change k.val<8 at hk; simp [slots]; omega))
    (physical_feature_linear c)

#print axioms run
end CurrentAdditive.FeatureGuardInvoke96
