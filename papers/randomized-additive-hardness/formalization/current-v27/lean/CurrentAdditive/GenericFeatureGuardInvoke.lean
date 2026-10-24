import CurrentAdditive.GenericFeatureDepthPacketGuard
import CurrentAdditive.FeatureEligibleDescriptor96
import CurrentAdditive.MachineInvokeFull

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CurrentAdditive.GenericFeatureGuardInvoke
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

def M (D : Nat) := GenericFeatureDepthPacketGuard.machine D
theorem stack_count (D : Nat) : (M D).stackCount = 8 := GenericFeatureDepthPacketGuard.stack_count D

def slots (D : Nat) : MachineInvokeCore.Slots (M D) 64 where
  machine := ⟨fun i => ⟨19 + i.val, by
      have hi : i.val < 8 := by simpa only [stack_count] using i.isLt
      omega⟩, by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp at hv
    omega⟩
  source := 6
  target := 27
  scratch := 28
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro k h; have hv := congrArg Fin.val h; simp at hv; omega
  target_machine := by
    intro k h
    have hv := congrArg Fin.val h
    have hk : k.val < 8 := by simpa only [stack_count] using k.isLt
    simp at hv
    omega
  scratch_machine := by
    intro k h
    have hv := congrArg Fin.val h
    have hk : k.val < 8 := by simpa only [stack_count] using k.isLt
    simp at hv
    omega

def program (D : Nat) := MachineInvokeFull.program (slots D)
def start (D : Nat) := MachineInvokeFull.start (slots D)
def control (D : Nat) := MachineInvokeFull.control (slots D)
def clock (D : Nat) (c : List (Nat × Nat)) : Nat :=
  MachineInvokeFull.uniformBound (M D) (CylinderFeatureCodec.encodeFeature c)
    (8 * ((CylinderFeatureCodec.encodeFeature c).length + 1) + 10)

theorem physical_feature_linear (D : Nat) (c : List (Nat × Nat)) :
    (M D).OutputsWithin (CylinderFeatureCodec.encodeFeature c) [decide (c.length < D)]
      (8 * ((CylinderFeatureCodec.encodeFeature c).length + 1) + 10) :=
  GenericFeatureDepthPacketGuard.physical_feature D c

theorem run (D : Nat) (S : Fin 96 → List Bool) (c : List (Nat × Nat))
    (h6 : S 6 = CylinderFeatureCodec.encodeFeature c)
    (hblank : ∀ k : Fin 96, 19 ≤ k.val → k.val ≤ 28 → S k = []) :
    ∃ t ≤ clock D c,
      ((advance (program D))^[t])
        (⟨some (start D), control D, S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none, control D, Function.update S 27 [decide (c.length < D)]⟩ := by
  apply MachineInvokeFull.invoke_run_uniform (slots D) S
    (CylinderFeatureCodec.encodeFeature c) [decide (c.length < D)]
    (8 * ((CylinderFeatureCodec.encodeFeature c).length + 1) + 10) h6
    (hblank 27 (by decide) (by decide)) (hblank 28 (by decide) (by decide))
    (fun k => hblank _ (by simp [slots]) (by
      have hk : k.val < 8 := by simpa only [stack_count] using k.isLt
      simp [slots]
      omega)) (physical_feature_linear D c)

#print axioms run
end CurrentAdditive.GenericFeatureGuardInvoke
