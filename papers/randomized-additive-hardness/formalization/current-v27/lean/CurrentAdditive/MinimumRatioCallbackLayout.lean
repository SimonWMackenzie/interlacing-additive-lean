import CurrentAdditive.MinimumRatioStepSpec
import CurrentAdditive.MachineInvokeFull
import CurrentAdditive.StatefulListSchedulerRun

/-! Fixed ambient banks for the itemwise arithmetic callback.  All embedded
machine stacks live above bank 31, so the scheduler's persistent banks and the
callback's low scratch registers are disjoint by construction. -/

namespace CurrentAdditive.MinimumRatioCallbackLayout

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext

noncomputable def extraCount : Nat :=
  MinimumRatioPositiveMachine.machine.stackCount +
  RationalCanonicalCallback.quotientMachine.stackCount +
  RationalLess.machine.stackCount

abbrev Stack := Fin (32 + extraCount)
abbrev Bank := Stack → List Bool

noncomputable def low (k : Fin 32) : Stack := k.castAdd extraCount

noncomputable def high {M : BitMachine.Machine} (h : M.stackCount ≤ extraCount) :
    Fin M.stackCount ↪ Stack where
  toFun k := ⟨32 + k.val, by have := k.isLt; omega⟩
  inj' := by
    intro a b hEq
    apply Fin.ext
    have hv := congrArg Fin.val hEq
    simpa using Nat.add_left_cancel hv

noncomputable def slots (M : BitMachine.Machine) (h : M.stackCount ≤ extraCount)
    (s t : Fin 32) (hst : s ≠ t) (hs31 : s ≠ 31) (ht31 : t ≠ 31) :
    MachineInvokeCore.Slots M extraCount where
  machine := high h
  source := low s
  target := low t
  scratch := low 31
  source_target := by
    intro he
    apply hst
    apply Fin.ext
    simpa [low] using congrArg Fin.val he
  source_scratch := by
    intro he
    apply hs31
    apply Fin.ext
    simpa [low] using congrArg Fin.val he
  target_scratch := by
    intro he
    apply ht31
    apply Fin.ext
    simpa [low] using congrArg Fin.val he
  source_machine := by
    intro k he
    have hv := congrArg Fin.val he
    have hs := s.isLt
    simp [low, high] at hv
    omega
  target_machine := by
    intro k he
    have hv := congrArg Fin.val he
    have ht := t.isLt
    simp [low, high] at hv
    omega
  scratch_machine := by
    intro k he
    have hv := congrArg Fin.val he
    simp [low, high] at hv
    omega

noncomputable def positiveSlots :
    MachineInvokeCore.Slots MinimumRatioPositiveMachine.machine extraCount :=
  slots MinimumRatioPositiveMachine.machine (by unfold extraCount; omega)
    6 15 (by decide) (by decide) (by decide)

noncomputable def quotientSlots :
    MachineInvokeCore.Slots RationalCanonicalCallback.quotientMachine extraCount :=
  slots RationalCanonicalCallback.quotientMachine (by unfold extraCount; omega)
    6 16 (by decide) (by decide) (by decide)

noncomputable def lessSlots :
    MachineInvokeCore.Slots RationalLess.machine extraCount :=
  slots RationalLess.machine (by unfold extraCount; omega)
    26 18 (by decide) (by decide) (by decide)

theorem positive_slots_source : positiveSlots.source = low 6 := rfl
theorem positive_slots_target : positiveSlots.target = low 15 := rfl
theorem quotient_slots_source : quotientSlots.source = low 6 := rfl
theorem quotient_slots_target : quotientSlots.target = low 16 := rfl
theorem less_slots_source : lessSlots.source = low 26 := rfl
theorem less_slots_target : lessSlots.target = low 18 := rfl

theorem high_blank (S : Bank) (hS : ∀ k : Stack, 32 ≤ k.val → S k = [])
    (M : BitMachine.Machine) (h : M.stackCount ≤ extraCount)
    (s t : Fin 32) (hst : s ≠ t) (hs31 : s ≠ 31) (ht31 : t ≠ 31) :
    ∀ k, S ((slots M h s t hst hs31 ht31).machine k) = [] := by
  intro k
  apply hS
  simp [slots, high]

end CurrentAdditive.MinimumRatioCallbackLayout
