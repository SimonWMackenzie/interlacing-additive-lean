import CurrentAdditive.MinimumRatioCallbackLayout

namespace CurrentAdditive.MinimumRatioCallbackCalls

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
open CurrentAdditive.MinimumRatioCallbackLayout

theorem high_after_low_update (S : Bank) (j : Fin 32) (bits : List Bool)
    (h : ∀ k : Stack, 32 ≤ k.val → S k = []) :
    ∀ k : Stack, 32 ≤ k.val →
      (Function.update S (low j) bits) k = [] := by
  intro k hk
  have hne : k ≠ low j := by
    intro he
    have hv := congrArg Fin.val he
    have hj := j.isLt
    simp [low] at hv
    omega
  simp [Function.update_apply, hne, h k hk]

theorem positive_run (S : Bank) (word : List Bool)
    (hsource : S (low 6) = word)
    (htarget : S (low 15) = [])
    (hscratch : S (low 31) = [])
    (hhigh : ∀ k : Stack, 32 ≤ k.val → S k = []) :
    ∃ u ≤ MachineInvokeFull.uniformBound MinimumRatioPositiveMachine.machine
        word (50*(word.length+1)),
      ((advance (MachineInvokeFull.program positiveSlots))^[u])
        (⟨some (MachineInvokeFull.start positiveSlots),
          MachineInvokeFull.control positiveSlots, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, MachineInvokeFull.control positiveSlots,
          Function.update S (low 15)
            (MinimumRatioPositiveMachine.result word)⟩ := by
  have hblank : ∀ k, S (positiveSlots.machine k) = [] := by
    intro k
    apply hhigh
    simp [positiveSlots, slots, high]
  simpa [positive_slots_source, positive_slots_target] using
    (MachineInvokeFull.invoke_run_uniform positiveSlots S word
      (MinimumRatioPositiveMachine.result word) (50*(word.length+1))
      (by simpa [positive_slots_source] using hsource)
      (by simpa [positive_slots_target] using htarget)
      (by simpa [positiveSlots, slots] using hscratch)
      hblank (MinimumRatioPositiveRun.outputs word))

noncomputable def quotientCoefficient : Nat :=
  Classical.choose RationalCanonicalCallback.quotient_outputs_all

theorem quotient_outputs (word : List Bool) :
    RationalCanonicalCallback.quotientMachine.OutputsWithin word
      (RationalCanonicalCallback.quotientResult word)
      (quotientCoefficient * (word.length+1)^96) :=
  (Classical.choose_spec RationalCanonicalCallback.quotient_outputs_all) word

theorem quotient_run (S : Bank) (word : List Bool)
    (hsource : S (low 6) = word)
    (htarget : S (low 16) = [])
    (hscratch : S (low 31) = [])
    (hhigh : ∀ k : Stack, 32 ≤ k.val → S k = []) :
    ∃ u ≤ MachineInvokeFull.uniformBound
        RationalCanonicalCallback.quotientMachine word
        (quotientCoefficient*(word.length+1)^96),
      ((advance (MachineInvokeFull.program quotientSlots))^[u])
        (⟨some (MachineInvokeFull.start quotientSlots),
          MachineInvokeFull.control quotientSlots, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, MachineInvokeFull.control quotientSlots,
          Function.update S (low 16)
            (RationalCanonicalCallback.quotientResult word)⟩ := by
  have hblank : ∀ k, S (quotientSlots.machine k) = [] := by
    intro k
    apply hhigh
    simp [quotientSlots, slots, high]
  simpa [quotient_slots_source, quotient_slots_target] using
    (MachineInvokeFull.invoke_run_uniform quotientSlots S word
      (RationalCanonicalCallback.quotientResult word)
      (quotientCoefficient*(word.length+1)^96)
      (by simpa [quotient_slots_source] using hsource)
      (by simpa [quotient_slots_target] using htarget)
      (by simpa [quotientSlots, slots] using hscratch)
      hblank (quotient_outputs word))

noncomputable def firstTwoProgram :=
  BitMachineRawSequence.program
    (MachineInvokeFull.program positiveSlots)
    (MachineInvokeFull.program quotientSlots)
    (MachineInvokeFull.start quotientSlots)
    (MachineInvokeFull.control positiveSlots)
    (MachineInvokeFull.control quotientSlots)

theorem first_two_run (S : Bank) (word : List Bool)
    (hsource : S (low 6) = word)
    (h15 : S (low 15) = []) (h16 : S (low 16) = [])
    (h31 : S (low 31) = [])
    (hhigh : ∀ k : Stack, 32 ≤ k.val → S k = []) :
    ∃ u ≤ MachineInvokeFull.uniformBound MinimumRatioPositiveMachine.machine
        word (50*(word.length+1)) +
      MachineInvokeFull.uniformBound RationalCanonicalCallback.quotientMachine
        word (quotientCoefficient*(word.length+1)^96) + 1,
      ((advance firstTwoProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (MachineInvokeFull.start positiveSlots)),
          (MachineInvokeFull.control positiveSlots,
            MachineInvokeFull.control quotientSlots), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (MachineInvokeFull.control positiveSlots,
            MachineInvokeFull.control quotientSlots),
          Function.update
            (Function.update S (low 15)
              (MinimumRatioPositiveMachine.result word))
            (low 16) (RationalCanonicalCallback.quotientResult word)⟩ := by
  obtain ⟨a, ha, hrunA⟩ := positive_run S word hsource h15 h31 hhigh
  let T := Function.update S (low 15)
    (MinimumRatioPositiveMachine.result word)
  have h6 : T (low 6) = word := by
    simpa [T, low] using hsource
  have h16' : T (low 16) = [] := by
    simpa [T, low] using h16
  have h31' : T (low 31) = [] := by
    simpa [T, low] using h31
  obtain ⟨b, hb, hrunB⟩ := quotient_run T word h6 h16' h31'
    (high_after_low_update S 15 _ hhigh)
  obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs
    (MachineInvokeFull.program positiveSlots)
    (MachineInvokeFull.program quotientSlots)
    (MachineInvokeFull.start positiveSlots)
    (MachineInvokeFull.start quotientSlots)
    (MachineInvokeFull.control positiveSlots)
    (MachineInvokeFull.control positiveSlots)
    (MachineInvokeFull.control quotientSlots)
    (MachineInvokeFull.control quotientSlots)
    S T (Function.update T (low 16)
      (RationalCanonicalCallback.quotientResult word)) a b
    (by simpa [T] using hrunA) hrunB
  refine ⟨u, ?_, ?_⟩
  · omega
  · simpa [firstTwoProgram, T] using hrun

end CurrentAdditive.MinimumRatioCallbackCalls
