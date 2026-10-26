import CurrentAdditive.MinimumRatioBestUpdateRun

namespace CurrentAdditive.MinimumRatioCallbackStages

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

noncomputable def copyTailProgram :=
  BitMachineRawSequence.program
    MinimumRatioBestTail.copyProgram MinimumRatioBestTail.tailProgram
    () none none

theorem copy_tail_run (S : Bank) (best : List Bool)
    (h9 : S (low 9) = best)
    (h20 : S (low 20) = []) (h21 : S (low 21) = []) :
    ∃ u ≤ 2*best.length+4,
      ((advance copyTailProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          BitMachineCopy.Label.scan), (none, none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (none, best.head?),
          Function.update S (low 20) best.tail⟩ := by
  obtain ⟨a,ha,hrA⟩ := MinimumRatioBestTail.copy_run S best h9 h20 h21
  let T := Function.update S (low 20) best
  have htail := MinimumRatioBestTail.tail_run T
  have ht : T (low 20) = best := by simp [T]
  rw [ht] at htail
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    MinimumRatioBestTail.copyProgram MinimumRatioBestTail.tailProgram
    BitMachineCopy.Label.scan () none none none best.head?
    S T (Function.update T (low 20) best.tail) a 1
    (by simpa [T] using hrA) htail
  refine ⟨u, by omega, ?_⟩
  simpa [copyTailProgram, T] using hr

noncomputable def pairLessProgram :=
  BitMachineRawSequence.program
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.program extraCount)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program lessSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start lessSlots)
    CurrentAdditive.MinimumRatioContext.RawRatPairFull.control
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)

theorem pair_less_run (S : Bank) (x y : List Bool)
    (hx : S (low 16) = x) (hy : S (low 20) = y)
    (h22 : S (low 22) = []) (h23 : S (low 23) = [])
    (h24 : S (low 24) = []) (h25 : S (low 25) = [])
    (h26 : S (low 26) = [])
    (h18 : S (low 18) = [])
    (h31 : S (low 31) = [])
    (hhigh : ∀ k : Stack, 32 ≤ k.val → S k = []) :
    let pair := RawRatPairAssembler.pairWord x y
    ∃ u ≤ CurrentAdditive.MinimumRatioContext.RawRatPairFull.linearBound
        extraCount x y +
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
        RationalLess.machine pair
        (RationalLess.coefficient*(pair.length+1)^RationalLess.exponent) + 1,
      ((advance pairLessProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          CurrentAdditive.MinimumRatioContext.RawRatPairFull.start),
          (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots),
          S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots),
          Function.update
            (Function.update S (low 26) pair)
            (low 18) (RationalLess.result pair)⟩ := by
  dsimp only
  let pair := RawRatPairAssembler.pairWord x y
  let T := Function.update S (low 26) pair
  obtain ⟨a,ha,hrA⟩ :=
    CurrentAdditive.MinimumRatioPairAndLess.pair_run S x y
      hx hy h22 h23 h24 h25 h26
  have hsource : T (low 26) = pair := by simp [T]
  have htarget : T (low 18) = [] := by
    simpa [T, Function.update_of_ne,
      (MinimumRatioBestUpdate.low_ne 26 18 (by decide)).symm] using h18
  have hscratch : T (low 31) = [] := by
    simpa [T, Function.update_of_ne,
      (MinimumRatioBestUpdate.low_ne 26 31 (by decide)).symm] using h31
  obtain ⟨b,hb,hrB⟩ :=
    CurrentAdditive.MinimumRatioPairAndLess.less_run T pair
      hsource htarget hscratch
      (CurrentAdditive.MinimumRatioCallbackCalls.high_after_low_update
        S 26 pair hhigh)
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.program extraCount)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program lessSlots)
    CurrentAdditive.MinimumRatioContext.RawRatPairFull.start
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start lessSlots)
    CurrentAdditive.MinimumRatioContext.RawRatPairFull.control
    CurrentAdditive.MinimumRatioContext.RawRatPairFull.control
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)
    S T (Function.update T (low 18) (RationalLess.result pair)) a b
    (by simpa [T] using hrA) hrB
  refine ⟨u, ?_, ?_⟩
  · have hb' : b ≤
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          RationalLess.machine (RawRatPairAssembler.pairWord x y)
          (RationalLess.coefficient *
            ((RawRatPairAssembler.pairWord x y).length + 1) ^
              RationalLess.exponent) := by
      simpa only [pair] using hb
    omega
  · simpa [pairLessProgram, T, pair] using hr

end CurrentAdditive.MinimumRatioCallbackStages
