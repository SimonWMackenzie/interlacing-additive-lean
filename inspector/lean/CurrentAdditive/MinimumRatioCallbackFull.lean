import CurrentAdditive.MinimumRatioCallbackStages

namespace CurrentAdditive.MinimumRatioCallbackFull

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

theorem at_other (S : Bank) (i j : Fin 32) (h : i ≠ j)
    (bits : List Bool) :
    (Function.update S (low i) bits) (low j) = S (low j) := by
  exact Function.update_of_ne
    (CurrentAdditive.MinimumRatioBestUpdate.low_ne i j h).symm _ _

def ScratchEmpty (S : Bank) : Prop :=
  (∀ j : Fin 32, 15 ≤ j.val → S (low j) = []) ∧
  (∀ k : Stack, 32 ≤ k.val → S k = [])

theorem scratch_at (S : Bank) (h : ScratchEmpty S)
    (j : Fin 32) (hj : 15 ≤ j.val) : S (low j) = [] :=
  h.1 j hj

theorem high_after_two (S : Bank) (a b : List Bool)
    (h : ScratchEmpty S) :
    ∀ k : Stack, 32 ≤ k.val →
      (Function.update (Function.update S (low 15) a) (low 16) b) k = [] :=
  CurrentAdditive.MinimumRatioCallbackCalls.high_after_low_update
    (Function.update S (low 15) a) 16 b
    (CurrentAdditive.MinimumRatioCallbackCalls.high_after_low_update
      S 15 a h.2)

noncomputable def firstHalfProgram :=
  BitMachineRawSequence.program
    CurrentAdditive.MinimumRatioCallbackCalls.firstTwoProgram
    CurrentAdditive.MinimumRatioCallbackStages.copyTailProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control quotientSlots)
    (none, none)

theorem first_half_run (S : Bank) (word best : List Bool)
    (h6 : S (low 6) = word) (h9 : S (low 9) = best)
    (hscratch : ScratchEmpty S) :
    let pos := MinimumRatioPositiveMachine.result word
    let q := RationalCanonicalCallback.quotientResult word
    ∃ u ≤
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
        MinimumRatioPositiveMachine.machine word (50*(word.length+1)) +
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
        RationalCanonicalCallback.quotientMachine word
        (CurrentAdditive.MinimumRatioCallbackCalls.quotientCoefficient *
          (word.length+1)^96) + 1 +
      (2*best.length+4) + 1,
      ((advance firstHalfProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
              positiveSlots))),
          ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              positiveSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              quotientSlots), (none,none)), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              positiveSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              quotientSlots), (none,best.head?)),
          Function.update
            (Function.update
              (Function.update S (low 15) pos) (low 16) q)
            (low 20) best.tail⟩ := by
  dsimp only
  let pos := MinimumRatioPositiveMachine.result word
  let q := RationalCanonicalCallback.quotientResult word
  let T := Function.update (Function.update S (low 15) pos) (low 16) q
  obtain ⟨a,ha,hrA⟩ :=
    CurrentAdditive.MinimumRatioCallbackCalls.first_two_run S word h6
      (scratch_at S hscratch 15 (by decide))
      (scratch_at S hscratch 16 (by decide))
      (scratch_at S hscratch 31 (by decide)) hscratch.2
  have h9T : T (low 9) = best := by
    simp [T, at_other, h9]
  have h20T : T (low 20) = [] := by
    simp [T, at_other, scratch_at S hscratch 20 (by decide)]
  have h21T : T (low 21) = [] := by
    simp [T, at_other, scratch_at S hscratch 21 (by decide)]
  obtain ⟨b,hb,hrB⟩ :=
    CurrentAdditive.MinimumRatioCallbackStages.copy_tail_run T best
      h9T h20T h21T
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    CurrentAdditive.MinimumRatioCallbackCalls.firstTwoProgram
    CurrentAdditive.MinimumRatioCallbackStages.copyTailProgram
    (BitMachineRawSequence.leftLabel
      (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
        positiveSlots))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots)
    (none,none) (none,best.head?)
    S T (Function.update T (low 20) best.tail) a b
    (by simpa [T, pos, q] using hrA) hrB
  refine ⟨u, by omega, ?_⟩
  simpa [firstHalfProgram, T, pos, q] using hr

noncomputable def preUpdateProgram :=
  BitMachineRawSequence.program firstHalfProgram
    CurrentAdditive.MinimumRatioCallbackStages.pairLessProgram
    (BitMachineRawSequence.leftLabel
      CurrentAdditive.MinimumRatioContext.RawRatPairFull.start)
    ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots), (none,none))
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)

theorem pre_update_run (S : Bank) (word best : List Bool)
    (h6 : S (low 6) = word) (h9 : S (low 9) = best)
    (hscratch : ScratchEmpty S) :
    let pos := MinimumRatioPositiveMachine.result word
    let q := RationalCanonicalCallback.quotientResult word
    let pair := RawRatPairAssembler.pairWord q best.tail
    let S2 := Function.update
      (Function.update
        (Function.update S (low 15) pos) (low 16) q)
      (low 20) best.tail
    ∃ u ≤
      (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
        MinimumRatioPositiveMachine.machine word (50*(word.length+1)) +
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
        RationalCanonicalCallback.quotientMachine word
        (CurrentAdditive.MinimumRatioCallbackCalls.quotientCoefficient *
          (word.length+1)^96) + 1 +
      (2*best.length+4) + 1) +
      (CurrentAdditive.MinimumRatioContext.RawRatPairFull.linearBound
        extraCount q best.tail +
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
        RationalLess.machine pair
        (RationalLess.coefficient*(pair.length+1)^RationalLess.exponent) + 1) + 1,
      ((advance preUpdateProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
                positiveSlots)))),
          (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                positiveSlots,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                quotientSlots), (none,none)),
            (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                lessSlots)), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                positiveSlots,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                quotientSlots), (none,none)),
            (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                lessSlots)),
          Function.update
            (Function.update S2 (low 26) pair)
            (low 18) (RationalLess.result pair)⟩ := by
  dsimp only
  let pos := MinimumRatioPositiveMachine.result word
  let q := RationalCanonicalCallback.quotientResult word
  let pair := RawRatPairAssembler.pairWord q best.tail
  let T := Function.update (Function.update S (low 15) pos) (low 16) q
  let S2 := Function.update T (low 20) best.tail
  obtain ⟨a,ha,hrA⟩ := first_half_run S word best h6 h9 hscratch
  have h16S2 : S2 (low 16) = q := by simp [S2, T, at_other]
  have h20S2 : S2 (low 20) = best.tail := by simp [S2]
  have h18S2 : S2 (low 18) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 18 (by decide)]
  have h31S2 : S2 (low 31) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 31 (by decide)]
  have h22S2 : S2 (low 22) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 22 (by decide)]
  have h23S2 : S2 (low 23) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 23 (by decide)]
  have h24S2 : S2 (low 24) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 24 (by decide)]
  have h25S2 : S2 (low 25) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 25 (by decide)]
  have h26S2 : S2 (low 26) = [] := by
    simp [S2, T, at_other, scratch_at S hscratch 26 (by decide)]
  have hhighS2 : ∀ k : Stack, 32 ≤ k.val → S2 k = [] :=
    CurrentAdditive.MinimumRatioCallbackCalls.high_after_low_update
      T 20 best.tail (high_after_two S pos q hscratch)
  obtain ⟨b,hb,hrB⟩ :=
    CurrentAdditive.MinimumRatioCallbackStages.pair_less_run S2 q best.tail
      h16S2 h20S2 h22S2 h23S2 h24S2 h25S2 h26S2
      h18S2 h31S2 hhighS2
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    firstHalfProgram
    CurrentAdditive.MinimumRatioCallbackStages.pairLessProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
          positiveSlots)))
    (BitMachineRawSequence.leftLabel
      CurrentAdditive.MinimumRatioContext.RawRatPairFull.start)
    ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots), (none,none))
    ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots), (none,best.head?))
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)
    S S2 (Function.update (Function.update S2 (low 26) pair)
      (low 18) (RationalLess.result pair)) a b
    (by simpa [S2, T, pos, q] using hrA)
    (by simpa [pair] using hrB)
  refine ⟨u, ?_, ?_⟩
  · have hb' : b ≤
        CurrentAdditive.MinimumRatioContext.RawRatPairFull.linearBound
          extraCount (RationalCanonicalCallback.quotientResult word) best.tail +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          RationalLess.machine
          (RawRatPairAssembler.pairWord
            (RationalCanonicalCallback.quotientResult word) best.tail)
          (RationalLess.coefficient *
            ((RawRatPairAssembler.pairWord
                (RationalCanonicalCallback.quotientResult word)
                best.tail).length + 1) ^ RationalLess.exponent) + 1 := by
      simpa only [q, pair] using hb
    omega
  · simpa [preUpdateProgram, S2, T, pos, q, pair] using hr

noncomputable def itemProgram :=
  BitMachineRawSequence.program preUpdateProgram
    CurrentAdditive.MinimumRatioBestUpdate.program
    CurrentAdditive.MinimumRatioBestUpdate.Label.positive
    (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          positiveSlots,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          quotientSlots), (none,none)),
      (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots))
    CurrentAdditive.MinimumRatioBestUpdate.initial

theorem item_run (S : Bank) (word best : List Bool)
    (h6 : S (low 6) = word) (h9 : S (low 9) = best)
    (hscratch : ScratchEmpty S) :
    let pos := MinimumRatioPositiveMachine.result word
    let q := RationalCanonicalCallback.quotientResult word
    let pair := RawRatPairAssembler.pairWord q best.tail
    let S2 := Function.update
      (Function.update
        (Function.update S (low 15) pos) (low 16) q)
      (low 20) best.tail
    let S3 := Function.update
      (Function.update S2 (low 26) pair)
      (low 18) (RationalLess.result pair)
    ∃ u ≤
      ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          MinimumRatioPositiveMachine.machine word (50*(word.length+1)) +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          RationalCanonicalCallback.quotientMachine word
          (CurrentAdditive.MinimumRatioCallbackCalls.quotientCoefficient *
            (word.length+1)^96) + 1 +
        (2*best.length+4) + 1) +
        (CurrentAdditive.MinimumRatioContext.RawRatPairFull.linearBound
          extraCount q best.tail +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          RationalLess.machine pair
          (RationalLess.coefficient*(pair.length+1)^RationalLess.exponent) + 1)
        + 1) +
      (3 + (S3 (low 9)).length + 1 +
        (2*(S3 (low 16)).length+2) + 1) + 1,
      ((advance itemProgram)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
                  positiveSlots))))),
          ((((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                positiveSlots,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                quotientSlots), (none,none)),
            (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                lessSlots)),
            CurrentAdditive.MinimumRatioBestUpdate.initial), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                positiveSlots,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                quotientSlots), (none,none)),
            (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
              CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
                lessSlots)),
            if CurrentAdditive.MinimumRatioBestUpdate.shouldReplace S3 then
              CurrentAdditive.MinimumRatioBestUpdate.initial else
              (((S3 (low 15)).head?, (S3 (low 9)).head?,
                (S3 (low 18)).head?), none)),
          Function.update
            (CurrentAdditive.MinimumRatioBestUpdate.readBank S3)
            (low 9)
            (CurrentAdditive.MinimumRatioBestUpdate.chosenBest S3)⟩ := by
  dsimp only
  let pos := MinimumRatioPositiveMachine.result word
  let q := RationalCanonicalCallback.quotientResult word
  let pair := RawRatPairAssembler.pairWord q best.tail
  let T := Function.update (Function.update S (low 15) pos) (low 16) q
  let S2 := Function.update T (low 20) best.tail
  let S3 := Function.update (Function.update S2 (low 26) pair)
    (low 18) (RationalLess.result pair)
  obtain ⟨a,ha,hrA⟩ := pre_update_run S word best h6 h9 hscratch
  have h21S3 : S3 (low 21) = [] := by
    simp [S3, S2, T, at_other,
      scratch_at S hscratch 21 (by decide)]
  obtain ⟨b,hb,hrB⟩ :=
    CurrentAdditive.MinimumRatioBestUpdate.update_run S3 h21S3
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    preUpdateProgram CurrentAdditive.MinimumRatioBestUpdate.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            positiveSlots))))
    CurrentAdditive.MinimumRatioBestUpdate.Label.positive
    (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          positiveSlots,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          quotientSlots), (none,none)),
      (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots))
    (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          positiveSlots,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          quotientSlots), (none,none)),
      (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots))
    CurrentAdditive.MinimumRatioBestUpdate.initial
    (if CurrentAdditive.MinimumRatioBestUpdate.shouldReplace S3 then
      CurrentAdditive.MinimumRatioBestUpdate.initial else
      (((S3 (low 15)).head?, (S3 (low 9)).head?,
        (S3 (low 18)).head?), none))
    S S3
    (Function.update (CurrentAdditive.MinimumRatioBestUpdate.readBank S3)
      (low 9) (CurrentAdditive.MinimumRatioBestUpdate.chosenBest S3))
    a b (by simpa [S3, S2, T, pos, q, pair] using hrA) hrB
  refine ⟨u, ?_, ?_⟩
  · dsimp only [S3, S2, T, pos, q, pair] at hb
    omega
  · simpa [itemProgram, S3, S2, T, pos, q, pair] using hr

end CurrentAdditive.MinimumRatioCallbackFull
