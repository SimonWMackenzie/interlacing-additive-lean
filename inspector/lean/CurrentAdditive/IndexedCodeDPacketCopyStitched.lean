import CurrentAdditive.IndexedCodeDRecordWordStitched

/-! One fixed program executes both source-preserving packet copies in the
larger scheduler bank, with an exact full-bank result. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

def packetCopyProgram (N : ℕ) :=
  BitMachineRawSequence.program
    (ambientWordCopyProgram N) (ambientIndexCopyProgram N)
    (Sum.inl SourceClausePreservingBroadcast.Label.scan)
    ((), none) ((), none)

theorem ambient_word_copy_halted (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool)
    (hword : S (packetAmbient N 3) = word)
    (hscratch : S (packetAmbient N 22) = []) :
    let low := fun k : packetStack => S (packetAmbient N k)
    let T := (ambientPacketFrame S
      (⟨none, ((), none), packetWordCopied low word⟩ :
        TM2.Cfg (fun _ : packetStack => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool))
      (some (.inr ()))).stk
    ∃ t ≤ 2*word.length+4,
      ((advance (ambientWordCopyProgram N))^[t])
        (⟨some (.inl .scan), ((), none), S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, ((), none), T⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := ambient_word_copy_run N S word hword hscratch
  refine ⟨t+1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']
  rw [← ambientPacketFrame_initial S
    SourceClausePreservingBroadcast.Label.scan ((), none) (some (.inr ()))]
  rw [hr]
  rfl

theorem ambient_index_copy_halted (N : ℕ)
    (S : StackN N → List Bool) (index : List Bool)
    (hindex : S (packetAmbient N 4) = index)
    (hscratch : S (packetAmbient N 22) = []) :
    let low := fun k : packetStack => S (packetAmbient N k)
    let T := (ambientPacketFrame S
      (⟨none, ((), none), packetIndexCopied low index⟩ :
        TM2.Cfg (fun _ : packetStack => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool))
      (some (.inr ()))).stk
    ∃ t ≤ 2*index.length+4,
      ((advance (ambientIndexCopyProgram N))^[t])
        (⟨some (.inl .scan), ((), none), S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, ((), none), T⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := ambient_index_copy_run N S index hindex hscratch
  refine ⟨t+1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']
  rw [← ambientPacketFrame_initial S
    SourceClausePreservingBroadcast.Label.scan ((), none) (some (.inr ()))]
  rw [hr]
  rfl

theorem packet_copy_stitched (N : ℕ)
    (S : StackN N → List Bool) (word index : List Bool)
    (hword : S (packetAmbient N 3) = word)
    (hindex : S (packetAmbient N 4) = index)
    (hscratch : S (packetAmbient N 22) = []) :
    let low := fun k : packetStack => S (packetAmbient N k)
    let S1 := (ambientPacketFrame S
      (⟨none, ((), none), packetWordCopied low word⟩ :
        TM2.Cfg (fun _ : packetStack => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool))
      (some (.inr ()))).stk
    let low1 := fun k : packetStack => S1 (packetAmbient N k)
    let S2 := (ambientPacketFrame S1
      (⟨none, ((), none), packetIndexCopied low1 index⟩ :
        TM2.Cfg (fun _ : packetStack => Bool)
          SourceClausePreservingBroadcast.Label (Unit × Option Bool))
      (some (.inr ()))).stk
    ∃ t ≤ 2*word.length+4 + (2*index.length+4) + 1,
      ((advance (packetCopyProgram N))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
          (((), none), ((), none)), S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, (((), none), ((), none)), S2⟩ := by
  dsimp only
  let low := fun k : packetStack => S (packetAmbient N k)
  let S1 := (ambientPacketFrame S
    (⟨none, ((), none), packetWordCopied low word⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk
  let low1 := fun k : packetStack => S1 (packetAmbient N k)
  let S2 := (ambientPacketFrame S1
    (⟨none, ((), none), packetIndexCopied low1 index⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (some (.inr ()))).stk
  have hlow1 (k : packetStack) :
      low1 k = packetWordCopied low word k := by
    change (BitMachineStackEmbedding.bank (packetAmbient N) S
      (packetWordCopied low word)) (packetAmbient N k) = _
    exact BitMachineStackEmbedding.bank_at (packetAmbient N) S
      (packetWordCopied low word) k
  have hindex1 : S1 (packetAmbient N 4) = index := by
    rw [show S1 (packetAmbient N 4) =
      packetWordCopied low word 4 from hlow1 4]
    change SourceClausePreservingBroadcast.result
      (3 : packetStack) 22 [18] word low 4 = index
    rw [SourceClausePreservingBroadcast.other_preserved
      (3 : packetStack) 22 [18] word low 4
      (by decide) (by decide) (by decide)]
    exact hindex
  have hscratch1 : S1 (packetAmbient N 22) = [] := by
    rw [show S1 (packetAmbient N 22) =
      packetWordCopied low word 22 from hlow1 22]
    simp [packetWordCopied, SourceClausePreservingBroadcast.result]
  obtain ⟨t1, ht1, hr1⟩ :=
    ambient_word_copy_halted N S word hword hscratch
  obtain ⟨t2, ht2, hr2⟩ :=
    ambient_index_copy_halted N S1 index hindex1 hscratch1
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (ambientWordCopyProgram N) (ambientIndexCopyProgram N)
    (.inl .scan) (.inl .scan)
    ((), none) ((), none) ((), none) ((), none)
    S S1 S2 t1 t2 hr1 hr2
  exact ⟨t, by omega, hr⟩

#print axioms ambient_word_copy_halted
#print axioms ambient_index_copy_halted
#print axioms packet_copy_stitched

end CurrentAdditive.IndexedExecutableStepRecovery
