import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerFinishItem

/-! A full canonical item step with an original-size, per-item clock. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication
open scoped BigOperators

noncomputable section

noncomputable def framePushBound : ℕ :=
  ∑ l : SourceOriginalPacketFraming.Label,
    BitMachine.pushBound (SourceOriginalPacketFraming.program l)

theorem frame_step_length (c : SourceOriginalPacketFraming.Config)
    (k : FrameStack) :
    ((advance SourceOriginalPacketFraming.program c).stk k).length ≤
      (c.stk k).length + framePushBound := by
  cases c with
  | mk l v S =>
      cases l with
      | none => simp [advance, TM2.step]
      | some l =>
          have h := BitMachine.stepAux_length
            (SourceOriginalPacketFraming.program l) v S k
          have hb : BitMachine.pushBound
              (SourceOriginalPacketFraming.program l) ≤ framePushBound := by
            unfold framePushBound
            exact Finset.single_le_sum
              (f := fun j => BitMachine.pushBound
                (SourceOriginalPacketFraming.program j))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
          exact h.trans (Nat.add_le_add_left hb _)

theorem frame_run_length (c : SourceOriginalPacketFraming.Config)
    (k : FrameStack) (t : ℕ) :
    ((((advance SourceOriginalPacketFraming.program)^[t]) c).stk k).length ≤
      (c.stk k).length + t * framePushBound := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hs := frame_step_length
        (((advance SourceOriginalPacketFraming.program)^[t]) c) k
      simp only [Nat.succ_mul]
      omega

def frameBankBound (n : ℕ) (word : List Bool) : ℕ :=
  n + word.length + SourceOriginalPacketFraming.totalTime n word *
    framePushBound

theorem frame_bank_length (n : ℕ) (word : List Bool)
    (t : ℕ) (ht : t ≤ SourceOriginalPacketFraming.totalTime n word)
    (c : SourceOriginalPacketFraming.Config)
    (hrun : ((advance SourceOriginalPacketFraming.program)^[t])
      (SourceOriginalPacketFraming.startCfg n word) = c)
    (k : FrameStack) : (c.stk k).length ≤ frameBankBound n word := by
  have h := frame_run_length (SourceOriginalPacketFraming.startCfg n word) k t
  rw [hrun] at h
  have hi : ((SourceOriginalPacketFraming.startCfg n word).stk k).length ≤
      n + word.length := by
    rw [SourceOriginalPacketFraming.startCfg_bank]
    split_ifs <;> simp <;> omega
  have hm := Nat.mul_le_mul_right framePushBound ht
  dsimp [frameBankBound]
  omega

def frameCleanupBound (n : ℕ) (word : List Bool) : ℕ :=
  Fintype.card FrameStack * frameBankBound n word + Fintype.card FrameStack + 1

noncomputable def outerPushBound : ℕ :=
  ∑ l : Label, BitMachine.pushBound (program l)

theorem outer_step_length (c : Config) (k : Stack) :
    ((advance program c).stk k).length ≤ (c.stk k).length + outerPushBound := by
  cases c with
  | mk l v S =>
      cases l with
      | none => simp [advance, TM2.step]
      | some l =>
          have h := BitMachine.stepAux_length (program l) v S k
          have hb : BitMachine.pushBound (program l) ≤ outerPushBound := by
            unfold outerPushBound
            exact Finset.single_le_sum
              (f := fun j => BitMachine.pushBound (program j))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
          exact h.trans (Nat.add_le_add_left hb _)

theorem outer_run_length (c : Config) (k : Stack) (t : ℕ) :
    ((run t c).stk k).length ≤ (c.stk k).length + t * outerPushBound := by
  induction t with
  | zero => simp [run]
  | succ t ih =>
      rw [run, Function.iterate_succ_apply']
      change ((advance program (run t c)).stk k).length ≤
        (c.stk k).length + (t+1) * outerPushBound
      have hs := outer_step_length (run t c) k
      change ((advance program (run t c)).stk k).length ≤
        ((run t c).stk k).length + outerPushBound at hs
      simp only [Nat.succ_mul]
      omega

def outerFrameBound (n : ℕ) (word : List Bool) : ℕ :=
  n + word.length + SourceOriginalPacketFraming.totalTime n word * outerPushBound

theorem frameFrame_bank (S : Stack → List Bool)
    (c : SourceOriginalPacketFraming.Config) (k : FrameStack) :
    (frameFrame S c).stk (.inl k) = c.stk k := by
  exact BitMachineStackEmbedding.bank_at frameStack S c.stk k

theorem embedded_frame_bank_length (S : Stack → List Bool)
    (n : ℕ) (word : List Bool) (t : ℕ)
    (ht : t ≤ SourceOriginalPacketFraming.totalTime n word)
    (c : SourceOriginalPacketFraming.Config)
    (hrun : frameFrame S c =
      run t (frameFrame S (SourceOriginalPacketFraming.startCfg n word)))
    (k : FrameStack) :
    (c.stk k).length ≤ outerFrameBound n word := by
  have h := outer_run_length
    (frameFrame S (SourceOriginalPacketFraming.startCfg n word)) (.inl k) t
  rw [← hrun, frameFrame_bank S c k,
    frameFrame_bank S (SourceOriginalPacketFraming.startCfg n word) k] at h
  have hi : ((SourceOriginalPacketFraming.startCfg n word).stk k).length ≤
      n + word.length := by
    rw [SourceOriginalPacketFraming.startCfg_bank]
    split_ifs <;> simp <;> omega
  have hm := Nat.mul_le_mul_right outerPushBound ht
  dsimp [outerFrameBound]
  omega

def outerCleanupBound (n : ℕ) (word : List Bool) : ℕ :=
  Fintype.card FrameStack * outerFrameBound n word +
    Fintype.card FrameStack + 1

theorem emitted_frame_length (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config)
    (hbound : ∀ k : FrameStack,
      (c.stk k).length ≤ outerFrameBound n word)
    (k : FrameStack) :
    ((Function.update (emittedBank n word suffix q acc c) (.inr 8) [])
      (.inl k)).length ≤ outerFrameBound n word := by
  by_cases hk : k = SourceOriginalPacketFraming.outputStack
  · subst k
    simp [emittedBank, BitMachineBroadcast.contents]
  · have heq : emittedBank n word suffix q acc c (.inl k) = c.stk k := by
      simp [emittedBank, BitMachineBroadcast.contents, hk, postFrame_local]
    simpa [heq] using hbound k

theorem cleanupTime_le (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config)
    (hbound : ∀ k : FrameStack,
      (c.stk k).length ≤ outerFrameBound n word) :
    cleanupTime n word suffix q acc c ≤ outerCleanupBound n word := by
  have hs : (∑ i : Fin (Fintype.card FrameStack),
      if SourceOriginalListPacketizerCleanupRun.frameBank i =
          .inl SourceOriginalPacketFraming.nStack then 0
      else ((Function.update (emittedBank n word suffix q acc c) (.inr 8) [])
        (SourceOriginalListPacketizerCleanupRun.frameBank i)).length) ≤
      ∑ _i : Fin (Fintype.card FrameStack), outerFrameBound n word := by
    apply Finset.sum_le_sum
    intro i _
    split
    · exact Nat.zero_le _
    · exact emitted_frame_length n word suffix q acc c hbound
        ((Fintype.equivFin FrameStack).symm i)
  simpa [cleanupTime, outerCleanupBound] using
    (Nat.add_le_add_right hs (Fintype.card FrameStack + 1))

def itemTimeBound (n : ℕ) (q word : List Bool) : ℕ :=
  (4*q.length+5) + 1 +
  20*(word.length+1)*(word.length.bits.length+1) + 1 +
  SourceOriginalPacketFraming.totalTime n word +
  1 + (SourceOriginalPacketFraming.answer n word).length+1 +
  (word.length+1) + outerCleanupBound n word

theorem canonical_item_step (n : ℕ) (word suffix q q' acc : List Bool)
    (hdec : ProtocolBinaryCounter.subOne q = some q') :
    ∃ t ≤ itemTimeBound n q word,
      run t (loopCfg (readyBank n
        (natField word.length ++ (word ++ suffix)) q acc)) =
      loopCfg (readyBank n suffix q'
        ((SourceOriginalPacketFraming.answer n word).reverse ++ acc)) := by
  obtain ⟨a, ha, hprefix⟩ :=
    canonical_item_to_frameStart n word suffix q q' acc hdec
  let S := frameReadyBank n word suffix q' acc
  obtain ⟨b, hb, c, hframe, hhalt, hout, hn, hw⟩ :=
    frame_embedded S n word
  have hbound : ∀ k : FrameStack,
      (c.stk k).length ≤ outerFrameBound n word := by
    intro k
    exact embedded_frame_bank_length S n word b hb c hframe k
  have hcleanup := cleanupTime_le n word suffix q' acc c hbound
  have hpost := frame_to_loop n word suffix q' acc c hhalt hout hn
  have h1 : run (a+b)
      (loopCfg (readyBank n
        (natField word.length ++ (word ++ suffix)) q acc)) =
      frameFrame S c :=
    (run_add hprefix b).trans hframe.symm
  refine ⟨a+b + (1 + (SourceOriginalPacketFraming.answer n word).length+1 +
      (word.length+1) + cleanupTime n word suffix q' acc c), ?_, ?_⟩
  · dsimp [itemTimeBound]
    omega
  · exact (run_add h1 _).trans hpost

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
