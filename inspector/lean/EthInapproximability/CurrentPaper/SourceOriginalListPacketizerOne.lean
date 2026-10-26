import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerCleanupRun

/-! One canonical branch step of the physical original-size packetizer. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

noncomputable section

theorem counter_success_bank (n : ℕ) (source q q' acc : List Bool) :
    BitMachineStackEmbedding.bank counterStack (readyBank n source q acc)
      (SourceListMachineCounter.cfg none
        (SourceListMachineCounter.doneControl true) q' []).stk =
    readyBank n source q' acc := by
  funext k
  cases k with
  | inl k =>
      have hk : ¬ ∃ i : SourceListMachineCounter.Stack,
          counterStack i = (.inl k : Stack) := by
        rintro ⟨i,hi⟩
        fin_cases i <;> cases hi
      rw [BitMachineStackEmbedding.bank_outside counterStack _ _ _ hk]
      rfl
  | inr k =>
      fin_cases k
      · rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi
      · rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi
      · change (BitMachineStackEmbedding.bank counterStack _ _)
          (counterStack 0) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · change (BitMachineStackEmbedding.bank counterStack _ _)
          (counterStack 1) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      all_goals
        rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi

theorem ready_field_start (n : ℕ) (word suffix q acc : List Bool) :
    fieldFrame (readyBank n (natField word.length ++ (word ++ suffix)) q acc)
      (SourceListMachineFields.cfg (some (.inl .scan))
        SourceListMachineFields.initialControl
        {input := natField word.length ++ (word ++ suffix)}) =
    ⟨some (fieldLabel (.inl .scan)),
      fieldControl SourceListMachineFields.initialControl,
      readyBank n (natField word.length ++ (word ++ suffix)) q acc⟩ := by
  apply fieldFrame_initial
  all_goals simp [readyBank, SourceOriginalPacketFraming.nStack_ne_wordStack,
    Ne.symm SourceOriginalPacketFraming.nStack_ne_wordStack]

def frameReadyBank (n : ℕ) (word suffix q acc : List Bool) : Stack → List Bool :=
  fun k => if k = .inl SourceOriginalPacketFraming.nStack then
    List.replicate n true
  else if k = .inl SourceOriginalPacketFraming.wordStack then word
  else if k = .inr 0 then suffix
  else if k = .inr 2 then q
  else if k = .inr 4 then acc
  else if k = .inr 8 then List.replicate word.length true
  else []

theorem field_success_bank (n : ℕ) (word suffix q acc : List Bool) :
    BitMachineStackEmbedding.bank fieldStack
      (readyBank n (natField word.length ++ (word ++ suffix)) q acc)
      (SourceListMachineFields.success word suffix).stk =
    frameReadyBank n word suffix q acc := by
  funext k
  cases k with
  | inl k =>
      by_cases hw : k = SourceOriginalPacketFraming.wordStack
      · subst k
        change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 6) = _
        rw [BitMachineStackEmbedding.bank_at]
        simp [SourceListMachineFields.success, SourceListMachineFields.cfg,
          SourceListMachineFields.Data.stacks, frameReadyBank,
          Ne.symm SourceOriginalPacketFraming.nStack_ne_wordStack]
      · have hk : ¬ ∃ i : SourceListMachineFields.Stack,
            fieldStack i = (.inl k : Stack) := by
          rintro ⟨i,hi⟩
          fin_cases i <;> simp [fieldStack] at hi
          exact hw hi.symm
        rw [BitMachineStackEmbedding.bank_outside fieldStack _ _ _ hk]
        simp [readyBank, frameReadyBank, hw]
  | inr k =>
      fin_cases k
      · change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 0) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 1) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi

      · rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi

      · rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi
      · change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 2) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 3) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 4) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · change (BitMachineStackEmbedding.bank fieldStack _ _)
          (fieldStack 5) = _
        rw [BitMachineStackEmbedding.bank_at]
        rfl
      · rw [BitMachineStackEmbedding.bank_outside]
        · rfl
        · rintro ⟨i,hi⟩; fin_cases i <;> cases hi

def frameFrame (S : Stack → List Bool)
    (c : SourceOriginalPacketFraming.Config) : Config :=
  BitMachineStackEmbedding.cfg frameStack S frameLabel frameControl
    (some (adminLabel .afterFrame)) c

theorem frameFrame_initial (n : ℕ) (word suffix q acc : List Bool) :
    frameFrame (frameReadyBank n word suffix q acc)
      (SourceOriginalPacketFraming.startCfg n word) =
    ⟨some (frameLabel frameStartLabel),frameControl frameInitialControl,
      frameReadyBank n word suffix q acc⟩ := by
  have h : ∀ k : FrameStack,
      (SourceOriginalPacketFraming.startCfg n word).stk k =
        frameReadyBank n word suffix q acc (frameStack k) := by
    intro k
    rw [SourceOriginalPacketFraming.startCfg_bank]
    simp [frameStack, frameReadyBank]
  unfold frameFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self frameStack _ _ h]
  rfl

theorem frame_embedded (S : Stack → List Bool) (n : ℕ) (word : List Bool) :
    ∃ t ≤ SourceOriginalPacketFraming.totalTime n word,
      ∃ c : SourceOriginalPacketFraming.Config,
      frameFrame S c = run t
        (frameFrame S (SourceOriginalPacketFraming.startCfg n word)) ∧
      c.l = none ∧
      c.stk SourceOriginalPacketFraming.outputStack =
        SourceOriginalPacketFraming.answer n word ∧
      c.stk SourceOriginalPacketFraming.nStack = List.replicate n true ∧
      c.stk SourceOriginalPacketFraming.wordStack = [] := by
  obtain ⟨a, ha, b, hb, c, hc, hstate, hhalt, hout, hn, hw⟩ :=
    SourceOriginalPacketFraming.framed_run n word
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs frameStack S
    frameLabel frameControl (fun v => v.1.2)
    (by intro v; rfl) (some (adminLabel .afterFrame))
    SourceOriginalPacketFraming.program program (fun _ => rfl)
    (SourceOriginalPacketFraming.startCfg n word) a
    (by change (((advance SourceOriginalPacketFraming.program)^[a])
          (SourceOriginalPacketFraming.startCfg n word)).l = none
        rw [hc]; exact hhalt)
  rw [hc] at hr
  exact ⟨t,ht.trans ha,c,hr.symm,hhalt,hout,hn,hw⟩

theorem counter_to_field (n : ℕ) (word suffix q q' acc : List Bool) :
    run 1 (counterFrame
      (readyBank n (natField word.length ++ (word ++ suffix)) q acc)
      (SourceListMachineCounter.cfg none
        (SourceListMachineCounter.doneControl true) q' [])) =
    fieldFrame
      (readyBank n (natField word.length ++ (word ++ suffix)) q' acc)
      (SourceListMachineFields.cfg (some (.inl .scan))
        SourceListMachineFields.initialControl
        {input := natField word.length ++ (word ++ suffix)}) := by
  rw [counterFrame_halted, counter_success_bank]
  rw [run_succ (afterCounter_positive _) 0]
  exact (ready_field_start n word suffix q' acc).symm

theorem field_to_frame (n : ℕ) (word suffix q acc : List Bool) :
    run 1 (fieldFrame
      (readyBank n (natField word.length ++ (word ++ suffix)) q acc)
      (SourceListMachineFields.success word suffix)) =
    frameFrame (frameReadyBank n word suffix q acc)
      (SourceOriginalPacketFraming.startCfg n word) := by
  change run 1 (fieldFrame _ (SourceListMachineFields.cfg none
    (SourceListMachineFields.coreControl (some true,false))
    {input := suffix, count := List.replicate word.length true,
      payload := word})) = _
  rw [fieldFrame_halted]
  change run 1 ⟨some (adminLabel .afterField),
    fieldControl (SourceListMachineFields.coreControl (some true,false)),
    BitMachineStackEmbedding.bank fieldStack
      (readyBank n (natField word.length ++ (word ++ suffix)) q acc)
      (SourceListMachineFields.success word suffix).stk⟩ = _
  rw [field_success_bank]
  rw [run_succ (afterField_positive _) 0]
  exact (frameFrame_initial n word suffix q acc).symm

theorem canonical_item_to_frame (n : ℕ) (word suffix q q' acc : List Bool)
    (hdec : ProtocolBinaryCounter.subOne q = some q') :
    ∃ t ≤ (4*q.length+5) + 1 +
        20*(word.length+1)*(word.length.bits.length+1) + 1 +
        SourceOriginalPacketFraming.totalTime n word,
      ∃ c : SourceOriginalPacketFraming.Config,
      run t (loopCfg (readyBank n
        (natField word.length ++ (word ++ suffix)) q acc)) =
        frameFrame (frameReadyBank n word suffix q' acc) c ∧
      c.l = none ∧
      c.stk SourceOriginalPacketFraming.outputStack =
        SourceOriginalPacketFraming.answer n word ∧
      c.stk SourceOriginalPacketFraming.nStack = List.replicate n true ∧
      c.stk SourceOriginalPacketFraming.wordStack = [] := by
  let S := readyBank n (natField word.length ++ (word ++ suffix)) q acc
  have hstart : counterFrame S
      (SourceListMachineCounter.cfg (some (.inr .scan))
        SourceListMachineCounter.initialControl q []) = loopCfg S := by
    apply counterFrame_initial
    · exact readyBank_count n _ q acc
    · simp [S, readyBank]
  obtain ⟨a, ha, hcounter⟩ := counter_embedded S q
  rw [hdec] at hcounter
  rw [hstart] at hcounter
  have hfieldStart := counter_to_field n word suffix q q' acc
  have h1 : run (a+1) (loopCfg S) =
      fieldFrame (readyBank n
        (natField word.length ++ (word ++ suffix)) q' acc)
        (SourceListMachineFields.cfg (some (.inl .scan))
          SourceListMachineFields.initialControl
          {input := natField word.length ++ (word ++ suffix)}) :=
    (run_add hcounter 1).trans hfieldStart
  obtain ⟨b, hb, hfield⟩ :=
    field_embedded (readyBank n
      (natField word.length ++ (word ++ suffix)) q' acc) word suffix
  have h2 : run (a+1+b) (loopCfg S) =
      fieldFrame (readyBank n
        (natField word.length ++ (word ++ suffix)) q' acc)
        (SourceListMachineFields.success word suffix) :=
    (run_add h1 b).trans hfield
  have hframeStart := field_to_frame n word suffix q' acc
  have h3 : run (a+1+b+1) (loopCfg S) =
      frameFrame (frameReadyBank n word suffix q' acc)
        (SourceOriginalPacketFraming.startCfg n word) :=
    (run_add h2 1).trans hframeStart
  obtain ⟨d, hd, c, hframe, hhalt, hout, hn, hw⟩ :=
    frame_embedded (frameReadyBank n word suffix q' acc) n word
  refine ⟨a+1+b+1+d, by omega, c, ?_, hhalt, hout, hn, hw⟩
  exact (run_add h3 d).trans hframe.symm

theorem canonical_item_to_frameStart (n : ℕ) (word suffix q q' acc : List Bool)
    (hdec : ProtocolBinaryCounter.subOne q = some q') :
    ∃ t ≤ (4*q.length+5) + 1 +
        20*(word.length+1)*(word.length.bits.length+1) + 1,
      run t (loopCfg (readyBank n
        (natField word.length ++ (word ++ suffix)) q acc)) =
        frameFrame (frameReadyBank n word suffix q' acc)
          (SourceOriginalPacketFraming.startCfg n word) := by
  let S := readyBank n (natField word.length ++ (word ++ suffix)) q acc
  have hstart : counterFrame S
      (SourceListMachineCounter.cfg (some (.inr .scan))
        SourceListMachineCounter.initialControl q []) = loopCfg S := by
    apply counterFrame_initial
    · exact readyBank_count n _ q acc
    · simp [S, readyBank]
  obtain ⟨a, ha, hcounter⟩ := counter_embedded S q
  rw [hdec] at hcounter
  rw [hstart] at hcounter
  have hfieldStart := counter_to_field n word suffix q q' acc
  have h1 : run (a+1) (loopCfg S) =
      fieldFrame (readyBank n
        (natField word.length ++ (word ++ suffix)) q' acc)
        (SourceListMachineFields.cfg (some (.inl .scan))
          SourceListMachineFields.initialControl
          {input := natField word.length ++ (word ++ suffix)}) :=
    (run_add hcounter 1).trans hfieldStart
  obtain ⟨b, hb, hfield⟩ :=
    field_embedded (readyBank n
      (natField word.length ++ (word ++ suffix)) q' acc) word suffix
  have h2 : run (a+1+b) (loopCfg S) =
      fieldFrame (readyBank n
        (natField word.length ++ (word ++ suffix)) q' acc)
        (SourceListMachineFields.success word suffix) :=
    (run_add h1 b).trans hfield
  have hframeStart := field_to_frame n word suffix q' acc
  exact ⟨a+1+b+1, by omega, (run_add h2 1).trans hframeStart⟩

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
