import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerOne

/-! Transfer and cleanup after one framed packet has been physically emitted. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication
open SourceOriginalListPacketizerCleanupRun

noncomputable section

theorem afterFrame_step (v : SourceOriginalPacketFraming.Control)
    (S : Stack → List Bool) :
    advance program
      ⟨some (adminLabel .afterFrame),frameControl v,S⟩ =
      ⟨some (adminLabel .emit),frameControl v,S⟩ := by
  simp [advance, adminLabel, program, TM2.step, TM2.stepAux]

theorem emit_program : program (adminLabel .emit) =
    BitMachineBroadcast.scanStep
      (.inl SourceOriginalPacketFraming.outputStack) (.inr 4)
      (adminLabel .emit) (adminLabel .clearFieldCount) := rfl

theorem clearFieldCount_program : program (adminLabel .clearFieldCount) =
    BitMachineClearBank.clearStep (.inr 8)
      (adminLabel .clearFieldCount) (adminLabel (.clearFrame 0)) := rfl

theorem emit_source_ne_acc :
    (.inl SourceOriginalPacketFraming.outputStack : Stack) ≠ .inr 4 :=
  Sum.inl_ne_inr

theorem contents_eq_self (S : Stack → List Bool) (a b : Stack) (hab : a ≠ b) :
    BitMachineBroadcast.contents a b S (S a) (S b) = S := by
  funext k
  by_cases ha : k = a
  · subst k
    simp [BitMachineBroadcast.contents, Function.update_of_ne hab]
  · by_cases hb : k = b
    · subst k
      simp [BitMachineBroadcast.contents, ha]
    · simp [BitMachineBroadcast.contents, ha, hb]

theorem emit_run (v : PreControl) (S : Stack → List Bool) :
    run ((S (.inl SourceOriginalPacketFraming.outputStack)).length+1)
      ⟨some (adminLabel .emit),(v,none),S⟩ =
    ⟨some (adminLabel .clearFieldCount),(v,none),
      BitMachineBroadcast.contents
        (.inl SourceOriginalPacketFraming.outputStack) (.inr 4) S []
        ((S (.inl SourceOriginalPacketFraming.outputStack)).reverse ++ S (.inr 4))⟩ := by
  let a : Stack := .inl SourceOriginalPacketFraming.outputStack
  let b : Stack := .inr 4
  let bits := S a
  let saved := S b
  have hrun := BitMachineBroadcast.scan_run program a b emit_source_ne_acc
    (adminLabel .emit) (adminLabel .clearFieldCount) emit_program
    v none bits saved S
  rw [contents_eq_self S a b emit_source_ne_acc] at hrun
  exact hrun

theorem clearFieldCount_run (v : PreControl) (S : Stack → List Bool) :
    run ((S (.inr 8)).length+1)
      ⟨some (adminLabel .clearFieldCount),(v,none),S⟩ =
    ⟨some (adminLabel (.clearFrame 0)),(v,none),
      Function.update S (.inr 8) []⟩ := by
  exact BitMachineClearBank.clear_one_run program (.inr 8)
    (adminLabel .clearFieldCount) (adminLabel (.clearFrame 0))
    clearFieldCount_program v S

def postFrameBank (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) : Stack → List Bool :=
  BitMachineStackEmbedding.bank frameStack
    (frameReadyBank n word suffix q acc) c.stk

theorem postFrame_local (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) (k : FrameStack) :
    postFrameBank n word suffix q acc c (.inl k) = c.stk k := by
  exact BitMachineStackEmbedding.bank_at frameStack _ _ k

theorem postFrame_aux (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) (k : Fin 10) :
    postFrameBank n word suffix q acc c (.inr k) =
      frameReadyBank n word suffix q acc (.inr k) := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i,hi⟩
  exact Sum.inl_ne_inr hi

def emittedBank (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) : Stack → List Bool :=
  BitMachineBroadcast.contents
    (.inl SourceOriginalPacketFraming.outputStack) (.inr 4)
    (postFrameBank n word suffix q acc c) []
    ((SourceOriginalPacketFraming.answer n word).reverse ++ acc)

theorem emittedBank_eq (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config)
    (hout : c.stk SourceOriginalPacketFraming.outputStack =
      SourceOriginalPacketFraming.answer n word) :
    BitMachineBroadcast.contents
      (.inl SourceOriginalPacketFraming.outputStack) (.inr 4)
      (postFrameBank n word suffix q acc c) []
      ((postFrameBank n word suffix q acc c
        (.inl SourceOriginalPacketFraming.outputStack)).reverse ++
        postFrameBank n word suffix q acc c (.inr 4)) =
      emittedBank n word suffix q acc c := by
  rw [postFrame_local, hout, postFrame_aux]
  rfl

theorem emitted_acc (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) :
    emittedBank n word suffix q acc c (.inr 4) =
      (SourceOriginalPacketFraming.answer n word).reverse ++ acc := by
  simp [emittedBank, BitMachineBroadcast.contents]

theorem emitted_aux_other (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) (k : Fin 10) (hk : k ≠ 4) :
    emittedBank n word suffix q acc c (.inr k) =
      frameReadyBank n word suffix q acc (.inr k) := by
  simp [emittedBank, BitMachineBroadcast.contents, hk, postFrame_aux]

theorem emitted_n (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config)
    (hn : c.stk SourceOriginalPacketFraming.nStack = List.replicate n true) :
    emittedBank n word suffix q acc c
      (.inl SourceOriginalPacketFraming.nStack) = List.replicate n true := by
  have hne : SourceOriginalPacketFraming.nStack ≠
      SourceOriginalPacketFraming.outputStack := by
    unfold SourceOriginalPacketFraming.nStack SourceOriginalPacketFraming.outputStack
    exact Sum.inl_ne_inr
  simp [emittedBank, BitMachineBroadcast.contents, hne, postFrame_local, hn]

def itemCleanBank (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) : Stack → List Bool :=
  SourceOriginalListPacketizerCleanup.clearedExcept
    SourceOriginalListPacketizerCleanupRun.frameBank
    (.inl SourceOriginalPacketFraming.nStack)
    (Function.update (emittedBank n word suffix q acc c) (.inr 8) [])

theorem itemCleanBank_eq_ready (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config)
    (hn : c.stk SourceOriginalPacketFraming.nStack = List.replicate n true) :
    itemCleanBank n word suffix q acc c =
      readyBank n suffix q
        ((SourceOriginalPacketFraming.answer n word).reverse ++ acc) := by
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = SourceOriginalPacketFraming.nStack
      · subst k
        rw [itemCleanBank, SourceOriginalListPacketizerCleanupRun.cleared_n]
        simp [Function.update_of_ne, emitted_n n word suffix q acc c hn,
          readyBank]
      · rw [itemCleanBank,
          SourceOriginalListPacketizerCleanupRun.cleared_other_frame _ k hk]
        exact (readyBank_other_frame n suffix q _ k hk).symm
  | inr k =>
      rw [itemCleanBank, SourceOriginalListPacketizerCleanupRun.cleared_aux]
      fin_cases k <;> simp [readyBank, Function.update_apply,
        emitted_aux_other, emitted_acc, frameReadyBank]

def cleanupTime (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config) : ℕ :=
  (∑ i : Fin (Fintype.card FrameStack),
    if SourceOriginalListPacketizerCleanupRun.frameBank i =
        .inl SourceOriginalPacketFraming.nStack then 0
    else ((Function.update (emittedBank n word suffix q acc c) (.inr 8) [])
      (SourceOriginalListPacketizerCleanupRun.frameBank i)).length) +
    Fintype.card FrameStack + 1

theorem frame_to_loop (n : ℕ) (word suffix q acc : List Bool)
    (c : SourceOriginalPacketFraming.Config)
    (hhalt : c.l = none)
    (hout : c.stk SourceOriginalPacketFraming.outputStack =
      SourceOriginalPacketFraming.answer n word)
    (hn : c.stk SourceOriginalPacketFraming.nStack = List.replicate n true) :
    run (1 + (SourceOriginalPacketFraming.answer n word).length+1 +
      (word.length+1) + cleanupTime n word suffix q acc c)
      (frameFrame (frameReadyBank n word suffix q acc) c) =
      loopCfg (readyBank n suffix q
        ((SourceOriginalPacketFraming.answer n word).reverse ++ acc)) := by
  let S := postFrameBank n word suffix q acc c
  have hcfg : frameFrame (frameReadyBank n word suffix q acc) c =
      ⟨some (adminLabel .afterFrame),frameControl c.var,S⟩ := by
    unfold frameFrame BitMachineStackEmbedding.cfg
      BitMachineStackEmbedding.stackCfg
    simp [BitMachineInline.cfg, hhalt, S, postFrameBank]
  have h1 : run 1 (frameFrame (frameReadyBank n word suffix q acc) c) =
      ⟨some (adminLabel .emit),frameControl c.var,S⟩ := by
    rw [hcfg, run_succ (afterFrame_step c.var S) 0]
    rfl
  have h2' := emit_run (frameControl c.var).1 S
  change run (S (.inl SourceOriginalPacketFraming.outputStack)).length.succ
    ⟨some (adminLabel .emit),frameControl c.var,S⟩ = _ at h2'
  have hSout : S (.inl SourceOriginalPacketFraming.outputStack) =
      SourceOriginalPacketFraming.answer n word :=
    (postFrame_local n word suffix q acc c _).trans hout
  rw [hSout] at h2'
  have hSacc : S (.inr 4) = acc := by
    change postFrameBank n word suffix q acc c (.inr 4) = acc
    rw [postFrame_aux]
    rfl
  rw [hSacc] at h2'
  change run _ _ = ⟨some (adminLabel .clearFieldCount),frameControl c.var,
    emittedBank n word suffix q acc c⟩ at h2'
  have h2 : run (1 + ((SourceOriginalPacketFraming.answer n word).length+1))
      (frameFrame (frameReadyBank n word suffix q acc) c) =
      ⟨some (adminLabel .clearFieldCount),frameControl c.var,
        emittedBank n word suffix q acc c⟩ :=
    (run_add h1 _).trans h2'
  have hcount : (emittedBank n word suffix q acc c (.inr 8)).length =
      word.length := by
    rw [emitted_aux_other n word suffix q acc c 8 (by decide)]
    simp [frameReadyBank]
  have h3' := clearFieldCount_run (frameControl c.var).1
    (emittedBank n word suffix q acc c)
  rw [hcount] at h3'
  have h3 : run (1 + ((SourceOriginalPacketFraming.answer n word).length+1) +
      (word.length+1))
      (frameFrame (frameReadyBank n word suffix q acc) c) =
      ⟨some (adminLabel (.clearFrame 0)),frameControl c.var,
        Function.update (emittedBank n word suffix q acc c) (.inr 8) []⟩ :=
    (run_add h2 _).trans h3'
  have h4' := SourceOriginalListPacketizerCleanupRun.clearFrame_run
    (frameControl c.var).1
    (Function.update (emittedBank n word suffix q acc c) (.inr 8) [])
  change run (cleanupTime n word suffix q acc c) _ = _ at h4'
  have h4 : run (1 + ((SourceOriginalPacketFraming.answer n word).length+1) +
      (word.length+1) + cleanupTime n word suffix q acc c)
      (frameFrame (frameReadyBank n word suffix q acc) c) =
      ⟨some (counterLabel (.inr .scan)),
        counterControl SourceListMachineCounter.initialControl,
        itemCleanBank n word suffix q acc c⟩ :=
    (run_add h3 _).trans h4'
  change run (1 + ((SourceOriginalPacketFraming.answer n word).length+1) +
    (word.length+1) + cleanupTime n word suffix q acc c)
    (frameFrame (frameReadyBank n word suffix q acc) c) = _
  rw [h4, itemCleanBank_eq_ready n word suffix q acc c hn]
  rfl

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
