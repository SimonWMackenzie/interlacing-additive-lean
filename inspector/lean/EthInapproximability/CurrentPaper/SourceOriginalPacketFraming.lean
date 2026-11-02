import EthInapproximability.CurrentPaper.SourceOriginalPacketWriter
import EthInapproximability.CurrentPaper.SourceListMachineWriter
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Framing one physically written original-size packet

Source: locked v8 Section 8, encoded source-list packets. The five-bank
writer leaves the original unary `n` in bank zero and a two-field packet in
bank four. A fixed sequential controller then transfers that packet into
the fixed binary-length framing machine. Every transfer and framing step is
charged. The outer list loop is deliberately not constructed here.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketFraming

open Turing BitMachineEncoding BitMachineComposition

noncomputable def writerMachine : BitMachine.Machine :=
  ofFinite (1 : Fin 5) (4 : Fin 5) SourceOriginalPacketWriter.Label.scanN
    (none : SourceOriginalPacketWriter.Control) SourceOriginalPacketWriter.program

noncomputable def frameMachine : BitMachine.Machine :=
  SourceListMachineWriter.framingMachine true

abbrev Stack := BitMachineComposition.Stack writerMachine frameMachine
abbrev Label := BitMachineComposition.Label writerMachine frameMachine
abbrev Control := BitMachineComposition.Control writerMachine frameMachine
abbrev Config := BitMachineComposition.Config writerMachine frameMachine

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineComposition.program writerMachine frameMachine

def packet (n : ℕ) (word : List Bool) : List Bool :=
  SourceOriginalBranchPackets.packet n word

def answer (n : ℕ) (word : List Bool) : List Bool :=
  EncodedCommunication.natField (packet n word).length ++ packet n word

noncomputable def writerStart (n : ℕ) (word : List Bool) : writerMachine.Config :=
  renameCfg (Fintype.equivFin SourceOriginalPacketWriter.Stack)
    (Fintype.equivFin SourceOriginalPacketWriter.Label)
    (Fintype.equivFin SourceOriginalPacketWriter.Control)
    (SourceOriginalPacketWriter.cfg (some .scanN) none
      (List.replicate n true) word [] [] [])

noncomputable def writerEnd (n : ℕ) (word : List Bool) : writerMachine.Config :=
  renameCfg (Fintype.equivFin SourceOriginalPacketWriter.Stack)
    (Fintype.equivFin SourceOriginalPacketWriter.Label)
    (Fintype.equivFin SourceOriginalPacketWriter.Control)
    (SourceOriginalPacketWriter.cfg none none
      (List.replicate n true) [] [] [] (packet n word))

noncomputable def startCfg (n : ℕ) (word : List Bool) : Config :=
  BitMachineComposition.leftCfg writerMachine frameMachine (writerStart n word)

noncomputable def nStack : Stack :=
  .inl (Fintype.equivFin SourceOriginalPacketWriter.Stack 0)

noncomputable def wordStack : Stack :=
  .inl (Fintype.equivFin SourceOriginalPacketWriter.Stack 1)

noncomputable def outputStack : Stack := .inr (.inl frameMachine.output)

noncomputable def startLabel : Label := .inl writerMachine.start

noncomputable def initialControl : Control :=
  (writerMachine.initial, frameMachine.initial, none)

theorem nStack_ne_wordStack : nStack ≠ wordStack := by
  change (Sum.inl ((Fintype.equivFin (Fin 5)) 0) : Stack) ≠
    Sum.inl ((Fintype.equivFin (Fin 5)) 1)
  exact fun h => (by decide : (0 : Fin 5) ≠ 1)
    ((Fintype.equivFin (Fin 5)).injective (Sum.inl.inj h))

theorem wordStack_ne_outputStack : wordStack ≠ outputStack := by
  exact Sum.inl_ne_inr

theorem startCfg_label (n : ℕ) (word : List Bool) :
    (startCfg n word).l = some startLabel := by
  rfl

theorem startCfg_control (n : ℕ) (word : List Bool) :
    (startCfg n word).var = initialControl := by
  rfl

theorem startCfg_left_bank (n : ℕ) (word : List Bool) (i : Fin 5) :
    (startCfg n word).stk
      (.inl (Fintype.equivFin SourceOriginalPacketWriter.Stack i)) =
      ![List.replicate n true,word,[],[],[]] i := by
  change (SourceOriginalPacketWriter.cfg (some .scanN) none
    (List.replicate n true) word [] [] []).stk
    ((Fintype.equivFin (Fin 5)).symm ((Fintype.equivFin (Fin 5)) i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem startCfg_foreign_empty (n : ℕ) (word : List Bool)
    (k : Fin frameMachine.stackCount ⊕ Unit) :
    (startCfg n word).stk (.inr k) = [] := by
  rfl

theorem startCfg_bank (n : ℕ) (word : List Bool) (k : Stack) :
    (startCfg n word).stk k =
      if k = nStack then List.replicate n true
      else if k = wordStack then word else [] := by
  rcases k with k | k
  · let e := Fintype.equivFin SourceOriginalPacketWriter.Stack
    let i := e.symm k
    have hk : k = e i := (e.apply_symm_apply k).symm
    rw [hk]
    rw [startCfg_left_bank]
    simp only [nStack, wordStack, Sum.inl.injEq]
    change ![List.replicate n true,word,[],[],[]] i =
      if e i = e 0 then List.replicate n true
      else if e i = e 1 then word else []
    simpa only [e.injective.eq_iff] using
      (show ∀ j : Fin 5,
        ![List.replicate n true,word,[],[],[]] j =
          if j = 0 then List.replicate n true
          else if j = 1 then word else [] from by
        intro j
        fin_cases j <;> rfl) i
  · rw [startCfg_foreign_empty]
    simp [nStack, wordStack]

def writerTime (n : ℕ) (word : List Bool) : ℕ :=
  4*n + 3*word.length + 6

noncomputable def framingTime (n : ℕ) (word : List Bool) : ℕ :=
  (UnaryBinaryEncoding.coefficient+7)*((packet n word).length+1)^2

noncomputable def totalTime (n : ℕ) (word : List Bool) : ℕ :=
  writerTime n word + 2*(packet n word).length+2 + framingTime n word

theorem writer_run (n : ℕ) (word : List Bool) :
    writerMachine.run (writerTime n word) (writerStart n word) =
      writerEnd n word := by
  simpa only [writerTime, writerStart, writerEnd, writerMachine, packet,
    BitMachineEncoding.ofFinite_run] using
    (BitMachineEncoding.ofFinite_run
      (1 : Fin 5) (4 : Fin 5) SourceOriginalPacketWriter.Label.scanN
      (none : SourceOriginalPacketWriter.Control)
      SourceOriginalPacketWriter.program
      (SourceOriginalPacketWriter.cfg (some .scanN) none
        (List.replicate n true) word [] [] [])
      (4*n+3*word.length+6)).trans
      (congrArg
        (renameCfg (Fintype.equivFin SourceOriginalPacketWriter.Stack)
          (Fintype.equivFin SourceOriginalPacketWriter.Label)
          (Fintype.equivFin SourceOriginalPacketWriter.Control))
        (SourceOriginalPacketWriter.unary_packet_run n word))

theorem writerEnd_halted (n : ℕ) (word : List Bool) :
    (writerEnd n word).l = none := rfl

theorem writerEnd_output (n : ℕ) (word : List Bool) :
    (writerEnd n word).stk writerMachine.output = packet n word := by
  change (SourceOriginalPacketWriter.cfg none none
    (List.replicate n true) [] [] [] (packet n word)).stk
    ((Fintype.equivFin (Fin 5)).symm ((Fintype.equivFin (Fin 5)) 4)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem writerEnd_unary (n : ℕ) (word : List Bool) :
    (writerEnd n word).stk (Fintype.equivFin SourceOriginalPacketWriter.Stack 0) =
      List.replicate n true := by
  change (SourceOriginalPacketWriter.cfg none none
    (List.replicate n true) [] [] [] (packet n word)).stk
    ((Fintype.equivFin (Fin 5)).symm ((Fintype.equivFin (Fin 5)) 0)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem writerEnd_branch (n : ℕ) (word : List Bool) :
    (writerEnd n word).stk (Fintype.equivFin SourceOriginalPacketWriter.Stack 1) =
      [] := by
  change (SourceOriginalPacketWriter.cfg none none
    (List.replicate n true) [] [] [] (packet n word)).stk
    ((Fintype.equivFin (Fin 5)).symm ((Fintype.equivFin (Fin 5)) 1)) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem rightCfg_left_bank (A B : BitMachine.Machine)
    (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (d : B.Config) (k : Fin A.stackCount) :
    (BitMachineComposition.rightCfg A B v S d).stk (.inl k) = S k := by
  simp [BitMachineComposition.rightCfg, renameCfg, liftCfg,
    BitMachineComposition.stackSwap]

private theorem rightCfg_right_bank (A B : BitMachine.Machine)
    (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (d : B.Config) (k : Fin B.stackCount) :
    (BitMachineComposition.rightCfg A B v S d).stk (.inr (.inl k)) = d.stk k := by
  simp [BitMachineComposition.rightCfg, renameCfg, liftCfg,
    BitMachineComposition.stackSwap]

/-- The local controller preserves the unary original size and physically
emits a length-framed ordinary word. Its state also identifies the entire
post-framing right-machine configuration, so downstream cleanup can be
charged to its actual bank contents. -/
theorem framed_run (n : ℕ) (word : List Bool) :
    ∃ t ≤ totalTime n word, ∃ b ≤ framingTime n word, ∃ c : Config,
      ((advance program)^[t]) (startCfg n word) = c ∧
      c = BitMachineComposition.rightCfg writerMachine frameMachine
        (writerEnd n word).var
        (Function.update (writerEnd n word).stk writerMachine.output [])
        (frameMachine.run b (frameMachine.init (packet n word))) ∧
      c.l = none ∧ c.stk outputStack = answer n word ∧
      c.stk nStack = List.replicate n true ∧ c.stk wordStack = [] := by
  let A := writerMachine
  let B := frameMachine
  let q := packet n word
  obtain ⟨a, ha, hah, hae, hafirst⟩ :=
    BitMachineSubroutine.first_halt_cfg A.program (writerStart n word)
      (writerTime n word) (by
        change (A.run (writerTime n word) (writerStart n word)).l = none
        rw [writer_run]
        rfl)
  have hae' : A.run a (writerStart n word) = writerEnd n word := by
    change A.run a (writerStart n word) =
      A.run (writerTime n word) (writerStart n word) at hae
    rw [writer_run] at hae
    exact hae
  have hleft := BitMachineComposition.left_run A B (writerStart n word) a
    (by simpa only [BitMachine.Machine.run] using hafirst)
  have htransfer := BitMachineComposition.transfer_run A B
    (writerEnd n word) (writerEnd_halted n word)
  have hf := SourceListMachineWriter.outputs true q
  change B.OutputsWithin q (answer n word) (framingTime n word) at hf
  obtain ⟨b, hb, hbh, hbo⟩ := hf
  let d := B.run b (B.init q)
  have hright := BitMachineComposition.right_run A B
    (writerEnd n word).var
    (Function.update (writerEnd n word).stk A.output []) (B.init q) b
  let c := BitMachineComposition.rightCfg A B (writerEnd n word).var
    (Function.update (writerEnd n word).stk A.output []) d
  have hr : ((advance program)^[a + 2*q.length+2+b]) (startCfg n word) = c := by
    have hq : (writerEnd n word).stk A.output = q :=
      writerEnd_output n word
    change ((advance (BitMachineComposition.program A B))^[a + 2*q.length+2+b])
      (BitMachineComposition.leftCfg A B (writerStart n word)) = c
    rw [show a + 2*q.length+2+b =
      b + ((q.length+1+(q.length+1)) + a) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply, hleft, hae']
    rw [← hq, htransfer, hq, hright]
  refine ⟨a + 2*q.length+2+b, by dsimp [totalTime, q]; omega,
    b, hb, c, hr, rfl, ?_, ?_, ?_, ?_⟩
  · have hdh : d.l = none := hbh
    simp only [c, BitMachineComposition.rightCfg, renameCfg, liftCfg,
      hdh, Option.map_none]
  · simpa only [c, outputStack, rightCfg_right_bank, d] using hbo
  · rw [show c.stk nStack =
      (Function.update (writerEnd n word).stk A.output [])
        (Fintype.equivFin SourceOriginalPacketWriter.Stack 0) from
        rightCfg_left_bank A B _ _ _ _]
    rw [Function.update_of_ne]
    · exact writerEnd_unary n word
    · change (Fintype.equivFin (Fin 5)) 0 ≠ (Fintype.equivFin (Fin 5)) 4
      exact (Fintype.equivFin (Fin 5)).injective.ne (by decide)
  · rw [show c.stk wordStack =
      (Function.update (writerEnd n word).stk A.output [])
        (Fintype.equivFin SourceOriginalPacketWriter.Stack 1) from
        rightCfg_left_bank A B _ _ _ _]
    rw [Function.update_of_ne]
    · exact writerEnd_branch n word
    · change (Fintype.equivFin (Fin 5)) 1 ≠ (Fintype.equivFin (Fin 5)) 4
      exact (Fintype.equivFin (Fin 5)).injective.ne (by decide)

/-- A uniform bound for every private bank of the physical length-framing
machine at the final state. Together with the exact `rightCfg` decomposition
in `framed_run`, this charges an outer cleanup loop without assuming its
scratch stacks are empty. -/
theorem frame_residual_length (n : ℕ) (word : List Bool)
    (b : ℕ) (hb : b ≤ framingTime n word)
    (k : Fin frameMachine.stackCount) :
    ((frameMachine.run b (frameMachine.init (packet n word))).stk k).length ≤
      (packet n word).length +
        framingTime n word * frameMachine.pushBound := by
  have hr := BitMachine.run_length frameMachine
    (frameMachine.init (packet n word)) k b
  have hi : ((frameMachine.init (packet n word)).stk k).length ≤
      (packet n word).length := by
    simp only [BitMachine.Machine.init]
    split <;> simp
  have hm := Nat.mul_le_mul_right frameMachine.pushBound hb
  omega

noncomputable def embeddedProgram {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) : Label → TM2.Stmt (fun _ : K => Bool) Label Control :=
  fun l => BitMachineStackEmbedding.stmt ι id id id none (program l)

/-- The exact local computation can be installed at any injectively chosen
ambient stack locations. Every unselected stack remains the supplied
`foreign` word throughout, even if those words are nonempty. -/
theorem embedded_framed_run {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (foreign : K → List Bool)
    (n : ℕ) (word : List Bool) :
    ∃ t ≤ totalTime n word, ∃ b ≤ framingTime n word, ∃ c : Config,
      ((advance (embeddedProgram ι))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none (startCfg n word)) =
          BitMachineStackEmbedding.cfg ι foreign id id none c ∧
      c = BitMachineComposition.rightCfg writerMachine frameMachine
        (writerEnd n word).var
        (Function.update (writerEnd n word).stk writerMachine.output [])
        (frameMachine.run b (frameMachine.init (packet n word))) ∧
      c.l = none ∧ c.stk outputStack = answer n word ∧
      c.stk nStack = List.replicate n true ∧ c.stk wordStack = [] := by
  obtain ⟨u, hu, b, hb, c, hc, he, hh, ho, hn, hw⟩ := framed_run n word
  have hhalt : (((advance program)^[u]) (startCfg n word)).l = none := by
    rw [hc]
    exact hh
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs
    ι foreign id id id (fun _ => rfl) none program
    (embeddedProgram ι) (fun _ => rfl) (startCfg n word) u hhalt
  refine ⟨t, ht.trans hu, b, hb, c, ?_, he, hh, ho, hn, hw⟩
  simpa only [hc] using hr

end EthInapproximability.CurrentPaper.SourceOriginalPacketFraming
