import Paper2.CappedLoopTerminalFrame
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Physical post-draw clearing of cells 1--8, preserving the
source tape on cell 0 and the result word on cell 9. -/

namespace Paper2.CappedLoop.Cleanup

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open scoped BigOperators

abbrev Label := Fin 10
abbrev Control := Unit × Option Bool

private theorem cmp_run_add {c d : TM2.Cfg (fun _ : Fin 10 => Bool)
    Comparator.Label Comparator.Control} {m : ℕ}
    (h : Comparator.run m c = d) (n : ℕ) :
    Comparator.run (m + n) c = Comparator.run n d := by
  rw [Nat.add_comm m n]
  simp only [Comparator.run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-- The full comparator loop has a canonical, rather than merely length-correct,
result word. Zero attempts give the empty abort word, including zero width. -/
theorem loop_exact (D R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) R)
    (suffix : List Bool) :
    ∃ t, ∃ v : Comparator.Control, ∃ ticket cap out r,
      ∃ tail : Paper2.CappedSampler.BitTape (Nat.clog 2 D) r,
      t ≤ R * Comparator.attemptBound D + 1 ∧
      Comparator.run t
        (Comparator.cfg (some .start) (none, false)
          (BlockTransfer.flatBitTape (Nat.clog 2 D) R tape ++ suffix)
          (List.replicate (Nat.clog 2 D) true) [] [] []
          (List.replicate R true) (List.replicate (D-1) true) [] [] []) =
        Comparator.cfg none v
          (BlockTransfer.flatBitTape (Nat.clog 2 D) r tail ++ suffix)
          (List.replicate (Nat.clog 2 D) true) [] [] ticket
          (List.replicate r true) (List.replicate (D-1) true) cap [] out ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧ r ≤ R ∧
      out = match (Paper2.CappedSampler.runBits D R tape).map Fin.val with
        | none => []
        | some q => true :: List.replicate q true := by
  induction R with
  | zero =>
      refine ⟨1, (none,false), [], [], [], 0, (), by simp, ?_,
        by simp, by simp, by simp, ?_⟩
      · simpa [BlockTransfer.flatBitTape] using
          Comparator.empty_attempts_halt suffix
            (List.replicate (Nat.clog 2 D) true)
            (List.replicate (D-1) true)
      · simp [Paper2.CappedSampler.runBits, Paper2.CappedSampler.run]
  | succ R ih =>
      let b := Nat.clog 2 D
      let n := D-1
      let block := List.ofFn tape.1
      let rest := BlockTransfer.flatBitTape b R tape.2 ++ suffix
      let q := EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block
      have hblen : block.length = b := List.length_ofFn
      have hv : q = (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val := by
        simpa [q, block, b, Paper2.CappedTicketMachine.ticketWord] using
          Paper2.CappedTicketMachine.bitsValue_ofFn tape.1
      by_cases hs : q ≤ n
      · obtain ⟨t,ticket,cap,v,ht,hr,hticket,hcap⟩ :=
          TerminalFrame.one_success_bank b n block rest hblen
            (List.replicate R true) hs
        refine ⟨t,(some true,v),ticket,cap,
          true :: List.replicate q true,R,tape.2,?_,?_,
          by omega,hcap,by omega,?_⟩
        · dsimp [Comparator.attemptBound,b,n] at *
          nlinarith
        · simpa [BlockTransfer.flatBitTape,block,rest,List.append_assoc] using hr
        · have hlt : (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [Comparator.runBits_succ, dif_pos hlt]
          simp
          simpa [q,b] using hv
      · have hf : n < q := by omega
        obtain ⟨t₁,ht₁,hr₁⟩ := Drain.one_reject_framed b n block rest hblen
          (List.replicate R true) hf
        obtain ⟨t₂,v,ticket,cap,out,r,tail,ht₂,hr₂,hticket,
          hcap,hrle,hout⟩ := ih tape.2
        refine ⟨t₁+t₂,v,ticket,cap,out,r,tail,?_,?_,
          hticket,hcap,by omega,?_⟩
        · dsimp [Comparator.attemptBound,b,n] at *
          nlinarith
        · have hr₁' : Comparator.run t₁
              (Comparator.cfg (some .start) (none,false)
                (BlockTransfer.flatBitTape b (R+1) tape ++ suffix)
                (List.replicate b true) [] [] []
                (List.replicate (R+1) true)
                (List.replicate n true) [] [] []) =
              Comparator.cfg (some .start) (none,false) rest
                (List.replicate b true) [] [] []
                (List.replicate R true) (List.replicate n true) [] [] [] := by
            simpa [BlockTransfer.flatBitTape,block,rest,
              List.append_assoc] using hr₁
          exact (cmp_run_add hr₁' t₂).trans
            (by simpa [rest,b,n] using hr₂)
        · have hnot : ¬ (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [Comparator.runBits_succ, dif_neg hnot]
          exact hout


theorem wrapped_exact (D R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) R)
    (suffix : List Bool) :
    ∃ t ticket cap out,
      t ≤ R * (Comparator.attemptBound D +
        (2 * Nat.clog 2 D + 3)) + 3 ∧
      ((advance Drain.wrappedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel Comparator.Label.start),
          ((none,false),(none,false)),
          Comparator.bank
            (BlockTransfer.flatBitTape (Nat.clog 2 D) R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] [] []
            (List.replicate R true) (List.replicate (D-1) true) [] [] []⟩ :
          TM2.Cfg (fun _ : Fin 10 => Bool)
            (BitMachineRawSequence.Label Comparator.Label Drain.Label)
            (BitMachineRawSequence.Control Comparator.Control Drain.Control)) =
        ⟨none, ((none,false),(none,false)),
          Comparator.bank suffix (List.replicate (Nat.clog 2 D) true)
            [] [] ticket [] (List.replicate (D-1) true) cap [] out⟩ ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧
      out = match (Paper2.CappedSampler.runBits D R tape).map Fin.val with
        | none => []
        | some q => true :: List.replicate q true := by
  obtain ⟨ta,v,ticket,cap,out,r,tail,hta,hra,hticket,hcap,hrle,hout⟩ :=
    loop_exact D R hD tape suffix
  let b := Nat.clog 2 D
  let n := D-1
  let S := Comparator.bank
    (BlockTransfer.flatBitTape b R tape ++ suffix)
    (List.replicate b true) [] [] []
    (List.replicate R true) (List.replicate n true) [] [] []
  let T := Comparator.bank
    (BlockTransfer.flatBitTape b r tail ++ suffix)
    (List.replicate b true) [] [] ticket (List.replicate r true)
    (List.replicate n true) cap [] out
  let U := Comparator.bank suffix (List.replicate b true) [] [] ticket []
    (List.replicate n true) cap [] out
  have ha : Comparator.run ta
      (⟨some Comparator.Label.start, (none,false), S⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Comparator.Label Comparator.Control) =
      ⟨none,v,T⟩ := by
    simpa [S,T,b,n,Comparator.cfg] using hra
  have hd := Drain.drain_bitTape b r tail suffix [] ticket
    (List.replicate n true) cap [] out
  have hb : Drain.run (r * (2*b+3)+1)
      (⟨some Drain.Label.start,(none,false),T⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Drain.Label Drain.Control) =
      ⟨none,(none,false),U⟩ := by
    simpa [T,U,Drain.cfg] using hd
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    Comparator.program Drain.program Comparator.Label.start Drain.Label.start
    (none,false) v (none,false) (none,false) S T U ta
    (r*(2*b+3)+1) ha hb
  refine ⟨t,ticket,cap,out,?_,?_,hticket,hcap,hout⟩
  · dsimp [b,n,Comparator.attemptBound] at *
    nlinarith
  · simpa [Drain.wrappedProgram,S,U,b,n] using hr


theorem wide_exact (D p R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D + p) R)
    (suffix : List Bool) :
    ∃ t ticket cap out,
      t ≤ R * (2 * (Nat.clog 2 D + p) + Nat.clog 2 D + 6) + 3 +
        (D - 1 + p + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance WideProjection.wideProgram)^[t])
        ⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel WideProjection.Label.start)),
          (((none,false),(none,false)),((none,false),(none,false))),
          WideProjection.bank
            (BlockTransfer.flatBitTape (Nat.clog 2 D + p) R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate p true) (List.replicate R true) [] []
            (List.replicate (D-1) true) []⟩ =
        ⟨none, (((none,false),(none,false)),((none,false),(none,false))),
          Comparator.bank suffix (List.replicate (Nat.clog 2 D) true)
            [] [] ticket [] (List.replicate (D-1) true) cap [] out⟩ ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧
      out = match (Paper2.CappedSampler.runWideBits D (Nat.clog 2 D + p) R
        (Nat.le_add_right (Nat.clog 2 D) p) tape).map Fin.val with
        | none => []
        | some q => true :: List.replicate q true := by
  let b := Nat.clog 2 D
  let n := D-1
  let prefTape := Paper2.CappedSampler.prefixBitTape
    (Nat.le_add_right b p) R tape
  let S := WideProjection.bank
    (BlockTransfer.flatBitTape (b+p) R tape ++ suffix)
    (List.replicate b true) [] [] (List.replicate p true)
    (List.replicate R true) [] [] (List.replicate n true) []
  let T := WideProjection.bank (WideProjection.compactTape b p R tape ++ suffix)
    (List.replicate b true) [] [] (List.replicate p true)
    (List.replicate R true) [] [] (List.replicate n true) []
  let U := Comparator.bank (BlockTransfer.flatBitTape b R prefTape ++ suffix)
    (List.replicate b true) [] [] [] (List.replicate R true)
    (List.replicate n true) [] [] []
  have hproj : WideProjection.run (R*(2*(b+p)+b+6)+3)
      (⟨some WideProjection.Label.start, (none,false), S⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) WideProjection.Label
          WideProjection.Control) = ⟨none,(none,false),T⟩ := by
    simpa [S,T,WideProjection.cfg] using
      WideProjection.project_wide_tape b p R tape suffix (List.replicate n true) []
  have hprep : WideProjection.Prepare.run (n+p+2)
      (⟨some WideProjection.Prepare.Label.moveCap,(none,false),T⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) WideProjection.Prepare.Label
          WideProjection.Control) = ⟨none,(none,false),U⟩ := by
    simpa [T,U,prefTape,WideProjection.compactTape_eq_source_prefix,
      WideProjection.Prepare.cfg,WideProjection.bank,Comparator.bank] using
      WideProjection.Prepare.prepare_bank n p
        (WideProjection.compactTape b p R tape ++ suffix)
        (List.replicate b true) (List.replicate R true)
  obtain ⟨t₁,ht₁,hr₁⟩ := BitMachineRawSequence.runs
    WideProjection.program WideProjection.Prepare.program
    WideProjection.Label.start WideProjection.Prepare.Label.moveCap
    (none,false) (none,false) (none,false) (none,false) S T U
    (R*(2*(b+p)+b+6)+3) (n+p+2) hproj hprep
  obtain ⟨t₂,ticket,cap,out,ht₂,hr₂,hticket,hcap,hout⟩ :=
    wrapped_exact D R hD prefTape suffix
  let V := Comparator.bank suffix (List.replicate b true) [] [] ticket []
    (List.replicate n true) cap [] out
  have hr₂' : ((advance Drain.wrappedProgram)^[t₂])
      (⟨some (BitMachineRawSequence.leftLabel Comparator.Label.start),
        ((none,false),(none,false)),U⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool)
          (BitMachineRawSequence.Label Comparator.Label Drain.Label)
          (BitMachineRawSequence.Control Comparator.Control Drain.Control)) =
      ⟨none,((none,false),(none,false)),V⟩ := by
    simpa [U,V,b,n,prefTape] using hr₂
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    WideProjection.projectionThenPrepare Drain.wrappedProgram
    (BitMachineRawSequence.leftLabel WideProjection.Label.start)
    (BitMachineRawSequence.leftLabel Comparator.Label.start)
    ((none,false),(none,false)) ((none,false),(none,false))
    ((none,false),(none,false)) ((none,false),(none,false))
    S U V t₁ t₂ (by simpa [WideProjection.projectionThenPrepare] using hr₁) hr₂'
  refine ⟨t,ticket,cap,out,?_,?_,hticket,hcap,?_⟩
  · dsimp [b,n] at *
    omega
  · simpa [WideProjection.wideProgram,S,V,b,n] using hr
  · simpa [Paper2.CappedSampler.runWideBits,prefTape] using hout


theorem source_draw_exact (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : Paper2.CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t ticket cap out,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance WideProjection.wideProgram)^[t])
        ⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel WideProjection.Label.start)),
          (((none,false),(none,false)),((none,false),(none,false))),
          WideProjection.bank
            (Paper2.RecursiveSamplingTape.writeTape B R (N+1) tape).val
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B-Nat.clog 2 D) true) (List.replicate R true)
            [] [] (List.replicate (D-1) true) []⟩ =
        ⟨none, (((none,false),(none,false)),((none,false),(none,false))),
          Comparator.bank
            (Paper2.RecursiveSamplingTape.writeTape B R N tape.2).val
            (List.replicate (Nat.clog 2 D) true) [] [] ticket []
            (List.replicate (D-1) true) cap [] out⟩ ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧
      out = match (Paper2.CappedSampler.runWideBits D B R hB tape.1).map Fin.val with
        | none => []
        | some q => true :: List.replicate q true := by
  obtain ⟨p,hp⟩ : ∃ p, B = Nat.clog 2 D + p :=
    ⟨B-Nat.clog 2 D, by omega⟩
  subst B
  simpa [Nat.add_sub_cancel_left,
    ← SerializationBridge.flatAdaptiveTape_eq_writeTape,
    WideProjection.flatAdaptiveTape] using
    wide_exact D p R hD tape.1 (WideProjection.flatAdaptiveTape (Nat.clog 2 D+p) R N tape.2)


def slot (i : Fin 8) : Fin 10 := ⟨i.val + 1, by omega⟩
def stage (i : Fin 9) : Label := ⟨i.val, by omega⟩
def done : Label := ⟨9, by omega⟩

def program (l : Label) : TM2.Stmt (fun _ : Fin 10 => Bool) Label Control :=
  if h : l.val < 8 then
    BitMachineClearBank.clearStep (slot ⟨l.val, h⟩) l
      ⟨l.val + 1, by omega⟩
  else if l.val = 8 then
    BitMachineClearBank.finishStep id done
  else .halt

private theorem stage_cast (i : Fin 8) : stage i.castSucc = ⟨i.val, by omega⟩ := rfl
private theorem stage_succ (i : Fin 8) : stage i.succ = ⟨i.val + 1, by omega⟩ := rfl

private theorem steps (i : Fin 8) :
    program (stage i.castSucc) =
      BitMachineClearBank.clearStep (slot i) (stage i.castSucc) (stage i.succ) := by
  simp only [program, stage_cast, stage_succ, dif_pos i.isLt]

private theorem finish : program (stage (Fin.last 8)) =
    BitMachineClearBank.finishStep id done := by
  simp [program, stage, Fin.last, done]

private theorem slot_inj : Function.Injective slot := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [slot] using this

theorem run_clear (S : Fin 10 → List Bool) :
    ((advance program)^[(∑ i : Fin 8, (S (slot i)).length) + 10])
      (⟨some (stage 0), ((), none), S⟩ : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) =
      ⟨none, ((), none), BitMachineClearBank.cleared slot S⟩ := by
  have h := BitMachineClearBank.clear_bank_run program id done 8 slot slot_inj
    stage steps finish () S
  have hhalt : advance program
      (⟨some done, ((), none), BitMachineClearBank.cleared slot S⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) =
      ⟨none, ((), none), BitMachineClearBank.cleared slot S⟩ := by
    simp [advance, TM2.step, TM2.stepAux, program, done]
  rw [show (∑ i : Fin 8, (S (slot i)).length) + 10 =
      ((∑ i : Fin 8, (S (slot i)).length) + 8 + 1) + 1 by omega,
    Function.iterate_succ_apply', h]
  exact hhalt

theorem cleared_zero (S : Fin 10 → List Bool) :
    BitMachineClearBank.cleared slot S 0 = S 0 := by
  apply BitMachineClearBank.cleared_foreign
  intro i h
  have := congrArg Fin.val h
  simp [slot] at this

theorem cleared_nine (S : Fin 10 → List Bool) :
    BitMachineClearBank.cleared slot S 9 = S 9 := by
  apply BitMachineClearBank.cleared_foreign
  intro i h
  have := congrArg Fin.val h
  simp [slot] at this
  omega

theorem clear_terminal (suffix : List Bool) (b n : ℕ)
    (ticket cap out : List Bool) :
    ((advance program)^[b + ticket.length + n + cap.length + 10])
      (⟨some (stage 0), ((), none),
        Comparator.bank suffix (List.replicate b true) [] [] ticket []
          (List.replicate n true) cap [] out⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) =
      ⟨none, ((), none),
        Comparator.bank suffix [] [] [] [] [] [] [] [] out⟩ := by
  let S := Comparator.bank suffix (List.replicate b true) [] [] ticket []
    (List.replicate n true) cap [] out
  have hsum : (∑ i : Fin 8, (S (slot i)).length) =
      b + ticket.length + n + cap.length := by
    simp [Fin.sum_univ_succ, S, slot, Comparator.bank]
    omega
  have hbank : BitMachineClearBank.cleared slot S =
      Comparator.bank suffix [] [] [] [] [] [] [] [] out := by
    funext k
    have hk : (∃ i : Fin 8, slot i = k) ↔ k ≠ 0 ∧ k ≠ 9 := by
      fin_cases k <;> decide
    simp only [BitMachineClearBank.cleared, hk]
    fin_cases k <;> simp [S, Comparator.bank]
  simpa [S, hsum, hbank] using run_clear S


def readyProgram :=
  BitMachineRawSequence.program WideProjection.wideProgram program (stage 0)
    (((none, false), (none, false)), ((none, false), (none, false))) ((), none)

/-- Source-serialized one-draw run followed by literal cell-by-cell clearing.
The result word on stack 9 and the complete next-draw suffix on stack 0 survive. -/
theorem source_draw_ready (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : Paper2.CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t out,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 +
        2 * Nat.clog 2 D + 2 * (D-1) + 11 ∧
      ((advance readyProgram)^[t])
        ⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel WideProjection.Label.start))),
          ((((none,false),(none,false)),((none,false),(none,false))), ((),none)),
          WideProjection.bank
            (Paper2.RecursiveSamplingTape.writeTape B R (N+1) tape).val
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B - Nat.clog 2 D) true) (List.replicate R true)
            [] [] (List.replicate (D-1) true) []⟩ =
        ⟨none,
          ((((none,false),(none,false)),((none,false),(none,false))), ((),none)),
          Comparator.bank
            (Paper2.RecursiveSamplingTape.writeTape B R N tape.2).val
            [] [] [] [] [] [] [] [] out⟩ ∧
      out = match (Paper2.CappedSampler.runWideBits D B R hB tape.1).map Fin.val with
        | none => []
        | some q => true :: List.replicate q true := by
  obtain ⟨ta,ticket,cap,out,hta,hra,hticket,hcap,hout⟩ :=
    source_draw_exact D B R N hD hB tape
  let b := Nat.clog 2 D
  let n := D-1
  let suffix := (Paper2.RecursiveSamplingTape.writeTape B R N tape.2).val
  let S := WideProjection.bank
    (Paper2.RecursiveSamplingTape.writeTape B R (N+1) tape).val
    (List.replicate b true) [] [] (List.replicate (B-b) true)
    (List.replicate R true) [] [] (List.replicate n true) []
  let T := Comparator.bank suffix (List.replicate b true) [] [] ticket []
    (List.replicate n true) cap [] out
  let U := Comparator.bank suffix [] [] [] [] [] [] [] [] out
  have ha : ((advance WideProjection.wideProgram)^[ta])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel WideProjection.Label.start)),
        (((none,false),(none,false)),((none,false),(none,false))), S⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) _ _) =
      ⟨none, (((none,false),(none,false)),((none,false),(none,false))), T⟩ := by
    simpa [S,T,suffix,b,n] using hra
  have hb : ((advance program)^[b + ticket.length + n + cap.length + 10])
      (⟨some (stage 0),((),none),T⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) =
      ⟨none,((),none),U⟩ := by
    simpa [T,U,b,n,suffix] using clear_terminal suffix b n ticket cap out
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    WideProjection.wideProgram program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel WideProjection.Label.start))
    (stage 0)
    (((none,false),(none,false)),((none,false),(none,false)))
    (((none,false),(none,false)),((none,false),(none,false)))
    ((),none) ((),none) S T U ta
    (b + ticket.length + n + cap.length + 10) ha hb
  refine ⟨t,out,?_,?_,hout⟩
  · dsimp [b,n] at *
    omega
  · simpa [readyProgram,S,U,suffix,b,n] using hr


end Paper2.CappedLoop.Cleanup
