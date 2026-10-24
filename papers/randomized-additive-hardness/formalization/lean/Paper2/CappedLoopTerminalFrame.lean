import Paper2.CappedLoopSerializationBridge

/-!
Scratch terminal-bank strengthening for the locked Paper 2 v12 one-draw
machine. The frozen drain/wide/serialization modules are not modified.
-/

namespace Paper2.CappedLoop.TerminalFrame

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding

private theorem cmp_run_add {c d : TM2.Cfg (fun _ : Fin 10 => Bool)
    Comparator.Label Comparator.Control} {m : ℕ}
    (h : Comparator.run m c = d) (n : ℕ) :
    Comparator.run (m + n) c = Comparator.run n d := by
  rw [Nat.add_comm m n]
  simp only [Comparator.run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-- A successful framed attempt exposes every residual physical stack and
the two bounded scratch lengths, not only the ticket observation. -/
theorem one_success_bank (b n : ℕ) (block rest : List Bool)
    (hb : block.length = b) (attempts : List Bool)
    (hs : EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block ≤ n) :
    ∃ t ticket cap, ∃ v : Bool,
      t ≤ 3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) + 1 ∧
      Comparator.run t
        (Comparator.cfg (some .start) (none, false) (block ++ rest)
          (List.replicate b true) [] [] [] (true :: attempts)
          (List.replicate n true) [] [] []) =
        Comparator.cfg none (some true, v) rest
          (List.replicate b true) [] [] ticket attempts
          (List.replicate n true) cap []
          (true :: List.replicate
            (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block)
            true) ∧
      ticket.length = b ∧ cap.length ≤ n := by
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    Drain.one_complete_framed b n block rest hb attempts
  let saved := List.replicate n true
  let base := Comparator.bank rest (List.replicate b true) [] [] block attempts
    saved saved [] []
  have hout' : c.stk 3 = true :: List.replicate
      (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block) true := by
    rw [hout]
    simp [EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result, hs]
  have hcfg : Comparator.injectCmp base c =
      Comparator.cfg (some .decision) c.var rest (List.replicate b true)
        [] [] (c.stk 0) attempts saved (c.stk 1) []
        (true :: List.replicate
          (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue block)
          true) := by
    rw [Comparator.cmp_endpoint_cfg rest (List.replicate b true) [] [] block
      attempts saved saved [] [] c hhalt hwork, hout']
  refine ⟨t+1, c.stk 0, c.stk 1, c.var.2, by omega, ?_, hlen, hcaplen⟩
  rw [cmp_run_add hr 1, hcfg]
  simp [saved, Comparator.run, advance, TM2.step, TM2.stepAux,
    Comparator.program, Comparator.cfg, Comparator.bank]


/-- Full terminal bank before the acceptance drain: the permanent cap is
unchanged, width is restored, work stacks 2,3,8 are empty, and residual
ticket/cap stacks have charged length bounds. -/
theorem loop_bank (D R : ℕ) (hD : 0 < D)
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
      (if out.head? = some true then some out.tail.length else none) =
        (Paper2.CappedSampler.runBits D R tape).map Fin.val := by
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
      · obtain ⟨t, ticket, cap, v, ht, hr, hticket, hcap⟩ :=
          one_success_bank b n block rest hblen (List.replicate R true) hs
        refine ⟨t, (some true,v), ticket, cap,
          true :: List.replicate q true, R, tape.2,
          ?_, ?_, by omega, hcap, by omega, ?_⟩
        · dsimp [Comparator.attemptBound, b, n] at *
          nlinarith
        · simpa [BlockTransfer.flatBitTape, block, rest, List.append_assoc]
            using hr
        · have hlt : (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [Comparator.runBits_succ, dif_pos hlt]
          simp
          simpa [q, b] using hv
      · have hf : n < q := by omega
        obtain ⟨t₁, ht₁, hr₁⟩ := Drain.one_reject_framed b n block rest
          hblen (List.replicate R true) hf
        obtain ⟨t₂, v, ticket, cap, out, r, tail, ht₂, hr₂, hticket,
          hcap, hrle, hout⟩ := ih tape.2
        refine ⟨t₁+t₂, v, ticket, cap, out, r, tail, ?_, ?_,
          hticket, hcap, by omega, ?_⟩
        · dsimp [Comparator.attemptBound, b, n] at *
          nlinarith
        · have hr₁' : Comparator.run t₁
              (Comparator.cfg (some .start) (none, false)
                (BlockTransfer.flatBitTape b (R+1) tape ++ suffix)
                (List.replicate b true) [] [] []
                (List.replicate (R+1) true)
                (List.replicate n true) [] [] []) =
              Comparator.cfg (some .start) (none,false) rest
                (List.replicate b true) [] [] []
                (List.replicate R true) (List.replicate n true) [] [] [] := by
            simpa [BlockTransfer.flatBitTape, block, rest,
              List.append_assoc] using hr₁
          exact (cmp_run_add hr₁' t₂).trans
            (by simpa [rest, b, n] using hr₂)
        · have hnot : ¬ (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [Comparator.runBits_succ, dif_neg hnot]
          exact hout


/-- After the literal acceptance drain, the entire ten-stack bank has a
bounded shape. The accepted output remains on stack 9; the ticket and cap
work stacks are left in place for a separately charged next-draw cleanup. -/
theorem wrapped_bank (D R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) R)
    (suffix : List Bool) :
    ∃ t ticket cap out,
      t ≤ R * (Comparator.attemptBound D +
        (2 * Nat.clog 2 D + 3)) + 3 ∧
      ((advance Drain.wrappedProgram)^[t])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            Comparator.Label.start),
          ((none,false),(none,false)),
          Comparator.bank
            (BlockTransfer.flatBitTape (Nat.clog 2 D) R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] [] []
            (List.replicate R true) (List.replicate (D-1) true) [] [] []⟩ :
          TM2.Cfg (fun _ : Fin 10 => Bool)
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.Label
              Comparator.Label Drain.Label)
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.Control
              Comparator.Control Drain.Control)) =
        ⟨none, ((none,false),(none,false)),
          Comparator.bank suffix (List.replicate (Nat.clog 2 D) true)
            [] [] ticket [] (List.replicate (D-1) true) cap [] out⟩ ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧
      (if out.head? = some true then some out.tail.length else none) =
        (Paper2.CappedSampler.runBits D R tape).map Fin.val := by
  obtain ⟨ta, v, ticket, cap, out, r, tail, hta, hra,
    hticket, hcap, hrle, hout⟩ := loop_bank D R hD tape suffix
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
      ⟨none, v, T⟩ := by
    simpa [S,T,b,n,Comparator.cfg] using hra
  have hd := Drain.drain_bitTape b r tail suffix [] ticket
    (List.replicate n true) cap [] out
  have hb : Drain.run (r * (2*b+3)+1)
      (⟨some Drain.Label.start, (none,false), T⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Drain.Label Drain.Control) =
      ⟨none, (none,false), U⟩ := by
    simpa [T,U,Drain.cfg] using hd
  obtain ⟨t, ht, hr⟩ :=
    EthInapproximability.CurrentPaper.BitMachineRawSequence.runs
      Comparator.program Drain.program Comparator.Label.start Drain.Label.start
      (none,false) v (none,false) (none,false) S T U ta
      (r*(2*b+3)+1) ha hb
  refine ⟨t, ticket, cap, out, ?_, ?_, hticket, hcap, hout⟩
  · dsimp [b,n,Comparator.attemptBound] at *
    nlinarith
  · simpa [Drain.wrappedProgram,S,U,b,n] using hr


/-- Full-bank wide-input result. Every bank change is the execution of the
frozen physical projector/preparer or loop/drain, plus two charged handoffs. -/
theorem wide_bank (D p R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D + p) R)
    (suffix : List Bool) :
    ∃ t ticket cap out,
      t ≤ R * (2 * (Nat.clog 2 D + p) + Nat.clog 2 D + 6) + 3 +
        (D - 1 + p + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance WideProjection.wideProgram)^[t])
        ⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              WideProjection.Label.start)),
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
      (if out.head? = some true then some out.tail.length else none) =
        (Paper2.CappedSampler.runWideBits D (Nat.clog 2 D + p) R
          (Nat.le_add_right (Nat.clog 2 D) p) tape).map Fin.val := by
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
  obtain ⟨t₁,ht₁,hr₁⟩ :=
    EthInapproximability.CurrentPaper.BitMachineRawSequence.runs
      WideProjection.program WideProjection.Prepare.program
      WideProjection.Label.start WideProjection.Prepare.Label.moveCap
      (none,false) (none,false) (none,false) (none,false) S T U
      (R*(2*(b+p)+b+6)+3) (n+p+2) hproj hprep
  obtain ⟨t₂,ticket,cap,out,ht₂,hr₂,hticket,hcap,hout⟩ :=
    wrapped_bank D R hD prefTape suffix
  let V := Comparator.bank suffix (List.replicate b true) [] [] ticket []
    (List.replicate n true) cap [] out
  have hr₂' : ((advance Drain.wrappedProgram)^[t₂])
      (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          Comparator.Label.start),((none,false),(none,false)),U⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool)
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.Label
            Comparator.Label Drain.Label)
          (EthInapproximability.CurrentPaper.BitMachineRawSequence.Control
            Comparator.Control Drain.Control)) =
      ⟨none,((none,false),(none,false)),V⟩ := by
    simpa [U,V,b,n,prefTape] using hr₂
  obtain ⟨t,ht,hr⟩ :=
    EthInapproximability.CurrentPaper.BitMachineRawSequence.runs
      WideProjection.projectionThenPrepare Drain.wrappedProgram
      (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
        WideProjection.Label.start)
      (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
        Comparator.Label.start)
      ((none,false),(none,false)) ((none,false),(none,false))
      ((none,false),(none,false)) ((none,false),(none,false))
      S U V t₁ t₂ (by simpa [WideProjection.projectionThenPrepare] using hr₁) hr₂'
  refine ⟨t,ticket,cap,out,?_,?_,hticket,hcap,?_⟩
  · dsimp [b,n] at *
    omega
  · simpa [WideProjection.wideProgram,S,V,b,n] using hr
  · simpa [Paper2.CappedSampler.runWideBits,prefTape] using hout


theorem wide_bank_public (D B R : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B) (tape : Paper2.CappedSampler.BitTape B R)
    (suffix : List Bool) :
    ∃ t ticket cap out,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance WideProjection.wideProgram)^[t])
        ⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              WideProjection.Label.start)),
          (((none,false),(none,false)),((none,false),(none,false))),
          WideProjection.bank
            (BlockTransfer.flatBitTape B R tape ++ suffix)
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B - Nat.clog 2 D) true) (List.replicate R true)
            [] [] (List.replicate (D-1) true) []⟩ =
        ⟨none, (((none,false),(none,false)),((none,false),(none,false))),
          Comparator.bank suffix (List.replicate (Nat.clog 2 D) true)
            [] [] ticket [] (List.replicate (D-1) true) cap [] out⟩ ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧
      (if out.head? = some true then some out.tail.length else none) =
        (Paper2.CappedSampler.runWideBits D B R hB tape).map Fin.val := by
  obtain ⟨p,hp⟩ : ∃ p, B = Nat.clog 2 D + p :=
    ⟨B - Nat.clog 2 D, by omega⟩
  subst B
  simpa [Nat.add_sub_cancel_left] using wide_bank D p R hD tape suffix


/-- Exact source-serialized draw with a complete terminal ten-stack bank.
Ticket and comparator-cap residues are bounded but deliberately not erased;
clearing them or consuming the output before the next draw must be charged. -/
theorem source_draw_bank (D B R N : ℕ) (hD : 0 < D)
    (hB : Nat.clog 2 D ≤ B)
    (tape : Paper2.CappedSampler.Adaptive.Tape B R (N+1)) :
    ∃ t ticket cap out,
      t ≤ R * (2 * B + Nat.clog 2 D + 6) + 3 +
        (D - 1 + (B - Nat.clog 2 D) + 2) +
        (R * (Comparator.attemptBound D + (2 * Nat.clog 2 D + 3)) + 3) + 2 ∧
      ((advance WideProjection.wideProgram)^[t])
        ⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
            (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
              WideProjection.Label.start)),
          (((none,false),(none,false)),((none,false),(none,false))),
          WideProjection.bank
            (Paper2.RecursiveSamplingTape.writeTape B R (N+1) tape).val
            (List.replicate (Nat.clog 2 D) true) [] []
            (List.replicate (B - Nat.clog 2 D) true) (List.replicate R true)
            [] [] (List.replicate (D-1) true) []⟩ =
        ⟨none, (((none,false),(none,false)),((none,false),(none,false))),
          Comparator.bank
            (Paper2.RecursiveSamplingTape.writeTape B R N tape.2).val
            (List.replicate (Nat.clog 2 D) true)
            [] [] ticket [] (List.replicate (D-1) true) cap [] out⟩ ∧
      ticket.length ≤ Nat.clog 2 D ∧ cap.length ≤ D-1 ∧
      (if out.head? = some true then some out.tail.length else none) =
        (Paper2.CappedSampler.runWideBits D B R hB tape.1).map Fin.val := by
  simpa [← SerializationBridge.flatAdaptiveTape_eq_writeTape,
    WideProjection.flatAdaptiveTape] using
    wide_bank_public D B R hD hB tape.1
      (WideProjection.flatAdaptiveTape B R N tape.2)


end Paper2.CappedLoop.TerminalFrame
