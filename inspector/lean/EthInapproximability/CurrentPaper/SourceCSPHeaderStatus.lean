import EthInapproximability.CurrentPaper.SourceCSPHeaderTotal

/-!
# Parser-failure flag through the hardwired header checks

The two fixed-word comparators never touch the parser's output stack. This
companion strengthens the framed totality interface without modifying the
frozen comparator or header-parser owners.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderStatus

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem checker_total_with_parser_flag (expected word status : List Bool)
    (j : Fin 4) (before : SourceCSPHeaderCheck.Stack → List Bool)
    (hword : before (.inl (.inl j)) = word)
    (hstatus : before (.inr 0) = status) :
    ∃ t v S, t ≤ expected.length + 1 ∧
      SourceCSPHeaderCheck.checkerRun expected j t
        (⟨some (.compare 0), none, before⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (SourceFixedBinaryCheck.Label expected) (Option Bool)) =
        ⟨none, v, S⟩ ∧
      S (.inr 0) = decide (word = expected) :: status ∧
      (∀ k : Fin 4, k ≠ j → S (.inl (.inl k)) = before (.inl (.inl k))) ∧
      S (.inl (.inr 2)) = before (.inl (.inr 2)) := by
  let localCfg : SourceFixedBinaryCheck.Config expected :=
    ⟨some (.compare 0), none, SourceFixedBinaryCheck.contents word status⟩
  obtain ⟨t, c, ht, hr, hh, hs⟩ :=
    SourceFixedBinaryCheck.run_from expected 0 word status none
  have hhalt : (SourceFixedBinaryCheck.run expected t localCfg).l = none := by
    rw [show SourceFixedBinaryCheck.run expected t localCfg = c from hr]
    exact hh
  obtain ⟨u, hu, hrun⟩ := outputs
    (SourceCSPHeaderCheck.checkerEmbedding j) before id id id
    (fun _ => rfl) none (SourceFixedBinaryCheck.program expected)
    (SourceCSPHeaderCheck.checkerProgram expected j) (fun _ => rfl)
    localCfg t hhalt
  have hstart : cfg (SourceCSPHeaderCheck.checkerEmbedding j) before id id none
      localCfg =
      (⟨some (.compare 0), none, before⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
          (SourceFixedBinaryCheck.Label expected) (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [SourceCSPHeaderCheck.checkerEmbedding,
      SourceFixedBinaryCheck.contents, hword, hstatus]
  change ((advance (SourceFixedBinaryCheck.program expected))^[t]) localCfg = c at hr
  rw [hr, hstart] at hrun
  let S := bank (SourceCSPHeaderCheck.checkerEmbedding j) before c.stk
  refine ⟨u, c.var, S, hu.trans ht, ?_, ?_, ?_, ?_⟩
  · simpa only [SourceCSPHeaderCheck.checkerRun, S, cfg, stackCfg,
      BitMachineInline.cfg, hh, id_eq, Option.map_none] using hrun
  · change bank (SourceCSPHeaderCheck.checkerEmbedding j) before c.stk
      (SourceCSPHeaderCheck.checkerEmbedding j 1) = _
    rw [bank_at]
    simpa only [List.drop_zero, Fin.val_zero, Nat.sub_zero] using hs
  · intro k hk
    apply bank_outside
    rintro ⟨r, hr⟩
    fin_cases r
    · simp [SourceCSPHeaderCheck.checkerEmbedding] at hr
      exact hk hr.symm
    · simp [SourceCSPHeaderCheck.checkerEmbedding] at hr
  · apply bank_outside
    rintro ⟨r, hr⟩
    fin_cases r <;> simp [SourceCSPHeaderCheck.checkerEmbedding] at hr

theorem fixed_header_total_status (a q : Nat) (input : List Bool) :
    ∃ t S v wa wq,
      t ≤ 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 2 ∧
      SourceCSPHeaderCheck.fixedHeaderRun a q t
        (⟨some (.inl (.inl (.start 0))), (((none, none), none), none),
          SourceCSPHeaderCheck.parserInitial input⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
                (SourceFixedBinaryCheck.Label a.bits))
              (SourceFixedBinaryCheck.Label q.bits))
            ((SourceCSPRowController.Control × Option Bool) × Option Bool)) =
        ⟨none, (((none, none), none), v), S⟩ ∧
      S (.inl (.inr 2)) = SourceCSPRowController.rowResult 4 0 input ∧
      S (.inr 0) = decide (wq = q.bits) :: decide (wa = a.bits) :: [] := by
  obtain ⟨tp, vp, Sp, htp, hrp, hparser, hstatus⟩ :=
    SourceCSPHeaderTotal.parser_total_framed input
  let wa := Sp (.inl (.inl 2))
  let wq := Sp (.inl (.inl 3))
  obtain ⟨ta, va, Sa, hta, hra, hsa, hqa, hparserA⟩ :=
    checker_total_with_parser_flag a.bits wa [] 2 Sp rfl hstatus
  have hqword : Sa (.inl (.inl 3)) = wq := hqa 3 (by decide)
  obtain ⟨tq, vq, Sq, htq, hrq, hsq, _, hparserQ⟩ :=
    checker_total_with_parser_flag q.bits wq
      (decide (wa = a.bits) :: []) 3 Sa hqword hsa
  obtain ⟨tpa, htpa, hrpa⟩ := BitMachineRawSequence.runs
    SourceCSPHeaderCheck.parserProgram
    (SourceCSPHeaderCheck.checkerProgram a.bits 2)
    (.start 0 : SourceCSPRowController.Label 4 0)
    (.compare 0 : SourceFixedBinaryCheck.Label a.bits)
    ((none, none) : SourceCSPRowController.Control) vp
    (none : Option Bool) va
    (SourceCSPHeaderCheck.parserInitial input) Sp Sa tp ta hrp hra
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPHeaderCheck.alphabetProgram a)
    (SourceCSPHeaderCheck.checkerProgram q.bits 3)
    (.inl (.start 0) : BitMachineRawSequence.Label
      (SourceCSPRowController.Label 4 0)
      (SourceFixedBinaryCheck.Label a.bits))
    (.compare 0 : SourceFixedBinaryCheck.Label q.bits)
    (((none, none), none) :
      SourceCSPRowController.Control × Option Bool)
    ((none, none), va) (none : Option Bool) vq
    (SourceCSPHeaderCheck.parserInitial input) Sa Sq tpa tq hrpa hrq
  refine ⟨t, Sq, vq, wa, wq, ?_, hr, ?_, hsq⟩
  · omega
  · exact hparserQ.trans (hparserA.trans hparser)

end EthInapproximability.CurrentPaper.SourceCSPHeaderStatus
