import EthInapproximability.CurrentPaper.SourceCSPHeaderCheck

/-!
# All-input halting of the four-field physical header/check sequence

The row-controller parser already halts on malformed canonical numbers. Its
physical framed run is followed by both hardwired expected-word comparators,
which also halt on arbitrary bitstrings. This establishes a transition bound
for the literal sequence on every input; the final global accept/reject
controller and its output selection are separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderTotal

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem parser_total_framed (input : List Bool) :
    ∃ t v S, t ≤ 4 * (2 * input.length + 4) + 3 ∧
      SourceCSPHeaderCheck.parserRun t
        (⟨some (.start 0), (none, none),
          SourceCSPHeaderCheck.parserInitial input⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (SourceCSPRowController.Label 4 0) SourceCSPRowController.Control) =
        ⟨none, v, S⟩ ∧
      S (.inl (.inr 2)) = SourceCSPRowController.rowResult 4 0 input ∧
      S (.inr 0) = [] := by
  obtain ⟨t, c, ht, hr, hh, hresult⟩ := SourceCSPHeaderParse.all_input input
  let before := SourceCSPHeaderCheck.parserInitial input
  let localCfg : SourceCSPHeaderParse.Config :=
    SourceCSPRowController.cfg (H := 0) (some (.start 0))
      (none, none) (fun _ => []) input [] []
  have hhalt : (SourceCSPRowController.run (H := 0) t localCfg).l = none := by
    rw [hr]
    exact hh
  obtain ⟨u, hu, hrun⟩ := outputs SourceCSPHeaderCheck.parserEmbedding
    before id id id (fun _ => rfl) none
    (SourceCSPRowController.program 4 0)
    SourceCSPHeaderCheck.parserProgram (fun _ => rfl) localCfg t hhalt
  have hstart : cfg SourceCSPHeaderCheck.parserEmbedding before id id none
      localCfg =
      (⟨some (.start 0), (none, none), before⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
          (SourceCSPRowController.Label 4 0) SourceCSPRowController.Control) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq,
      SourceCSPRowController.cfg]
    congr 1
    apply bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  change ((advance (SourceCSPRowController.program 4 0))^[t]) localCfg = c at hr
  rw [hr, hstart] at hrun
  let S := bank SourceCSPHeaderCheck.parserEmbedding before c.stk
  refine ⟨u, c.var, S, hu.trans ht, ?_, ?_, ?_⟩
  · simpa only [SourceCSPHeaderCheck.parserRun, S, cfg, stackCfg,
      BitMachineInline.cfg, id_eq, hh, Option.map_none] using hrun
  · change bank SourceCSPHeaderCheck.parserEmbedding before c.stk
      (SourceCSPHeaderCheck.parserEmbedding (.inr 2)) = _
    rw [bank_at]
    exact hresult
  · apply bank_outside
    rintro ⟨k, hk⟩
    cases hk

theorem fixed_header_total (a q : Nat) (input : List Bool) :
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
      S (.inr 0) = decide (wq = q.bits) :: decide (wa = a.bits) :: [] := by
  obtain ⟨tp, vp, Sp, htp, hrp, _, hstatus⟩ := parser_total_framed input
  let wa := Sp (.inl (.inl 2))
  let wq := Sp (.inl (.inl 3))
  obtain ⟨ta, va, Sa, hta, hra, hsa, hqa, _⟩ :=
    SourceCSPHeaderCheck.checker_total a.bits wa [] 2 Sp rfl hstatus
  have hqword : Sa (.inl (.inl 3)) = wq := hqa 3 (by decide)
  obtain ⟨tq, vq, Sq, htq, hrq, hsq, _, _⟩ :=
    SourceCSPHeaderCheck.checker_total q.bits wq
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
  refine ⟨t, Sq, vq, wa, wq, ?_, hr, hsq⟩
  · omega

end EthInapproximability.CurrentPaper.SourceCSPHeaderTotal
