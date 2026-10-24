import EthInapproximability.CurrentPaper.SourceCSPHeaderRawBank
import EthInapproximability.CurrentPaper.SourceCSPInputGuardedPoly
import EthInapproximability.CurrentPaper.SourceCSPGuardStatusSequence
import EthInapproximability.CurrentPaper.SourceCSPGuardDispatchPreserve
import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalHaltCompare
import EthInapproximability.CurrentPaper.SourceCSPGuardOutputCombined

/-!
# Literal raw CSP header bank through physical checks and guard

The successful four-word parser retains its actual words and row suffix.
These lemmas transport that bank through the disjoint fixed-word comparators,
status collection, input-length scan, and bounded constraint-count guard.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderBankTransport

open Turing BitMachineEncoding BitMachineStackEmbedding

private theorem embedded_outside {K J L V : Type*}
    [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (l : L) (v : V) (before : J → List Bool) (t : Nat) (j : J)
    (hj : ¬ ∃ k, ι k = j) :
    (((advance (fun l => stmt ι id id id none (P l)))^[t])
      (⟨some l, v, before⟩ : TM2.Cfg (fun _ : J => Bool) L V)).stk j =
      before j := by
  let localCfg : TM2.Cfg (fun _ : K => Bool) L V :=
    ⟨some l, v, fun k => before (ι k)⟩
  have hstart : stackCfg ι before localCfg =
      (⟨some l, v, before⟩ : TM2.Cfg (fun _ : J => Bool) L V) := by
    simp only [stackCfg, localCfg, bank_restrict]
  rw [← hstart]
  change (((advance (fun l => stackStmt ι
      (BitMachineInline.stmt id id id none (P l))))^[t])
      (stackCfg ι before localCfg)).stk j = before j
  rw [BitMachineStackRun.run]
  exact bank_outside ι before _ j hj

private theorem checker_preserves_suffix (expected : List Bool)
    (j : Fin 4) (before : SourceCSPHeaderCheck.Stack → List Bool)
    (t : Nat) :
    (SourceCSPHeaderCheck.checkerRun expected j t
      (⟨some (.compare 0), none, before⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
          (SourceFixedBinaryCheck.Label expected) (Option Bool))).stk
      (.inl (.inr 0)) = before (.inl (.inr 0)) := by
  have h := embedded_outside (SourceCSPHeaderCheck.checkerEmbedding j)
    (SourceFixedBinaryCheck.program expected) (.compare 0) none before t
    (.inl (.inr 0)) (by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp [SourceCSPHeaderCheck.checkerEmbedding] at hk)
  simpa only [SourceCSPHeaderCheck.checkerRun,
    SourceCSPHeaderCheck.checkerProgram] using h

/-- Successful arbitrary four-field parsing followed by both actual fixed
comparators preserves the parsed vertex/count words and literal row suffix. -/
theorem fixed_header_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t S v,
      t ≤ 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 2 ∧
      SourceCSPHeaderCheck.fixedHeaderRun a q t
        (⟨some (.inl (.inl (.start 0))), (((none, none), none), none),
          SourceCSPHeaderCheck.parserInitial input⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (SourceCSPRowController.Label 4 0)
                (SourceFixedBinaryCheck.Label a.bits))
              (SourceFixedBinaryCheck.Label q.bits))
            ((SourceCSPRowController.Control × Option Bool) × Option Bool)) =
        ⟨none, (((none, none), none), v), S⟩ ∧
      S (.inl (.inl 0)) = bank 0 ∧
      S (.inl (.inl 1)) = bank 1 ∧
      S (.inl (.inr 0)) = rest ∧
      S (.inl (.inr 2)) = [true] ∧
      S (.inr 0) =
        decide (bank 3 = q.bits) :: decide (bank 2 = a.bits) :: [] := by
  obtain ⟨tp, vp, Sp, htp, hrp, hwords, hsuffix, hparser, hstatus⟩ :=
    SourceCSPHeaderRawBank.parser_framed_success input bank rest hparse
  obtain ⟨ta, va, Sa, hta, hra, hsa, hothersA, hparserA⟩ :=
    SourceCSPHeaderStatus.checker_total_with_parser_flag a.bits
      (bank 2) [] 2 Sp (hwords 2) hstatus
  have hqword : Sa (.inl (.inl 3)) = bank 3 :=
    (hothersA 3 (by decide)).trans (hwords 3)
  obtain ⟨tq, vq, Sq, htq, hrq, hsq, hothersQ, hparserQ⟩ :=
    SourceCSPHeaderStatus.checker_total_with_parser_flag q.bits
      (bank 3) (decide (bank 2 = a.bits) :: []) 3 Sa hqword hsa
  have hsuffixA : Sa (.inl (.inr 0)) = rest := by
    have hp := checker_preserves_suffix a.bits 2 Sp ta
    rw [hra] at hp
    exact hp.trans hsuffix
  have hsuffixQ : Sq (.inl (.inr 0)) = rest := by
    have hp := checker_preserves_suffix q.bits 3 Sa tq
    rw [hrq] at hp
    exact hp.trans hsuffixA
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
  refine ⟨t, Sq, vq, by omega, hr, ?_, ?_, hsuffixQ, ?_, hsq⟩
  · exact (hothersQ 0 (by decide)).trans
      ((hothersA 0 (by decide)).trans (hwords 0))
  · exact (hothersQ 1 (by decide)).trans
      ((hothersA 1 (by decide)).trans (hwords 1))
  · exact hparserQ.trans (hparserA.trans hparser)

private theorem collect_preserves_source
    (before : SourceCSPHeaderCheck.Stack → List Bool)
    (k : SourceCSPHeaderCheck.Stack)
    (hparser : k ≠ SourceCSPHeaderValidFlag.parserSlot)
    (hflag : k ≠ SourceCSPHeaderValidFlag.flagSlot) :
    (advance SourceCSPHeaderValidFlag.collectProgram
      (⟨some (), (none, none, none), before⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool) Unit
          SourceCSPHeaderValidFlag.Control)).stk k = before k := by
  change k ≠ (.inl (.inr 2) : SourceCSPHeaderCheck.Stack) at hparser
  change k ≠ (.inr 0 : SourceCSPHeaderCheck.Stack) at hflag
  simp [advance, TM2.step, TM2.stepAux,
    SourceCSPHeaderValidFlag.collectProgram,
    SourceCSPHeaderValidFlag.parserSlot,
    SourceCSPHeaderValidFlag.flagSlot]
  simp [Function.update, hflag, hparser]

theorem valid_flag_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t S v,
      t ≤ 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 4 ∧
      ((advance (SourceCSPHeaderValidFlag.program a q))^[t])
        (⟨some (.inl (.inl (.inl (.start 0)))),
          ((((none, none), none), none), (none, none, none)),
          SourceCSPHeaderCheck.parserInitial input⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPHeaderValidFlag.ParseLabel a q) Unit)
            (SourceCSPHeaderValidFlag.ParseControl ×
              SourceCSPHeaderValidFlag.Control)) =
        ⟨none, ((((none, none), none), none), v), S⟩ ∧
      S (.inl (.inl 0)) = bank 0 ∧
      S (.inl (.inl 1)) = bank 1 ∧
      S (.inl (.inr 0)) = rest ∧
      S SourceCSPHeaderValidFlag.flagSlot =
        [decide (bank 3 = q.bits) && decide (bank 2 = a.bits)] := by
  obtain ⟨tp, Sp, vp, htp, hrp, hn, hm, hsuffix, hparser, hstatus⟩ :=
    fixed_header_success_bank a q input bank rest hparse
  let bq := decide (bank 3 = q.bits)
  let ba := decide (bank 2 = a.bits)
  let c : TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool) Unit
      SourceCSPHeaderValidFlag.Control :=
    advance SourceCSPHeaderValidFlag.collectProgram
      (⟨some (), (none, none, none), Sp⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool) Unit
          SourceCSPHeaderValidFlag.Control)
  have hp : Sp SourceCSPHeaderValidFlag.parserSlot = [true] := hparser
  have hq : Sp SourceCSPHeaderValidFlag.flagSlot = [bq, ba] := hstatus
  obtain ⟨hhalt, hflag, _⟩ :=
    SourceCSPHeaderValidFlag.collect_step Sp true bq ba hp hq
  have hrunC : ((advance SourceCSPHeaderValidFlag.collectProgram)^[1])
      (⟨some (), (none, none, none), Sp⟩ :
        TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool) Unit
          SourceCSPHeaderValidFlag.Control) =
      ⟨none, c.var, c.stk⟩ := by
    change c = ⟨none, c.var, c.stk⟩
    change c.l = none at hhalt
    cases hc : c with
    | mk l v S =>
        have hl : l = none := by simpa only [hc] using hhalt
        cases l <;> simp_all
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPHeaderCheck.fixedHeaderProgram a q)
    SourceCSPHeaderValidFlag.collectProgram
    (.inl (.inl (.start 0)) : SourceCSPHeaderValidFlag.ParseLabel a q)
    ()
    ((((none, none), none), none) : SourceCSPHeaderValidFlag.ParseControl)
    ((((none, none), none), vp) : SourceCSPHeaderValidFlag.ParseControl)
    ((none, none, none) : SourceCSPHeaderValidFlag.Control) c.var
    (SourceCSPHeaderCheck.parserInitial input) Sp c.stk tp 1 hrp hrunC
  have hsource (k : SourceCSPHeaderCheck.Stack)
      (hk1 : k ≠ SourceCSPHeaderValidFlag.parserSlot)
      (hk2 : k ≠ SourceCSPHeaderValidFlag.flagSlot) :
      c.stk k = Sp k := collect_preserves_source Sp k hk1 hk2
  refine ⟨t, c.stk, c.var, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SourceCSPHeaderValidFlag.program] using hr
  · exact (hsource (.inl (.inl 0)) (by decide) (by decide)).trans hn
  · exact (hsource (.inl (.inl 1)) (by decide) (by decide)).trans hm
  · exact (hsource (.inl (.inr 0)) (by decide) (by decide)).trans hsuffix
  · simpa only [SourceCSPHeaderValidFlag.flagSlot, bq, ba,
      Bool.true_and] using hflag

theorem input_header_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t v S,
      t ≤ 4 * (2 * input.length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 4 ∧
      ((advance (SourceCSPInputValid.headerProgram a q))^[t])
        (⟨some (.inl (.inl (.inl (.start 0)))),
          ((((none, none), none), none), (none, none, none)),
          SourceCSPInputFrame.afterLength input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (SourceCSPInputValid.HeaderLabel a q)
            SourceCSPInputValid.HeaderControl) =
        ⟨none, v, S⟩ ∧
      S (.inl (.inl (.inl 0))) = bank 0 ∧
      S (.inl (.inl (.inl 1))) = bank 1 ∧
      S (.inl (.inl (.inr 0))) = rest ∧
      S (.inl SourceCSPHeaderValidFlag.flagSlot) =
        [decide (bank 3 = q.bits) && decide (bank 2 = a.bits)] ∧
      S (.inr 2) = List.replicate input.length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = []) := by
  obtain ⟨th, Sh, vh, hth, hrh, hn, hm, hsuffix, hflag⟩ :=
    valid_flag_success_bank a q input bank rest hparse
  let before := SourceCSPInputFrame.afterLength input
  let localCfg : TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
      (SourceCSPInputValid.HeaderLabel a q)
      SourceCSPInputValid.HeaderControl :=
    ⟨some (.inl (.inl (.inl (.start 0)))),
      ((((none, none), none), none), (none, none, none)),
      SourceCSPHeaderCheck.parserInitial input⟩
  have hhalt : (((advance (SourceCSPHeaderValidFlag.program a q))^[th])
      localCfg).l = none := by
    rw [show ((advance (SourceCSPHeaderValidFlag.program a q))^[th])
      localCfg = ⟨none, ((((none, none), none), none), vh), Sh⟩ from by
      simpa only [localCfg] using hrh]
  obtain ⟨t, ht, hr⟩ := outputs SourceCSPInputFrame.headerEmbedding before
    id id id (fun _ => rfl) none
    (SourceCSPHeaderValidFlag.program a q)
    (SourceCSPInputValid.headerProgram a q)
    (fun _ => rfl) localCfg th hhalt
  have hstart : cfg SourceCSPInputFrame.headerEmbedding before id id none
      localCfg =
      (⟨some (.inl (.inl (.inl (.start 0)))),
        ((((none, none), none), none), (none, none, none)), before⟩ :
        TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
          (SourceCSPInputValid.HeaderLabel a q)
          SourceCSPInputValid.HeaderControl) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    exact congrFun (SourceCSPInputFrame.after_length_header input) k |>.symm
  have hlocal : ((advance (SourceCSPHeaderValidFlag.program a q))^[th])
      localCfg = ⟨none, ((((none, none), none), none), vh), Sh⟩ := by
    simpa only [localCfg] using hrh
  rw [hstart, hlocal] at hr
  let S : SourceCSPInputFrame.Stack → List Bool :=
    BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh
  refine ⟨t, ((((none, none), none), none), vh), S,
    ht.trans hth, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [SourceCSPInputValid.headerProgram, S,
      cfg, stackCfg, BitMachineInline.cfg, id_eq, Option.map_none] using hr
  · change BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh
      (SourceCSPInputFrame.headerEmbedding (.inl (.inl 0))) = _
    rw [bank_at]
    exact hn
  · change BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh
      (SourceCSPInputFrame.headerEmbedding (.inl (.inl 1))) = _
    rw [bank_at]
    exact hm
  · change BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh
      (SourceCSPInputFrame.headerEmbedding (.inl (.inr 0))) = _
    rw [bank_at]
    exact hsuffix
  · change BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh
      (SourceCSPInputFrame.headerEmbedding SourceCSPHeaderValidFlag.flagSlot) = _
    rw [bank_at]
    exact hflag
  · change BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh (.inr 2) = _
    rw [bank_outside]
    · exact SourceCSPInputFrame.after_length_cap input
    · rintro ⟨k, hk⟩
      cases hk
  · intro k hk
    change BitMachineStackEmbedding.bank SourceCSPInputFrame.headerEmbedding before Sh (.inr k) = []
    rw [bank_outside]
    · exact SourceCSPInputFrame.after_length_unused input k hk
    · rintro ⟨j, hj⟩
      cases hj

theorem input_valid_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t S v,
      t ≤ SourceCSPInputGuarded.inputBound a q input.length ∧
      ((advance (SourceCSPInputValid.inputProgram a q))^[t])
        (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
          ((none, none),
            ((((none, none), none), none), (none, none, none))),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label
                SourceInputLengthUnary.CountLabel)
              (SourceCSPInputValid.HeaderLabel a q))
            ((Option Bool × Option Bool) ×
              SourceCSPInputValid.HeaderControl)) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inl (.inl (.inl 0))) = bank 0 ∧
      S (.inl (.inl (.inl 1))) = bank 1 ∧
      S (.inl (.inl (.inr 0))) = rest ∧
      S (.inl SourceCSPHeaderValidFlag.flagSlot) =
        [decide (bank 3 = q.bits) && decide (bank 2 = a.bits)] ∧
      S (.inr 2) = List.replicate input.length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = []) := by
  obtain ⟨tl, htl, hrl⟩ := SourceCSPInputFrame.length_framed input
  obtain ⟨th, vh, Sh, hth, hrh, hn, hm, hsuffix, hflag, hcap, hunused⟩ :=
    input_header_success_bank a q input bank rest hparse
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    SourceCSPInputFrame.lengthProgram
    (SourceCSPInputValid.headerProgram a q)
    (.inl BitMachineCopy.Label.scan :
      BitMachineRawSequence.Label BitMachineCopy.Label
        SourceInputLengthUnary.CountLabel)
    (.inl (.inl (.inl (.start 0))) : SourceCSPInputValid.HeaderLabel a q)
    ((none, none) : Option Bool × Option Bool) (none, none)
    (((((none, none), none), none), (none, none, none)) :
      SourceCSPInputValid.HeaderControl) vh
    (SourceCSPInputFrame.initial input)
    (SourceCSPInputFrame.afterLength input) Sh tl th hrl hrh
  refine ⟨t, Sh, vh, ?_, ?_, hn, hm, hsuffix, hflag, hcap, hunused⟩
  · unfold SourceCSPInputGuarded.inputBound
    omega
  · simpa only [SourceCSPInputValid.inputProgram] using hr

private theorem guardBound_mono {W W' L : Nat} (h : W ≤ W') :
    SourceCSPInputGuarded.guardBound W L ≤
      SourceCSPInputGuarded.guardBound W' L := by
  have hm := Nat.mul_le_mul_left (L + 1)
    (show 4 * W + 5 ≤ 4 * W' + 5 by omega)
  unfold SourceCSPInputGuarded.guardBound
  omega

/-- The successful parser's literal vertex/count words and row suffix survive
the raw-length count, fixed-field checks, and bounded constraint guard. -/
theorem guarded_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t S v,
      t ≤ SourceCSPInputGuardedPoly.polyBound a q input.length ∧
      ((advance (SourceCSPInputGuarded.program a q))^[t])
        (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
          ((((none, none),
            (((((none, none), none), none), (none, none, none))))),
            ((none, none), (none, false))),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label BitMachineCopy.Label
                  SourceInputLengthUnary.CountLabel)
                (SourceCSPInputValid.HeaderLabel a q))
              SourceCSPQueryRange.Label)
            (SourceCSPInputGuarded.HeaderControl ×
              SourceCSPQueryRange.Control)) =
        ⟨none,
          ((((none, none),
            (((((none, none), none), none), (none, none, none))))), v), S⟩ ∧
      S (.inl (.inl (.inl 0))) = bank 0 ∧
      S (.inl (.inl (.inl 1))) = bank 1 ∧
      S (.inl (.inl (.inr 0))) = rest ∧
      S SourceCSPInputGuarded.FlagSlot =
        [decide (bank 3 = q.bits) && decide (bank 2 = a.bits)] ∧
      S (.inr 2) = List.replicate input.length true ∧
      S (.inr 6) = ProtocolBoundedUnary.result (bank 1)
        (List.replicate input.length true) [] := by
  obtain ⟨th, Sh, vh, hth, hrh, hn, hm, hsuffix, hflag, hcap,
      hunused⟩ := input_valid_success_bank a q input bank rest hparse
  let word := bank 1
  let cap := List.replicate input.length true
  have hready : SourceCSPConstraintGuard.Ready Sh word cap := by
    refine ⟨hm, hcap, ?_, ?_, ?_, ?_⟩
    · exact hunused 3 (by decide)
    · exact hunused 4 (by decide)
    · exact hunused 5 (by decide)
    · exact hunused 6 (by decide)
  obtain ⟨tg, vg, Sg, htg, hrg, hword, hcapg, hresult,
      hnG, hsuffixG⟩ :=
    SourceCSPConstraintGuard.guard_total word cap Sh hready
  have hflagG : Sg SourceCSPInputGuarded.FlagSlot =
      Sh SourceCSPInputGuarded.FlagSlot := by
    have h := SourceCSPInputGuarded.guard_preserves_flag Sh tg
    rw [hrg] at h
    exact h
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPInputValid.inputProgram a q)
    SourceCSPConstraintGuard.guardProgram
    (.inl (.inl BitMachineCopy.Label.scan) :
      BitMachineRawSequence.Label
        (BitMachineRawSequence.Label BitMachineCopy.Label
          SourceInputLengthUnary.CountLabel)
        (SourceCSPInputValid.HeaderLabel a q))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) :
      SourceCSPQueryRange.Label)
    (((none, none),
      (((((none, none), none), none), (none, none, none)))) :
        SourceCSPInputGuarded.HeaderControl)
    ((none, none), vh)
    (((none, none), (none, false)) : SourceCSPQueryRange.Control) vg
    (SourceCSPInputFrame.initial input) Sh Sg th tg hrh hrg
  have hwordBound : word.length ≤
      SourceCSPInputGrowth.growthConstant a q *
        SourceCSPInputGuarded.inputBound a q input.length := by
    have hw := SourceCSPInputGrowth.word_length_from_run
      a q input th Sh vh hrh
    have hw' : word.length ≤
        SourceCSPInputGrowth.growthConstant a q * th := by
      simpa only [word, SourceCSPInputGrowth.mSlot, hm] using hw
    exact hw'.trans (Nat.mul_le_mul_left _ hth)
  have hguardBound := guardBound_mono (L := input.length) hwordBound
  refine ⟨t, Sg, vg, ?_, ?_, hnG.trans hn, hword,
    hsuffixG.trans hsuffix, hflagG.trans hflag, hcapg, hresult⟩
  · unfold SourceCSPInputGuardedPoly.polyBound
    have htg' : tg ≤ SourceCSPInputGuarded.guardBound
        word.length input.length := by
      simpa only [cap, List.length_replicate,
        SourceCSPInputGuarded.guardBound] using htg
    omega
  · simpa only [SourceCSPInputGuarded.program] using hr

private theorem status_collect_preserves_source
    (before : SourceCSPInputFrame.Stack → List Bool)
    (k : SourceCSPInputFrame.Stack)
    (hh : k ≠ SourceCSPGuardStatus.headerSlot)
    (hg : k ≠ SourceCSPGuardStatus.guardSlot)
    (hs : k ≠ SourceCSPGuardStatus.statusSlot) :
    (advance SourceCSPGuardStatus.program
      (⟨some (), (none, none), before⟩ :
        TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool) Unit
          SourceCSPGuardStatus.Control)).stk k = before k := by
  change k ≠ SourceCSPInputGuarded.FlagSlot at hh
  change k ≠ (.inr 6 : SourceCSPInputFrame.Stack) at hg
  change k ≠ (.inr 1 : SourceCSPInputFrame.Stack) at hs
  simp [advance, TM2.step, TM2.stepAux,
    SourceCSPGuardStatus.program,
    SourceCSPGuardStatus.headerSlot,
    SourceCSPGuardStatus.guardSlot,
    SourceCSPGuardStatus.statusSlot]
  simp [Function.update, hh, hg, hs]

theorem guard_status_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t S v,
      t ≤ SourceCSPGuardStatusSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardStatusSequence.program a q))^[t])
        (⟨some (.inl (SourceCSPGuardStatusSequence.guardStart a q)),
          (SourceCSPGuardStatusSequence.guardInitial, (none, none)),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPGuardStatusSequence.GuardLabel a q) Unit)
            (SourceCSPGuardStatusSequence.GuardControl ×
              SourceCSPGuardStatus.Control)) =
        ⟨none, (SourceCSPGuardStatusSequence.guardInitial, v), S⟩ ∧
      S (.inl (.inl (.inl 0))) = bank 0 ∧
      S (.inl (.inl (.inl 1))) = bank 1 ∧
      S (.inl (.inl (.inr 0))) = rest ∧
      (S SourceCSPGuardStatus.statusSlot).head? =
        some (decide (bank 3 = q.bits) &&
          decide (bank 2 = a.bits) &&
          decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length)) ∧
      S SourceCSPGuardStatus.guardSlot =
        List.replicate (min (EncodedCommunication.bitsValue (bank 1))
          input.length) true := by
  obtain ⟨th, Sh, vh, hth, hrh, hn, hm, hsuffix, hflag, _, hresult⟩ :=
    guarded_success_bank a q input bank rest hparse
  let h := decide (bank 3 = q.bits) && decide (bank 2 = a.bits)
  let g := decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length)
  let unary := List.replicate
    (min (EncodedCommunication.bitsValue (bank 1)) input.length) true
  have hresult' : Sh SourceCSPGuardStatus.guardSlot = g :: unary := by
    simpa [SourceCSPGuardStatus.guardSlot, ProtocolBoundedUnary.result,
      g, unary] using hresult
  let c := advance SourceCSPGuardStatus.program
    (⟨some (), (none, none), Sh⟩ :
      TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool) Unit
        SourceCSPGuardStatus.Control)
  have hc := SourceCSPGuardStatus.collect_step Sh h g unary hflag hresult'
  have hcb : c.l = none ∧
      c.stk SourceCSPGuardStatus.statusSlot =
        (h && g) :: Sh SourceCSPGuardStatus.statusSlot ∧
      c.stk SourceCSPGuardStatus.guardSlot = unary := by
    simpa only [c] using ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hrcollect : ((advance SourceCSPGuardStatus.program)^[1])
      (⟨some (), (none, none), Sh⟩ :
        TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool) Unit
          SourceCSPGuardStatus.Control) =
      ⟨none, c.var, c.stk⟩ := by
    change c = ⟨none, c.var, c.stk⟩
    cases hcv : c with
    | mk l v s =>
        cases l with
        | none => rfl
        | some l =>
            have hx : some l = (none : Option Unit) := by
              simpa only [hcv] using hcb.1
            cases hx
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPInputGuarded.program a q) SourceCSPGuardStatus.program
    (SourceCSPGuardStatusSequence.guardStart a q) ()
    SourceCSPGuardStatusSequence.guardInitial
    (((((none, none),
      (((((none, none), none), none), (none, none, none))))), vh) :
        SourceCSPGuardStatusSequence.GuardControl)
    ((none, none) : SourceCSPGuardStatus.Control) c.var
    (SourceCSPInputFrame.initial input) Sh c.stk th 1
    (by simpa only [SourceCSPGuardStatusSequence.guardStart,
      SourceCSPGuardStatusSequence.guardInitial] using hrh) hrcollect
  have hsource (k : SourceCSPInputFrame.Stack)
      (hk1 : k ≠ SourceCSPGuardStatus.headerSlot)
      (hk2 : k ≠ SourceCSPGuardStatus.guardSlot)
      (hk3 : k ≠ SourceCSPGuardStatus.statusSlot) :
      c.stk k = Sh k :=
    status_collect_preserves_source Sh k hk1 hk2 hk3
  refine ⟨t, c.stk, c.var, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [SourceCSPGuardStatusSequence.bound]
    omega
  · simpa only [SourceCSPGuardStatusSequence.program] using hr
  · exact (hsource (.inl (.inl (.inl 0))) (by decide)
      (by decide) (by decide)).trans hn
  · exact (hsource (.inl (.inl (.inl 1))) (by decide)
      (by decide) (by decide)).trans hm
  · exact (hsource (.inl (.inl (.inr 0))) (by decide)
      (by decide) (by decide)).trans hsuffix
  · simpa only [h, g, List.head_cons] using
      congrArg List.head? hcb.2.1
  · exact hcb.2.2

/-- A successful arbitrary four-field parse whose fixed words agree with the
reduction parameters is literally the canonical header plus its suffix. -/
theorem parse_fixed_is_header (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest))
    (ha : bank 2 = a.bits) (hq : bank 3 = q.bits) :
    input = SourceCSPHeaderParse.header
      (EncodedCommunication.bitsValue (bank 0))
      (EncodedCommunication.bitsValue (bank 1)) a q ++ rest ∧
    bank 0 = (EncodedCommunication.bitsValue (bank 0)).bits ∧
    bank 1 = (EncodedCommunication.bitsValue (bank 1)).bits := by
  obtain ⟨hsource, hcanonical⟩ :=
    SourceCSPRowCodecParser.parse_zero_sound input bank rest hparse
  have hnumbers : (fun j : Fin 4 => EncodedCommunication.bitsValue (bank j)) =
      SourceCSPHeaderParse.numbers
        (EncodedCommunication.bitsValue (bank 0))
        (EncodedCommunication.bitsValue (bank 1)) a q := by
    funext j
    fin_cases j <;> simp [SourceCSPHeaderParse.numbers, ha, hq,
      EncodedCommunication.bitsValue_bits]
  refine ⟨?_, hcanonical 0, hcanonical 1⟩
  rw [hsource, hnumbers, SourceCSPHeaderParse.queries_eq_header]

/-- At the successful physical status bank, a true guard bit gives the exact
canonical source header, parsed binary words, and bounded unary count. -/
theorem guard_good_literal (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest))
    (S : SourceCSPInputFrame.Stack → List Bool)
    (hstatus : (S SourceCSPGuardStatus.statusSlot).head? =
      some (decide (bank 3 = q.bits) &&
        decide (bank 2 = a.bits) &&
        decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length)))
    (hgood : (S SourceCSPGuardStatus.statusSlot).head? = some true) :
    let n := EncodedCommunication.bitsValue (bank 0)
    let m := EncodedCommunication.bitsValue (bank 1)
    input = SourceCSPHeaderParse.header n m a q ++ rest ∧
      bank 0 = n.bits ∧ bank 1 = m.bits ∧ m ≤ input.length := by
  have hb := Option.some.inj (hstatus.symm.trans hgood)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hq, ha⟩, hm⟩ := hb
  obtain ⟨hsource, hnword, hmword⟩ :=
    parse_fixed_is_header a q input bank rest hparse ha hq
  exact ⟨hsource, hnword, hmword, hm⟩

/-- The final branch selector changes only its status stack; in particular,
the positive branch receives the exact parsed header and raw row suffix. -/
theorem dispatch_success_bank (a q : Nat) (input : List Bool)
    (bank : SourceCSPRowController.Bank 4) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) = some (bank, rest)) :
    ∃ t S v,
      t ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardDispatchSequence.program a q))^[t])
        (⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
          (SourceCSPGuardDispatchSequence.headerInitial,
            SourceCSPGuardDispatch.initialControl),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPGuardDispatchSequence.HeaderLabel a q)
              SourceCSPGuardDispatch.Label)
            (SourceCSPGuardDispatchSequence.HeaderControl ×
              SourceCSPGuardDispatch.Control)) =
        ⟨none, (SourceCSPGuardDispatchSequence.headerInitial, v), S⟩ ∧
      S SourceCSPGuardDispatch.vertexSlot = bank 0 ∧
      S (.inl (.inl (.inl 1))) = bank 1 ∧
      S SourceCSPGuardDispatch.sourceSlot = rest ∧
      S SourceCSPGuardDispatch.countSlot =
        List.replicate (min (EncodedCommunication.bitsValue (bank 1))
          input.length) true ∧
      v.2 = some (SourceCSPGuardDispatch.classify
        (decide (bank 3 = q.bits) && decide (bank 2 = a.bits) &&
          decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length))
        (bank 0)
        (List.replicate (min (EncodedCommunication.bitsValue (bank 1))
          input.length) true) rest) := by
  obtain ⟨th, Sh, vh, hth, hrh, hn, hm, hsuffix, hstatus, hcount⟩ :=
    guard_status_success_bank a q input bank rest hparse
  let good := decide (bank 3 = q.bits) && decide (bank 2 = a.bits) &&
    decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length)
  have hshape : ∃ tail, Sh SourceCSPGuardDispatch.statusSlot = good :: tail := by
    change (Sh SourceCSPGuardStatus.statusSlot).head? = some good at hstatus
    cases hcell : Sh SourceCSPGuardStatus.statusSlot with
    | nil => simp [hcell] at hstatus
    | cons b tail =>
        have hb : b = good := by
          simpa only [hcell, List.head?_cons,
            Option.some.injEq] using hstatus
        subst b
        exact ⟨tail, by simpa only [SourceCSPGuardDispatch.statusSlot] using hcell⟩
  obtain ⟨tail, hshape⟩ := hshape
  obtain ⟨td, htd, hdhalt, hdout⟩ :=
    SourceCSPGuardDispatch.total Sh good tail hshape
  let cd := SourceCSPGuardDispatch.run td Sh
  change cd.l = none at hdhalt
  have hrd : ((advance SourceCSPGuardDispatch.program)^[td])
      (⟨some .status, SourceCSPGuardDispatch.initialControl, Sh⟩ :
        SourceCSPGuardDispatch.Config) =
      ⟨none, cd.var, cd.stk⟩ := by
    change cd = ⟨none, cd.var, cd.stk⟩
    cases hcd : cd with
    | mk l v s =>
        cases l with
        | none => rfl
        | some l =>
            have hx : some l = (none : Option SourceCSPGuardDispatch.Label) := by
              simpa only [hcd] using hdhalt
            cases hx
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPGuardStatusSequence.program a q)
    SourceCSPGuardDispatch.program
    (SourceCSPGuardDispatchSequence.headerStart a q) .status
    SourceCSPGuardDispatchSequence.headerInitial
    (SourceCSPGuardStatusSequence.guardInitial, vh)
    SourceCSPGuardDispatch.initialControl cd.var
    (SourceCSPInputFrame.initial input) Sh cd.stk th td
    (by simpa only [SourceCSPGuardDispatchSequence.headerStart,
      SourceCSPGuardDispatchSequence.headerInitial] using hrh) hrd
  have hpres (k : SourceCSPInputFrame.Stack)
      (hk : k ≠ SourceCSPGuardDispatch.statusSlot) :
      cd.stk k = Sh k :=
    SourceCSPGuardDispatchPreserve.run_preserves td Sh k hk
  refine ⟨t, cd.stk, cd.var, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [SourceCSPGuardDispatchSequence.bound]
    omega
  · simpa only [SourceCSPGuardDispatchSequence.program] using hr
  · exact (hpres SourceCSPGuardDispatch.vertexSlot (by decide)).trans hn
  · exact (hpres (.inl (.inl (.inl 1))) (by decide)).trans hm
  · exact (hpres SourceCSPGuardDispatch.sourceSlot (by decide)).trans hsuffix
  · exact (hpres SourceCSPGuardDispatch.countSlot (by decide)).trans hcount
  · simpa only [cd, good, SourceCSPGuardDispatch.vertexSlot,
      SourceCSPGuardDispatch.countSlot, SourceCSPGuardDispatch.sourceSlot,
      hn, hsuffix, hcount] using hdout

/-- No parser bank is supplied: if the actual all-input prefix chooses the
positive tag, its terminal bank contains the exact canonical header operands,
bounded unary count, and literal unread row suffix. -/
theorem positive_tag_literal (a q : Nat) (input : List Bool) :
    ∃ t S v,
      t ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardDispatchSequence.program a q))^[t])
        (⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
          (SourceCSPGuardDispatchSequence.headerInitial,
            SourceCSPGuardDispatch.initialControl),
          SourceCSPInputFrame.initial input⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPGuardDispatchSequence.HeaderLabel a q)
              SourceCSPGuardDispatch.Label)
            (SourceCSPGuardDispatchSequence.HeaderControl ×
              SourceCSPGuardDispatch.Control)) =
        ⟨none, (SourceCSPGuardDispatchSequence.headerInitial, v), S⟩ ∧
      (v.2 = some .positive →
        ∃ n m rest,
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          S SourceCSPGuardDispatch.vertexSlot = n.bits ∧
          S (.inl (.inl (.inl 1))) = m.bits ∧
          S SourceCSPGuardDispatch.sourceSlot = rest ∧
          S SourceCSPGuardDispatch.countSlot =
            List.replicate m true ∧
          m ≤ input.length) := by
  obtain ⟨t, S, S₀, v, wa, wq, word, ht, hr, hv⟩ :=
    SourceCSPGuardDispatchSequence.all_input a q input
  refine ⟨t, S, v, ht, hr, ?_⟩
  intro hpositive
  have hclass : SourceCSPGuardDispatch.classify
      ((SourceCSPHeaderValidFlag.parserGood input &&
        decide (wq = q.bits) && decide (wa = a.bits)) &&
        decide (EncodedCommunication.bitsValue word ≤ input.length))
      (S₀ SourceCSPGuardDispatch.vertexSlot)
      (S₀ SourceCSPGuardDispatch.countSlot)
      (S₀ SourceCSPGuardDispatch.sourceSlot) = .positive :=
    Option.some.inj (hv.symm.trans hpositive)
  have hpg : SourceCSPHeaderValidFlag.parserGood input = true := by
    cases hp : SourceCSPHeaderValidFlag.parserGood input with
    | true => rfl
    | false =>
        simp [SourceCSPGuardDispatch.classify, hp] at hclass
  cases hp : SourceCSPRowController.readQueriesFrom (q := 4) 0 input
      (fun _ => []) with
  | none =>
      simp [SourceCSPHeaderValidFlag.parserGood, hp] at hpg
  | some pair =>
      obtain ⟨bank, rest⟩ := pair
      obtain ⟨u, S', v', hu, hru, hn, hm, hsuffix, hcount, hv'⟩ :=
        dispatch_success_bank a q input bank rest hp
      let start : TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
          (BitMachineRawSequence.Label
            (SourceCSPGuardDispatchSequence.HeaderLabel a q)
            SourceCSPGuardDispatch.Label)
          (SourceCSPGuardDispatchSequence.HeaderControl ×
            SourceCSPGuardDispatch.Control) :=
        ⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
          (SourceCSPGuardDispatchSequence.headerInitial,
            SourceCSPGuardDispatch.initialControl),
          SourceCSPInputFrame.initial input⟩
      have he := SourceCSPRowLoopTotalHaltCompare.halted_unique
        (SourceCSPGuardDispatchSequence.program a q) start t u
        (by simpa only [start] using congrArg (fun c => c.l) hr)
        (by simpa only [start] using congrArg (fun c => c.l) hru)
      have hS : S = S' := by
        have h := congrArg (fun c => c.stk) he
        simpa only [start, hr, hru] using h
      have hvpos : v'.2 = some .positive := by
        have h := congrArg (fun c => c.var.2.2) he
        have hvv : v.2 = v'.2 := by
          simpa only [start, hr, hru] using h
        exact hvv.symm.trans hpositive
      have hclass' : SourceCSPGuardDispatch.classify
          (decide (bank 3 = q.bits) && decide (bank 2 = a.bits) &&
            decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length))
          (bank 0)
          (List.replicate (min (EncodedCommunication.bitsValue (bank 1))
            input.length) true) rest = .positive :=
        Option.some.inj (hv'.symm.trans hvpos)
      let good : Bool := decide (bank 3 = q.bits) &&
        decide (bank 2 = a.bits) &&
        decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length)
      have hgood : good = true := by
        cases hg : good with
        | true => rfl
        | false =>
            have hclassFalse : SourceCSPGuardDispatch.classify false
                (bank 0)
                (List.replicate (min
                  (EncodedCommunication.bitsValue (bank 1)) input.length) true)
                rest = .positive := by
              simpa only [good, hg] using hclass'
            simp [SourceCSPGuardDispatch.classify] at hclassFalse
      change (decide (bank 3 = q.bits) &&
        decide (bank 2 = a.bits) &&
        decide (EncodedCommunication.bitsValue (bank 1) ≤ input.length)) =
        true at hgood
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hgood
      obtain ⟨⟨hq, ha⟩, hbound⟩ := hgood
      obtain ⟨hsource, hnword, hmword⟩ :=
        parse_fixed_is_header a q input bank rest hp ha hq
      let n := EncodedCommunication.bitsValue (bank 0)
      let m := EncodedCommunication.bitsValue (bank 1)
      refine ⟨n, m, rest, hsource, ?_, ?_, ?_, ?_, hbound⟩
      · rw [hS, hn]
        exact hnword
      · rw [hS, hm]
        exact hmword
      · exact hS.symm ▸ hsuffix
      · rw [hS, hcount, Nat.min_eq_left hbound]

/-- The same positive-tag bank facts at the inlined route boundary used by
the global output controller. This is an actual run of its prefix table. -/
theorem combined_positive_prefix (a q : Nat) (input : List Bool) :
    ∃ t v S,
      t ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[t])
        (SourceCSPGuardOutputCombined.initial a q input) =
        (⟨some .route, (v, none), S⟩ :
          TM2.Cfg (fun _ : SourceCSPGuardOutputCombined.Stack => Bool)
            (SourceCSPGuardOutputCombined.Label a q)
            SourceCSPGuardOutputCombined.Control) ∧
      (v.2.2 = some .positive →
        ∃ n m rest,
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          S SourceCSPGuardDispatch.vertexSlot = n.bits ∧
          S (.inl (.inl (.inl 1))) = m.bits ∧
          S SourceCSPGuardDispatch.sourceSlot = rest ∧
          S SourceCSPGuardDispatch.countSlot =
            List.replicate m true ∧
          m ≤ input.length) := by
  obtain ⟨tp, Sp, vp, htp, hrp, hpositive⟩ :=
    positive_tag_literal a q input
  let localCfg : TM2.Cfg (fun _ : SourceCSPGuardOutputCombined.Stack => Bool)
      (SourceCSPGuardOutputCombined.PrefixLabel a q)
      SourceCSPGuardOutputCombined.PrefixControl :=
    ⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
      (SourceCSPGuardDispatchSequence.headerInitial,
        SourceCSPGuardDispatch.initialControl),
      SourceCSPInputFrame.initial input⟩
  have hhalt : (((advance (SourceCSPGuardDispatchSequence.program a q))^[tp])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun c => c.l) hrp
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs
    SourceCSPGuardOutputCombined.Label.prefix
    (fun v => (v, none)) Prod.fst (fun _ => rfl) (some .route)
    (SourceCSPGuardDispatchSequence.program a q)
    (SourceCSPGuardOutputCombined.program a q)
    (fun _ => rfl) localCfg tp hhalt
  rw [hrp] at hr
  refine ⟨t, (SourceCSPGuardDispatchSequence.headerInitial, vp), Sp,
    ht.trans htp, ?_, ?_⟩
  · simpa only [SourceCSPGuardOutputCombined.initial,
      SourceCSPGuardOutputCombined.initialControl, localCfg,
      BitMachineInline.cfg, Option.map_none] using hr
  · intro hv
    exact hpositive hv

end EthInapproximability.CurrentPaper.SourceCSPHeaderBankTransport
