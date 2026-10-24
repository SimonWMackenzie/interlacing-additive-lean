import EthInapproximability.CurrentPaper.SourceCSPGlobalPrefixTerminal
import EthInapproximability.CurrentPaper.SourceCSPGlobalRowFailure
import EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveLiteral
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Total raw-input terminal classification for the existing global CSP program. -/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalTotalValidation

open Turing BitMachineEncoding
open SourceCSPGlobalDecisionProgram

private theorem positive_route_unique (a q : Nat) (input : List Bool)
    (t₁ t₂ : Nat) (v₁ v₂ : SourceCSPGuardOutputCombined.PrefixControl)
    (S₁ S₂ : SourceCSPInputFrame.Stack → List Bool)
    (hr₁ : ((advance (SourceCSPGuardOutputCombined.program a q))^[t₁])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v₁, none), S₁⟩)
    (hv₁ : v₁.2.2 = some .positive)
    (hr₂ : ((advance (SourceCSPGuardOutputCombined.program a q))^[t₂])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v₂, none), S₂⟩) :
    v₂.2.2 = some .positive := by
  let P := SourceCSPGuardOutputCombined.program a q
  let c := SourceCSPGuardOutputCombined.initial a q input
  have hpos : ((advance P)^[t₁ + 2]) c =
      ⟨none, (v₁, none), S₁⟩ := by
    rw [show t₁ + 2 = 2 + t₁ by omega, Function.iterate_add_apply, hr₁]
    exact SourceCSPGuardOutputCombined.route_positive a q v₁ S₁ hv₁
  have htag : v₂.2.2 = some .positive := by
    cases hv₂ : v₂.2.2 with
    | none =>
        have hnone : SourceCSPGuardOutputCombined.routeRun a q 2 v₂ S₂ =
            ⟨none, (v₂, none), S₂⟩ := by
          simp [SourceCSPGuardOutputCombined.routeRun,
            Function.iterate_succ_apply', advance, TM2.step, TM2.stepAux,
            SourceCSPGuardOutputCombined.program, hv₂]
        have hlast : ((advance P)^[t₂ + 2]) c =
            ⟨none, (v₂, none), S₂⟩ := by
          rw [show t₂ + 2 = 2 + t₂ by omega, Function.iterate_add_apply, hr₂]
          exact hnone
        have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique P c
          (t₁ + 2) (t₂ + 2)
          (by rw [hpos]) (by rw [hlast])
        have hv := congrArg (fun x => x.var.1.2.2) heq
        rw [hpos, hlast] at hv
        simp only at hv
        exact False.elim (by rw [hv₁, hv₂] at hv; cases hv)
    | some tag =>
        cases tag with
        | positive => rfl
        | reject =>
            obtain ⟨tr, T, _, hroute, _, _⟩ :=
              SourceCSPGuardOutputCombined.route_reject a q v₂ S₂ hv₂
            have hlast : ((advance P)^[t₂ + tr]) c =
                ⟨none, (SourceCSPGuardOutputCombined.rejectControl, none), T⟩ := by
              rw [show t₂ + tr = tr + t₂ by omega,
                Function.iterate_add_apply, hr₂]
              exact hroute
            have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique P c
              (t₁ + 2) (t₂ + tr)
              (by rw [hpos]) (by rw [hlast])
            have hv := congrArg (fun x => x.var.1.2.2) heq
            rw [hpos, hlast] at hv
            simp [SourceCSPGuardOutputCombined.rejectControl, hv₁] at hv
        | zero =>
            obtain ⟨tr, T, _, hroute, _, _⟩ :=
              SourceCSPGuardOutputCombined.route_zero a q v₂ S₂ hv₂
            have hlast : ((advance P)^[t₂ + tr]) c =
                ⟨none, (SourceCSPGuardOutputCombined.zeroControl, none), T⟩ := by
              rw [show t₂ + tr = tr + t₂ by omega,
                Function.iterate_add_apply, hr₂]
              exact hroute
            have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique P c
              (t₁ + 2) (t₂ + tr)
              (by rw [hpos]) (by rw [hlast])
            have hv := congrArg (fun x => x.var.1.2.2) heq
            rw [hpos, hlast] at hv
            simp [SourceCSPGuardOutputCombined.zeroControl, hv₁] at hv
  exact htag

/-- A fixed-`a,q` polynomial in the original raw input length.  The
per-transition push count charges clearing a previously grown output stack. -/
noncomputable def totalBound (a q L : Nat) : Nat :=
  let p := BitMachineStackGrowth.perStep
    (SourceCSPGlobalDecisionProgram.program a q)
  let prefixBoundVal := SourceCSPGuardOutputCombined.polyBound a q L + 1
  let cap := SourceCSPGuardDispatchSequence.bound a q L + 2 +
    SourceCSPGlobalCapFromLiteral.capBound q L L
  let row := SourceCSPGlobalPositiveRows.physicalRowBound a q L
  max prefixBoundVal (max ((1 + p) * cap + 4) ((1 + p) * row + 4))

private theorem output_growth (a q : Nat) (input : List Bool)
    (t : Nat) (label : Option (SourceCSPGlobalDecisionProgram.Label a q))
    (control : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hrun : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨label, control, S⟩) :
    (S SourceCSPGlobalDecisionProgram.outputSlot).length ≤
      BitMachineStackGrowth.perStep
        (SourceCSPGlobalDecisionProgram.program a q) * t := by
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input) t
    SourceCSPGlobalDecisionProgram.outputSlot
  rw [hrun] at hg
  have hb : (SourceCSPGlobalDecisionProgram.initial a q input).stk
      SourceCSPGlobalDecisionProgram.outputSlot = [] := rfl
  simpa only [hb, List.length_nil, Nat.zero_add] using hg

private theorem prefix_le_total (a q L : Nat) :
    SourceCSPGuardOutputCombined.polyBound a q L + 1 ≤
      totalBound a q L := by
  unfold totalBound
  exact le_max_left _ _

private theorem cap_le_total (a q L : Nat) :
    (1 + BitMachineStackGrowth.perStep
      (SourceCSPGlobalDecisionProgram.program a q)) *
      (SourceCSPGuardDispatchSequence.bound a q L + 2 +
        SourceCSPGlobalCapFromLiteral.capBound q L L) + 4 ≤
      totalBound a q L := by
  unfold totalBound
  exact (le_max_left _ _).trans (le_max_right _ _)

private theorem row_le_total (a q L : Nat) :
    (1 + BitMachineStackGrowth.perStep
      (SourceCSPGlobalDecisionProgram.program a q)) *
      SourceCSPGlobalPositiveRows.physicalRowBound a q L + 4 ≤
      totalBound a q L := by
  unfold totalBound
  exact (le_max_right _ _).trans (le_max_right _ _)

private theorem charged_clear_bound (p t tw out B : Nat)
    (ht : t ≤ B) (hw : tw ≤ out + 4) (hg : out ≤ p * t) :
    t + tw ≤ (1 + p) * B + 4 := by
  have hfirst : t + tw ≤ (1 + p) * t + 4 := by
    rw [add_mul]
    omega
  have hsecond := Nat.mul_le_mul_left (1 + p) ht
  omega

/-- The same finite instruction table reaches a literal accepting tag or a
completed reject/zero output on every raw input. Acceptance means only that
the bounded header and typed row list were validated; no CNF is written there. -/
theorem raw_total_validation (a q : Nat) (input : List Bool) :
    ∃ t ≤ totalBound a q input.length,
      (∃ (c : SourceCSPGlobalDecisionProgram.Control a q)
          (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, c, S⟩ ∧
        S SourceCSPGlobalDecisionProgram.outputSlot =
          SourceCSPRejectFormula.bits ∧
        S SourceCSPGlobalDecisionProgram.outputSlot ∉ EncodedCNF.Language) ∨
      (∃ S : SourceCSPGlobalDecisionProgram.Stack q → List Bool,
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, .prefix (SourceCSPGuardOutputCombined.zeroControl, none), S⟩ ∧
        S SourceCSPGlobalDecisionProgram.outputSlot = [false, false]) ∨
      (∃ (n m : Nat) (rest : List Bool)
          (rows : Fin m → SourceCSPCodec.Row n a q)
          (vr : SourceCSPRowLoopController.QueryControl ×
            SourceCSPRowLoopController.ResetControl)
          (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
        input = SourceCSPHeaderParse.header n m a q ++ rest ∧
        0 < n ∧ n ≤ q * m ∧
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
          some (rows, []) ∧
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨some .accept, .row (vr, some true), S⟩) := by
  obtain ⟨tp, v, Sp, S₀, wa, wq, word, htp, hrp,
    htag, _, hreje, hzero⟩ :=
    SourceCSPGlobalDecisionProgram.raw_guarded_terminal a q input
  let tag := SourceCSPGuardDispatch.classify
    ((SourceCSPHeaderValidFlag.parserGood input &&
      decide (wq = q.bits) && decide (wa = a.bits)) &&
      decide (EncodedCommunication.bitsValue word ≤ input.length))
    (S₀ SourceCSPGuardDispatch.vertexSlot)
    (S₀ SourceCSPGuardDispatch.countSlot)
    (S₀ SourceCSPGuardDispatch.sourceSlot)
  have hv : v.2.2 = some tag := htag
  cases hcase : tag with
  | reject =>
      have hvreje : v.2.2 = some .reject := by simpa only [hcase] using hv
      obtain ⟨t, S, ht, hrun, hout, hnlang⟩ := hreje hvreje
      exact ⟨t, ht.trans (prefix_le_total a q input.length),
        Or.inl ⟨_, S, hrun, hout, hnlang⟩⟩
  | zero =>
      have hvzero : v.2.2 = some .zero := by simpa only [hcase] using hv
      obtain ⟨t, S, ht, hrun, hout⟩ := hzero hvzero
      exact ⟨t, ht.trans (prefix_le_total a q input.length),
        Or.inr (Or.inl ⟨S, hrun, hout⟩)⟩
  | positive =>
      have hvpos : v.2.2 = some .positive := by simpa only [hcase] using hv
      obtain ⟨tp₂, v₂, Sp₂, _, hrp₂, hpositive⟩ :=
        SourceCSPGlobalPositiveLiteral.positive_literal a q input
      have hv₂ := positive_route_unique a q input tp tp₂ v v₂ Sp Sp₂
        hrp hvpos hrp₂
      obtain ⟨n, m, tg, rest, Sg, htg, hglobal, hinput,
        hnword, _, hrest, hm, hmL, hempty, hrowblank⟩ := hpositive hv₂
      by_cases hcap : 0 < n ∧ n ≤ q * m
      · have hsuffixL :=
          (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
            a q n m input rest hinput).2.2
        obtain ⟨tr, Sr, vr, b, htr, hrr, hsem, _, _⟩ :=
          SourceCSPGlobalPositiveRows.positive_rows_from_literal
            n m a q input.length rest (v₂, none) Sg
            hcap.1 hcap.2 hmL hsuffixL hv₂ hnword hm hrest
            hempty hrowblank
        have hnwordL :=
          (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
            a q n m input rest hinput).1
        have hcBound := SourceCSPGlobalCapFromLiteral.capBound_uniform
          q n.bits.length m input.length hnwordL hmL
        have hcapL : n - 1 ≤ q * input.length := by
          have hqm : q * m ≤ q * input.length := Nat.mul_le_mul_left q hmL
          omega
        have htrow : tg + tr ≤
            SourceCSPGlobalPositiveRows.physicalRowBound a q input.length := by
          unfold SourceCSPGlobalPositiveRows.physicalRowBound
          omega
        have hrowrun :
            ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr])
              (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨some .afterRow, .row (vr, some b), Sr⟩ := by
          rw [show tg + tr = tr + tg by omega,
            Function.iterate_add_apply, hglobal]
          exact hrr
        cases b with
        | true =>
            have hrows := hsem.mp rfl
            obtain ⟨rows, hrows⟩ := hrows
            have hacc :
                ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr + 1])
                  (SourceCSPGlobalDecisionProgram.initial a q input) =
                ⟨some .accept, .row (vr, some true), Sr⟩ := by
              rw [show tg + tr + 1 = 1 + (tg + tr) by omega,
                Function.iterate_add_apply, hrowrun]
              exact SourceCSPGlobalDecisionProgram.after_row_success a q vr Sr
            refine ⟨tg + tr + 1, ?_, Or.inr (Or.inr ?_)⟩
            · have hb := row_le_total a q input.length
              have hm : SourceCSPGlobalPositiveRows.physicalRowBound
                  a q input.length ≤
                  (1 + BitMachineStackGrowth.perStep
                    (SourceCSPGlobalDecisionProgram.program a q)) *
                    SourceCSPGlobalPositiveRows.physicalRowBound
                      a q input.length := by
                simpa only [one_mul] using
                  (Nat.mul_le_mul_right
                    (SourceCSPGlobalPositiveRows.physicalRowBound
                      a q input.length)
                    (show 1 ≤ 1 + BitMachineStackGrowth.perStep
                      (SourceCSPGlobalDecisionProgram.program a q) by omega))
              omega
            · exact ⟨n, m, rest, rows, vr, Sr, hinput,
                hcap.1, hcap.2, hrows, hacc⟩
        | false =>
            obtain ⟨tw, T, htw, hwriter, hout, _⟩ :=
              SourceCSPGlobalDecisionProgram.row_failure_reject a q vr Sr
            have hg := output_growth a q input (tg + tr)
              (some .afterRow) (.row (vr, some false)) Sr hrowrun
            have hfinal :
                ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr + tw])
                  (SourceCSPGlobalDecisionProgram.initial a q input) =
                ⟨none, .writer none, T⟩ := by
              rw [show tg + tr + tw = tw + (tg + tr) by omega,
                Function.iterate_add_apply, hrowrun]
              exact hwriter
            refine ⟨tg + tr + tw, ?_, Or.inl ?_⟩
            · have hb := row_le_total a q input.length
              have hc := charged_clear_bound
                (BitMachineStackGrowth.perStep
                  (SourceCSPGlobalDecisionProgram.program a q))
                (tg + tr) tw (Sr SourceCSPGlobalDecisionProgram.outputSlot).length
                (SourceCSPGlobalPositiveRows.physicalRowBound a q input.length)
                htrow htw hg
              exact hc.trans hb
            · exact ⟨_, T, hfinal, hout,
                by rw [hout]; exact SourceCSPRejectFormula.bits_not_language⟩
      · obtain ⟨tc, Sc, cc, htc, hcaprun, hbit⟩ :=
          SourceCSPGlobalCapFromLiteral.cap_from_literal a q n m
            (v₂, none) Sg hv₂ hnword hm hempty
        have hnwordL :=
          (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
            a q n m input rest hinput).1
        have hcBound := SourceCSPGlobalCapFromLiteral.capBound_uniform
          q n.bits.length m input.length hnwordL hmL
        have htcap : tg + tc ≤
            SourceCSPGuardDispatchSequence.bound a q input.length + 2 +
              SourceCSPGlobalCapFromLiteral.capBound q input.length input.length := by
          omega
        have hcapglobal :
            ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tc])
              (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨some .capCheck, .cap cc, Sc⟩ := by
          rw [show tg + tc = tc + tg by omega,
            Function.iterate_add_apply, hglobal]
          exact hcaprun
        have hbad : (Sc SourceCSPHeaderRowBridge.capSource).head? ≠
            some true := by rw [hbit]; simp [hcap]
        obtain ⟨tw, T, htw, hwriter, hout, _⟩ :=
          SourceCSPGlobalDecisionProgram.cap_failure_reject a q cc Sc hbad
        have hg := output_growth a q input (tg + tc)
          (some .capCheck) (.cap cc) Sc hcapglobal
        have hfinal :
            ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tc + tw])
              (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, .writer none, T⟩ := by
          rw [show tg + tc + tw = tw + (tg + tc) by omega,
            Function.iterate_add_apply, hcapglobal]
          exact hwriter
        refine ⟨tg + tc + tw, ?_, Or.inl ?_⟩
        · have hb := cap_le_total a q input.length
          have hc := charged_clear_bound
            (BitMachineStackGrowth.perStep
              (SourceCSPGlobalDecisionProgram.program a q))
            (tg + tc) tw (Sc SourceCSPGlobalDecisionProgram.outputSlot).length
            (SourceCSPGuardDispatchSequence.bound a q input.length + 2 +
              SourceCSPGlobalCapFromLiteral.capBound q input.length input.length)
            htcap htw hg
          exact hc.trans hb
        · exact ⟨_, T, hfinal, hout,
            by rw [hout]; exact SourceCSPRejectFormula.bits_not_language⟩

/-- The validation-success tag is an actual halt instruction. It leaves the
bank and successful row-control bit unchanged; it does not emit clauses. -/
theorem accept_one_step_halt (a q : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    advance (SourceCSPGlobalDecisionProgram.program a q)
      (⟨some .accept, .row (vr, some true), S⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (SourceCSPGlobalDecisionProgram.Control a q)) =
      ⟨none, .row (vr, some true), S⟩ := by
  rfl

/-- Every raw input halts within the same displayed fixed-parameter
polynomial plus one step. The stronger three-way state/output classification
is `raw_total_validation` above. -/
theorem raw_total_halts (a q : Nat) (input : List Bool) :
    ∃ t ≤ totalBound a q input.length,
      ∃ (c : SourceCSPGlobalDecisionProgram.Control a q)
        (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t + 1])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, c, S⟩ := by
  obtain ⟨t, ht, hcase⟩ := raw_total_validation a q input
  refine ⟨t, ht, ?_⟩
  rcases hcase with hreje | hzero | hacc
  · obtain ⟨c, S, hrun, _, _⟩ := hreje
    refine ⟨c, S, ?_⟩
    rw [Function.iterate_succ_apply', hrun]
    rfl
  · obtain ⟨S, hrun, _⟩ := hzero
    refine ⟨.prefix (SourceCSPGuardOutputCombined.zeroControl, none), S, ?_⟩
    rw [Function.iterate_succ_apply', hrun]
    rfl
  · obtain ⟨n, m, rest, rows, vr, S, _, _, _, _, hrun⟩ := hacc
    refine ⟨.row (vr, some true), S, ?_⟩
    rw [Function.iterate_succ_apply', hrun]
    exact accept_one_step_halt a q vr S


end EthInapproximability.CurrentPaper.SourceCSPGlobalTotalValidation
