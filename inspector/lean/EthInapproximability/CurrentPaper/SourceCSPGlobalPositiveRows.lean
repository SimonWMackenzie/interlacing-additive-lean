import EthInapproximability.CurrentPaper.SourceCSPGlobalRowsFromReady
import EthInapproximability.CurrentPaper.SourceCSPGlobalRetentionRun

/-!
# Literal positive branch through the corrected row validator

This composes the physical cap, four-copy row preparation, and corrected
all-input row loop on one global instruction table. The result is a checked
finite-control row-validity bit, before clause emission.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows

open Turing BitMachineEncoding

theorem positive_rows_from_literal (n m a q L : Nat)
    (suffix : List Bool)
    (v : SourceCSPGuardOutputCombined.Control)
    (before : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m)
    (hmL : m ≤ L) (hsuffixL : suffix.length ≤ L)
    (hv : v.1.2.2 = some .positive)
    (hnword : before (SourceCSPGlobalDecisionProgram.inputEmbedding
      SourceCSPGuardDispatch.vertexSlot) = n.bits)
    (hm : before (SourceCSPGlobalDecisionProgram.inputEmbedding
      SourceCSPGuardDispatch.countSlot) = List.replicate m true)
    (hsuffix : before SourceCSPHeaderRowBridge.source = suffix)
    (hempty : ∀ k : Fin 7,
      before (SourceCSPGlobalDecisionProgram.capEmbedding (.inr k)) = [])
    (hrowblank : ∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
      before (.inr k) = []) :
    ∃ (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
      (vr : SourceCSPRowLoopController.QueryControl ×
        SourceCSPRowLoopController.ResetControl) (b : Bool),
      t ≤ SourceCSPGlobalCapFromLiteral.capBound q n.bits.length m +
        (1 + 2 * suffix.length + 4 * (n - 1) + 2 * m + 13) +
        (2 * suffix.length + 4) +
        SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) *
          (L + 1) ^ 3 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some .afterPrefix, .prefix v, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .afterRow, .row (vr, some b), S⟩ ∧
      (b = true ↔ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
          some (rows, [])) ∧
      S SourceCSPGlobalDecisionProgram.savedSource = suffix ∧
      S SourceCSPHeaderRowBridge.capSource =
        List.replicate (n - 1) true := by
  obtain ⟨tc, Sc, cc, htc, hrc, hcap, hcount, hsource, hblank⟩ :=
    SourceCSPGlobalCapFromLiteral.cap_from_literal_success
      a q n m v before hn hsize hv hnword hm hempty hrowblank
  have hrows : Sc SourceCSPHeaderRowBridge.source = suffix := by
    rw [hsource, hsuffix]
  obtain ⟨tp, Sp, htp, hrp, hready, hsourceSp, hcapSp, hsavedSp,
    hworkSp⟩ :=
    SourceCSPGlobalPrepareFromCap.prepare_from_cap
      a q Sc cc suffix (List.replicate (n - 1) true)
      (List.replicate m true) hrows hcap hcount hblank
  have hcapL : n - 1 ≤ q * L := by
    have hqm : q * m ≤ q * L := Nat.mul_le_mul_left q hmL
    omega
  obtain ⟨tu, Su, htu, hru, _, hsavedSu, hworkSu, hother⟩ :=
    SourceCSPGlobalRetentionRun.retained_handoff
      a q (.prepare SourceCSPHeaderRowBridge.prepareStart)
      Sp suffix hsourceSp hsavedSp hworkSp
  have hcapSu : Su SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true :=
    (hother SourceCSPHeaderRowBridge.capSource
      (by simp [SourceCSPHeaderRowBridge.capSource,
        SourceCSPHeaderRowBridge.source])
      (by simp [SourceCSPHeaderRowBridge.capSource,
        SourceCSPGlobalDecisionProgram.savedSource,
        SourceCSPHeaderRowBridge.scratch])
      (by simp [SourceCSPHeaderRowBridge.capSource,
        SourceCSPGlobalDecisionProgram.copyWork])).trans hcapSp
  have hreadySu :
      (fun k => Su (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        SourceCSPHeaderRowBridge.ready suffix
          (List.replicate (n - 1) true) (List.replicate m true) := by
    funext k
    have hsourceK : SourceCSPHeaderRowBridge.rowEmbedding k ≠
        SourceCSPHeaderRowBridge.source := by
      cases k <;> simp [SourceCSPHeaderRowBridge.rowEmbedding,
        SourceCSPHeaderRowBridge.source]
    have hsavedK : SourceCSPHeaderRowBridge.rowEmbedding k ≠
        SourceCSPGlobalDecisionProgram.savedSource := by
      cases k with
      | inl k => simp [SourceCSPHeaderRowBridge.rowEmbedding,
          SourceCSPGlobalDecisionProgram.savedSource,
          SourceCSPHeaderRowBridge.scratch]
      | inr k => fin_cases k <;> simp
          [SourceCSPHeaderRowBridge.rowEmbedding,
          SourceCSPGlobalDecisionProgram.savedSource,
          SourceCSPHeaderRowBridge.scratch]
    have heq : Su (SourceCSPHeaderRowBridge.rowEmbedding k) =
        Sp (SourceCSPHeaderRowBridge.rowEmbedding k) := by
      by_cases hk : SourceCSPHeaderRowBridge.rowEmbedding k =
          SourceCSPGlobalDecisionProgram.copyWork
      · rw [hk, hworkSu, hworkSp]
      · exact hother _ hsourceK hsavedK hk
    exact heq.trans (congrFun hready k)
  obtain ⟨tr, Sr, vr, br, htr, hrr, hsem, hsavedEnd,
    hcapEnd⟩ :=
    SourceCSPGlobalRowsFromReady.global_rows_total
      n m a q L suffix Su hn hmL hsuffixL hcapL hreadySu
  refine ⟨tc + tp + tu + tr, Sr, vr, br, ?_, ?_, hsem,
    hsavedEnd.trans hsavedSu, hcapEnd.trans hcapSu⟩
  · simp only [List.length_replicate] at htp
    omega
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tc + tp + tu + tr]) _ = _
    have hcp : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tp + tc])
        (⟨some .afterPrefix, .prefix v, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .rowHandoff,
          .prepare SourceCSPHeaderRowBridge.prepareStart, Sp⟩ := by
      rw [Function.iterate_add_apply, hrc, hrp]
    have hcpu : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tu + (tp + tc)])
        (⟨some .afterPrefix, .prefix v, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some (.row (SourceCSPRowLoopController.adminLabel .check)),
          .row SourceCSPRowLoopController.initialControl, Su⟩ := by
      rw [Function.iterate_add_apply, hcp, hru]
    rw [show tc + tp + tu + tr = tr + (tu + (tp + tc)) by omega,
      Function.iterate_add_apply, hcpu, hrr]

/-- Every actual raw input selecting the positive guard tag and passing the
physical vertex cap reaches the corrected all-row decision. The transition
bound is a displayed fixed-`a,q` polynomial in raw input length. -/
theorem raw_positive_rows (a q : Nat) (input : List Bool) :
    ∃ (tp : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
      (Sp : SourceCSPInputFrame.Stack → List Bool),
      tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
        (SourceCSPGuardOutputCombined.initial a q input) =
          (⟨some .route, (v, none), Sp⟩ :
            TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
              (SourceCSPGuardOutputCombined.Label a q)
              SourceCSPGuardOutputCombined.Control) ∧
      (v.2.2 = some .positive →
        ∃ (n m : Nat) (rest : List Bool),
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          (0 < n ∧ n ≤ q * m →
            ∃ (t : Nat)
              (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
              (vr : SourceCSPRowLoopController.QueryControl ×
                SourceCSPRowLoopController.ResetControl) (b : Bool),
              t ≤ SourceCSPGuardDispatchSequence.bound a q input.length + 2 +
                SourceCSPGlobalCapFromLiteral.capBound q input.length
                  input.length +
                (1 + 2 * input.length + 4 * (q * input.length) +
                  2 * input.length + 13) +
                (2 * input.length + 4) +
                SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) *
                  (input.length + 1) ^ 3 ∧
              ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
                (SourceCSPGlobalDecisionProgram.initial a q input) =
                  (⟨some .afterRow, .row (vr, some b), S⟩ :
                    TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                      (SourceCSPGlobalDecisionProgram.Label a q)
                      (SourceCSPGlobalDecisionProgram.Control a q)) ∧
              (b = true ↔ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
                SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
                  some (rows, [])) ∧
              S SourceCSPGlobalDecisionProgram.savedSource = rest ∧
              S SourceCSPHeaderRowBridge.capSource =
                List.replicate (n - 1) true)) := by
  obtain ⟨tp, v, Sp, htp, hrp, hpositive⟩ :=
    SourceCSPGlobalPositiveLiteral.positive_literal a q input
  refine ⟨tp, v, Sp, htp, hrp, ?_⟩
  intro hv
  obtain ⟨n, m, tg, rest, S₀, htg, hglobal, hinput,
    hnword, _, hrest, hm, hmL, hempty, hrowblank⟩ := hpositive hv
  refine ⟨n, m, rest, hinput, ?_⟩
  rintro ⟨hn, hsize⟩
  have hsource : S₀ SourceCSPHeaderRowBridge.source = rest := hrest
  have hwordL := (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
    a q n m input rest hinput).1
  have hsuffixL := (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
    a q n m input rest hinput).2.2
  obtain ⟨tr, S, vr, br, htr, hrr, hsem, hsaved, hcap⟩ :=
    positive_rows_from_literal n m a q input.length rest
      (v, none) S₀ hn hsize hmL hsuffixL hv
      hnword hm hsource hempty hrowblank
  have hcapBound := SourceCSPGlobalCapFromLiteral.capBound_uniform
    q n.bits.length m input.length hwordL hmL
  have hcapL : n - 1 ≤ q * input.length := by
    have hqm : q * m ≤ q * input.length := Nat.mul_le_mul_left q hmL
    omega
  refine ⟨tg + tr, S, vr, br, ?_, ?_, hsem, hsaved, hcap⟩
  · omega
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr]) _ = _
    rw [show tg + tr = tr + tg by omega,
      Function.iterate_add_apply, hglobal, hrr]

end EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows
