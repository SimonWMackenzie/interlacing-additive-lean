import EthInapproximability.CurrentPaper.SourceCSPGlobalTotalValidation
import EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows
import EthInapproximability.CurrentPaper.SourceCSPTotalSelective

/-! Retained literal unary constraint count on the existing raw positive route. -/

namespace EthInapproximability.CurrentPaper.SourceCSPAcceptedCount

open Turing BitMachineEncoding BitMachineStackEmbedding BitMachineInline

theorem countSlot_eq_headerCount {q : Nat} :
    SourceCSPGlobalDecisionProgram.inputEmbedding (q := q)
      SourceCSPGuardDispatch.countSlot =
      SourceCSPHeaderRowBridge.count := by
  rfl

theorem prepared_count {q : Nat}
    (before : SourceCSPHeaderRowBridge.Stack q → List Bool)
    (rows cap unaryM : List Bool) :
    SourceCSPHeaderRowBridge.prepared before rows cap unaryM
      SourceCSPHeaderRowBridge.count =
      before SourceCSPHeaderRowBridge.count := by
  simp [SourceCSPHeaderRowBridge.prepared,
    SourceCSPHeaderRowBridge.count,
    SourceCSPHeaderRowBridge.rowSource,
    SourceCSPHeaderRowBridge.capSource,
    SourceCSPHeaderRowBridge.rowCap,
    SourceCSPHeaderRowBridge.loopCap,
    SourceCSPHeaderRowBridge.loopCount]

private theorem canonical_header_unique (a q n m n' m' : Nat)
    (input rest rest' : List Bool)
    (h : input = SourceCSPHeaderParse.header n m a q ++ rest)
    (h' : input = SourceCSPHeaderParse.header n' m' a q ++ rest') :
    n = n' ∧ m = m' ∧ rest = rest' := by
  have hn := EncodedCommunication.readNat_append n
    (EncodedCommunication.natField m ++
      EncodedCommunication.natField a ++
      EncodedCommunication.natField q ++ rest)
  have hn' := EncodedCommunication.readNat_append n'
    (EncodedCommunication.natField m' ++
      EncodedCommunication.natField a ++
      EncodedCommunication.natField q ++ rest')
  have heqN : (n,
      EncodedCommunication.natField m ++
        EncodedCommunication.natField a ++
        EncodedCommunication.natField q ++ rest) =
      (n',
      EncodedCommunication.natField m' ++
        EncodedCommunication.natField a ++
        EncodedCommunication.natField q ++ rest') := by
    apply Option.some.inj
    calc
      some (n, _) = EncodedCommunication.readNat input := by
        rw [h, SourceCSPHeaderParse.header]
        simpa only [List.append_assoc] using hn.symm
      _ = some (n', _) := by
        rw [h', SourceCSPHeaderParse.header]
        simpa only [List.append_assoc] using hn'
  have hnEq : n = n' := congrArg Prod.fst heqN
  have htail : EncodedCommunication.natField m ++
      EncodedCommunication.natField a ++
      EncodedCommunication.natField q ++ rest =
      EncodedCommunication.natField m' ++
        EncodedCommunication.natField a ++
        EncodedCommunication.natField q ++ rest' := by
    simpa using congrArg Prod.snd heqN
  have hmRead := EncodedCommunication.readNat_append m
    (EncodedCommunication.natField a ++
      EncodedCommunication.natField q ++ rest)
  have hmRead' := EncodedCommunication.readNat_append m'
    (EncodedCommunication.natField a ++
      EncodedCommunication.natField q ++ rest')
  have heqM : (m,
      EncodedCommunication.natField a ++
        EncodedCommunication.natField q ++ rest) =
      (m',
      EncodedCommunication.natField a ++
        EncodedCommunication.natField q ++ rest') := by
    apply Option.some.inj
    calc
      some (m, _) = EncodedCommunication.readNat
          (EncodedCommunication.natField m ++
            EncodedCommunication.natField a ++
            EncodedCommunication.natField q ++ rest) := by
        simpa only [List.append_assoc] using hmRead.symm
      _ = EncodedCommunication.readNat
          (EncodedCommunication.natField m' ++
            EncodedCommunication.natField a ++
            EncodedCommunication.natField q ++ rest') := by rw [htail]
      _ = some (m', _) := by
        simpa only [List.append_assoc] using hmRead'
  have hmEq : m = m' := congrArg Prod.fst heqM
  have htail2 : EncodedCommunication.natField a ++
      EncodedCommunication.natField q ++ rest =
      EncodedCommunication.natField a ++
        EncodedCommunication.natField q ++ rest' := by
    simpa using congrArg Prod.snd heqM
  have hrest : rest = rest' := by
    have ha := EncodedCommunication.readNat_append a
      (EncodedCommunication.natField q ++ rest)
    have ha' := EncodedCommunication.readNat_append a
      (EncodedCommunication.natField q ++ rest')
    have hqtail : EncodedCommunication.natField q ++ rest =
        EncodedCommunication.natField q ++ rest' := by
      have hpair : (a, EncodedCommunication.natField q ++ rest) =
          (a, EncodedCommunication.natField q ++ rest') := by
        apply Option.some.inj
        calc
          some (a, _) = EncodedCommunication.readNat
              (EncodedCommunication.natField a ++
                EncodedCommunication.natField q ++ rest) := by
            simpa only [List.append_assoc] using ha.symm
          _ = EncodedCommunication.readNat
              (EncodedCommunication.natField a ++
                EncodedCommunication.natField q ++ rest') := by rw [htail2]
          _ = some (a, _) := by
            simpa only [List.append_assoc] using ha'
      exact congrArg Prod.snd hpair
    exact List.append_cancel_left hqtail
  exact ⟨hnEq, hmEq, hrest⟩

/-- The existing cap-to-row preparation physically copies the unary row
count but leaves the source header's count register unchanged. -/
theorem prepare_from_cap_count (a q : Nat)
    (before : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (c : Unit × SourceCSPPositiveCapEntry.CapControl)
    (rows cap unaryM : List Bool)
    (hrows : before SourceCSPHeaderRowBridge.source = rows)
    (hcap : before SourceCSPHeaderRowBridge.capSource = true :: cap)
    (hm : before SourceCSPHeaderRowBridge.count = unaryM)
    (hblank : ∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
      before (.inr k) = []) :
    ∃ t S,
      t ≤ 1 + 2 * rows.length + 4 * cap.length +
        2 * unaryM.length + 13 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some .capCheck, .cap c, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .rowHandoff,
          .prepare SourceCSPHeaderRowBridge.prepareStart, S⟩ ∧
      (fun k => S (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        SourceCSPHeaderRowBridge.ready rows cap unaryM ∧
      S SourceCSPHeaderRowBridge.source = rows ∧
      S SourceCSPHeaderRowBridge.capSource = cap ∧
      S SourceCSPHeaderRowBridge.count = unaryM ∧
      S SourceCSPGlobalDecisionProgram.savedSource = [] ∧
      S SourceCSPGlobalDecisionProgram.copyWork = [] := by
  obtain ⟨tp, htp, hrp⟩ :=
    SourceCSPHeaderRowBridge.prepare_run before rows cap unaryM
      hrows hcap hm hblank
  have hstart := SourceCSPGlobalDecisionProgram.cap_check_good
    a q c before cap hcap
  let localCfg := SourceCSPHeaderRowBridge.start before
  have hhalt : (((advance SourceCSPHeaderRowBridge.prepareProgram)^[tp])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun x => x.l) hrp
  let read : SourceCSPGlobalDecisionProgram.Control a q →
      SourceCSPHeaderRowBridge.Control5 :=
    fun x => match x with
      | .prepare w => w
      | _ => SourceCSPHeaderRowBridge.prepareStart
  have hleft : Function.LeftInverse read
      SourceCSPGlobalDecisionProgram.Control.prepare := by
    intro w
    rfl
  obtain ⟨u, hu, hglobal⟩ := outputs
    SourceCSPGlobalDecisionProgram.Label.prepare
    SourceCSPGlobalDecisionProgram.Control.prepare
    read hleft (some .rowHandoff)
    SourceCSPHeaderRowBridge.prepareProgram
    (SourceCSPGlobalDecisionProgram.program a q)
    (fun _ => rfl) localCfg tp hhalt
  rw [hrp] at hglobal
  have hlocalStart : BitMachineInline.cfg
      SourceCSPGlobalDecisionProgram.Label.prepare
      SourceCSPGlobalDecisionProgram.Control.prepare
      (some .rowHandoff) localCfg =
      (⟨some (.prepare (.inl (.inl (.inl (.inl .scan))))),
        .prepare SourceCSPHeaderRowBridge.prepareStart, before⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (SourceCSPGlobalDecisionProgram.Control a q)) := by
    rfl
  rw [hlocalStart] at hglobal
  let S := SourceCSPHeaderRowBridge.prepared before rows cap unaryM
  refine ⟨u + 1, S, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[u + 1]) _ = _
    rw [Function.iterate_succ_apply, hstart]
    simpa only [BitMachineInline.cfg, id_eq, Option.map_none, S]
      using hglobal
  · exact SourceCSPHeaderRowBridge.prepared_ready before
      rows cap unaryM hblank
  · simp [S, SourceCSPHeaderRowBridge.prepared,
      SourceCSPHeaderRowBridge.source,
      SourceCSPHeaderRowBridge.rowSource,
      SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.rowCap,
      SourceCSPHeaderRowBridge.loopCap,
      SourceCSPHeaderRowBridge.loopCount]
    exact hrows
  · simp [S, SourceCSPHeaderRowBridge.prepared,
      SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.rowSource,
      SourceCSPHeaderRowBridge.rowCap,
      SourceCSPHeaderRowBridge.loopCap,
      SourceCSPHeaderRowBridge.loopCount]
  · exact (prepared_count before rows cap unaryM).trans hm
  · simp [S, SourceCSPHeaderRowBridge.prepared,
      SourceCSPGlobalDecisionProgram.savedSource,
      SourceCSPHeaderRowBridge.scratch,
      SourceCSPHeaderRowBridge.rowSource,
      SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.rowCap,
      SourceCSPHeaderRowBridge.loopCap,
      SourceCSPHeaderRowBridge.loopCount, hblank (.inr 4)]
  · simp [S, SourceCSPHeaderRowBridge.prepared,
      SourceCSPGlobalDecisionProgram.copyWork,
      SourceCSPHeaderRowBridge.rowSource,
      SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.rowCap,
      SourceCSPHeaderRowBridge.loopCap,
      SourceCSPHeaderRowBridge.loopCount, hblank (.inr 2)]

/-- Strengthened actual positive cap/prepare/retention/row route. The
validated raw header's unary `m` remains in its original physical cell. -/
theorem positive_rows_count (n m a q L : Nat)
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
        List.replicate (n - 1) true ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true := by
  obtain ⟨tc, Sc, cc, htc, hrc, hcap, hcount, hsource, hblank⟩ :=
    SourceCSPGlobalCapFromLiteral.cap_from_literal_success
      a q n m v before hn hsize hv hnword hm hempty hrowblank
  have hrows : Sc SourceCSPHeaderRowBridge.source = suffix := by
    rw [hsource, hsuffix]
  obtain ⟨tp, Sp, htp, hrp, hready, hsourceSp, hcapSp,
    hcountSp, hsavedSp, hworkSp⟩ :=
    prepare_from_cap_count a q Sc cc suffix
      (List.replicate (n - 1) true)
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
  have hcountSu : Su SourceCSPHeaderRowBridge.count =
      List.replicate m true :=
    (hother SourceCSPHeaderRowBridge.count
      (by simp [SourceCSPHeaderRowBridge.count,
        SourceCSPHeaderRowBridge.source])
      (by simp [SourceCSPHeaderRowBridge.count,
        SourceCSPGlobalDecisionProgram.savedSource,
        SourceCSPHeaderRowBridge.scratch])
      (by simp [SourceCSPHeaderRowBridge.count,
        SourceCSPGlobalDecisionProgram.copyWork])).trans hcountSp
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
  let cap := List.replicate (n - 1) true
  let E := SourceCSPPositiveRowTotalBridge.rowExtras m cap
  have hc : E 0 = List.replicate m true := rfl
  have hcv : E 1 = cap := rfl
  have hcs : E 3 = [] := rfl
  obtain ⟨tr, Tr, vr, br, htr, hrr, hsem⟩ :=
    SourceCSPRowLoopTotalPolynomial.rows_total_codec_cubic
      n a q m L suffix E hn hmL hsuffixL hcapL hc hcv hcs
  have hlocal : ((advance
      (SourceCSPRowLoopTotalController.program q (a ^ q)))^[tr])
      (⟨some (SourceCSPRowLoopController.adminLabel .check),
        SourceCSPRowLoopController.initialControl,
        SourceCSPHeaderRowBridge.ready suffix cap
          (List.replicate m true)⟩ :
          SourceCSPRowLoopController.Config q (a ^ q)) =
      ⟨none, (vr, some br), Tr⟩ := by
    simpa only [cap, E,
      SourceCSPPositiveRowTotalBridge.ready_eq_row_start
        suffix cap m] using hrr
  obtain ⟨ur, Sr, hur, hrrGlobal, _, hforeign⟩ :=
    SourceCSPGlobalRowsFromReady.row_lift a q Su tr Tr vr br
      suffix cap (List.replicate m true) hreadySu hlocal
  have hsavedEnd : Sr SourceCSPGlobalDecisionProgram.savedSource = suffix := by
    have h := hforeign SourceCSPGlobalDecisionProgram.savedSource
      (by
        rintro ⟨j, hj⟩
        cases j with
        | inl j => simp [SourceCSPHeaderRowBridge.rowEmbedding,
            SourceCSPGlobalDecisionProgram.savedSource,
            SourceCSPHeaderRowBridge.scratch] at hj
        | inr j => fin_cases j <;> simp
            [SourceCSPHeaderRowBridge.rowEmbedding,
              SourceCSPGlobalDecisionProgram.savedSource,
              SourceCSPHeaderRowBridge.scratch] at hj)
    exact h.trans hsavedSu
  have hcapEnd : Sr SourceCSPHeaderRowBridge.capSource = cap := by
    have h := hforeign SourceCSPHeaderRowBridge.capSource
      (by
        rintro ⟨j, hj⟩
        cases j <;> simp [SourceCSPHeaderRowBridge.rowEmbedding,
          SourceCSPHeaderRowBridge.capSource] at hj)
    exact h.trans hcapSu
  have hcountEnd : Sr SourceCSPHeaderRowBridge.count =
      List.replicate m true := by
    have h := hforeign SourceCSPHeaderRowBridge.count
      (by
        rintro ⟨j, hj⟩
        cases j <;> simp [SourceCSPHeaderRowBridge.rowEmbedding,
          SourceCSPHeaderRowBridge.count] at hj)
    exact h.trans hcountSu
  refine ⟨tc + tp + tu + ur, Sr, vr, br, ?_, ?_, hsem,
    hsavedEnd, hcapEnd, hcountEnd⟩
  · simp only [List.length_replicate] at htp
    omega
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))
      ^[tc + tp + tu + ur]) _ = _
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
    rw [show tc + tp + tu + ur = ur + (tu + (tp + tc)) by omega,
      Function.iterate_add_apply, hcpu, hrrGlobal]

private theorem positive_route_of_accept (a q : Nat) (input : List Bool)
    (tp t : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
    (Sp : SourceCSPInputFrame.Stack → List Bool)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hrp : ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v, none), Sp⟩)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    v.2.2 = some .positive := by
  have impossible (u : Nat) (c : SourceCSPGuardOutputCombined.Control)
      (T : SourceCSPInputFrame.Stack → List Bool)
      (hlocal : ((advance
        (SourceCSPGuardOutputCombined.program a q))^[u])
        (SourceCSPGuardOutputCombined.initial a q input) =
          ⟨none, c, T⟩)
      (hnot : c.1.2.2 ≠ some .positive) : False := by
    obtain ⟨ug, U, _, hglobal, _⟩ :=
      SourceCSPGlobalDecisionProgram.lift_nonpositive_terminal
        a q input u c T hlocal hnot
    have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
      (SourceCSPGlobalDecisionProgram.program a q)
      (SourceCSPGlobalDecisionProgram.initial a q input)
      ug t (by rw [hglobal]) (by rw [hacc])
    have hc := congrArg (fun x => x.var) heq
    rw [hglobal, hacc] at hc
    cases hc
  cases hv : v.2.2 with
  | none =>
      have hroute : SourceCSPGuardOutputCombined.routeRun a q 2 v Sp =
          ⟨none, (v, none), Sp⟩ := by
        simp [SourceCSPGuardOutputCombined.routeRun,
          Function.iterate_succ_apply', advance, TM2.step,
          TM2.stepAux, SourceCSPGuardOutputCombined.program, hv]
      have hlocal : ((advance
          (SourceCSPGuardOutputCombined.program a q))^[tp + 2])
          (SourceCSPGuardOutputCombined.initial a q input) =
          ⟨none, (v, none), Sp⟩ := by
        rw [show tp + 2 = 2 + tp by omega,
          Function.iterate_add_apply, hrp]
        exact hroute
      exact False.elim (impossible (tp + 2) (v, none) Sp hlocal
        (by simp [hv]))
  | some tag =>
      cases tag with
      | positive => rfl
      | reject =>
          obtain ⟨tr, T, _, hroute, _, _⟩ :=
            SourceCSPGuardOutputCombined.route_reject a q v Sp hv
          have hlocal : ((advance
              (SourceCSPGuardOutputCombined.program a q))^[tp + tr])
              (SourceCSPGuardOutputCombined.initial a q input) =
              ⟨none, (SourceCSPGuardOutputCombined.rejectControl, none), T⟩ := by
            rw [show tp + tr = tr + tp by omega,
              Function.iterate_add_apply, hrp]
            exact hroute
          exact False.elim (impossible (tp + tr)
            (SourceCSPGuardOutputCombined.rejectControl, none) T hlocal
            (by simp [SourceCSPGuardOutputCombined.rejectControl]))
      | zero =>
          obtain ⟨tr, T, _, hroute, _, _⟩ :=
            SourceCSPGuardOutputCombined.route_zero a q v Sp hv
          have hlocal : ((advance
              (SourceCSPGuardOutputCombined.program a q))^[tp + tr])
              (SourceCSPGuardOutputCombined.initial a q input) =
              ⟨none, (SourceCSPGuardOutputCombined.zeroControl, none), T⟩ := by
            rw [show tp + tr = tr + tp by omega,
              Function.iterate_add_apply, hrp]
            exact hroute
          exact False.elim (impossible (tp + tr)
            (SourceCSPGuardOutputCombined.zeroControl, none) T hlocal
            (by simp [SourceCSPGuardOutputCombined.zeroControl]))

/-- An actual accepting halt of the raw global validator retains the
literal unary constraint count from its canonical source header. No parsed
header bank or count word is supplied as a hypothesis. -/
theorem raw_accepted_count (a q : Nat) (input : List Bool)
    (t : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    ∃ (n m : Nat) (rest : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n a q),
      input = SourceCSPHeaderParse.header n m a q ++ rest ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
        some (rows, []) ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true := by
  obtain ⟨tg, _, c, G, hglobal, ts, _, d, W, hselect, hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective a q input
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input)
    tg t (by rw [hglobal]) (by rw [hacc])
  have hcontrol : c = .row (vr, some true) := by
    have h := congrArg (fun x => x.var) heq
    simpa only [hglobal, hacc] using h
  have hbank : G = S := by
    have h := congrArg (fun x => x.stk) heq
    simpa only [hglobal, hacc] using h
  rcases hcase with hreje | hzero | hgood
  · have hfalse := hreje.1
    rw [hcontrol] at hfalse
    simp [SourceCSPSelectiveStage.acceptedControl] at hfalse
  · have hfalse := hzero.1
    rw [hcontrol] at hfalse
    cases hfalse
  · obtain ⟨n, m, rest, rows, vr₀, hc, hstage, hinput,
      hn, hsize, hmL, hread, hsaved, hcap, _⟩ := hgood
    obtain ⟨tp, v, Sp, _, hrp, hpositive⟩ :=
      SourceCSPGlobalPositiveLiteral.positive_literal a q input
    have hv : v.2.2 = some .positive :=
      positive_route_of_accept a q input tp t v Sp vr S hrp hacc
    obtain ⟨n', m', tg', rest', G', _, hprefix,
      hinput', hnword, _, hrest, hm, hmL', hempty, hrowblank⟩ :=
      hpositive hv
    obtain ⟨rfl, rfl, rfl⟩ :=
      canonical_header_unique a q n m n' m' input rest rest'
        hinput hinput'
    have hsuffixL :=
      (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
        a q n m input rest hinput).2.2
    obtain ⟨tr, R, vr', b, _, hrr, hsem, _, _, hcount⟩ :=
      positive_rows_count n m a q input.length rest (v, none) G'
        hn hsize hmL' hsuffixL hv hnword hm hrest
        hempty hrowblank
    have hb : b = true := hsem.mpr ⟨rows, hread⟩
    subst b
    have hrow : ((advance
        (SourceCSPGlobalDecisionProgram.program a q))^[tg' + tr])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨some .afterRow, .row (vr', some true), R⟩ := by
      rw [show tg' + tr = tr + tg' by omega,
        Function.iterate_add_apply, hprefix]
      exact hrr
    have hterminal : ((advance
        (SourceCSPGlobalDecisionProgram.program a q))^[tg' + tr + 2])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr', some true), R⟩ := by
      rw [show tg' + tr + 2 = 2 + (tg' + tr) by omega,
        Function.iterate_add_apply, hrow]
      simp only [Function.iterate_succ_apply, Function.iterate_zero,
        Function.id_def]
      rw [SourceCSPGlobalDecisionProgram.after_row_success a q vr' R]
      exact SourceCSPGlobalTotalValidation.accept_one_step_halt a q vr' R
    have heq' := SourceCSPRowLoopTotalHaltCompare.halted_unique
      (SourceCSPGlobalDecisionProgram.program a q)
      (SourceCSPGlobalDecisionProgram.initial a q input)
      (tg' + tr + 2) t (by rw [hterminal]) (by rw [hacc])
    have hS : R = S := by
      have h := congrArg (fun x => x.stk) heq'
      simpa only [hterminal, hacc] using h
    exact ⟨n, m, rest, rows, hinput, hread, hS ▸ hcount⟩

/-- Match the recovered unary count to any already-proved canonical header
decomposition of the same raw input, such as the all-raw first-row theorem. -/
theorem raw_accepted_count_at (a q n m : Nat)
    (input rest : List Bool)
    (hinput : input = SourceCSPHeaderParse.header n m a q ++ rest)
    (t : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    S SourceCSPHeaderRowBridge.count = List.replicate m true := by
  obtain ⟨n', m', rest', rows', hinput', _, hcount⟩ :=
    raw_accepted_count a q input t vr S hacc
  obtain ⟨_, hmeq, _⟩ :=
    canonical_header_unique a q n m n' m' input rest rest'
      hinput hinput'
  simpa only [hmeq] using hcount


end EthInapproximability.CurrentPaper.SourceCSPAcceptedCount
