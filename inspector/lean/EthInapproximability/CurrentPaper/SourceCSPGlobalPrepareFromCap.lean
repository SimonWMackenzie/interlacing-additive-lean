import EthInapproximability.CurrentPaper.SourceCSPGlobalCapFromLiteral

/-!
# Literal cap-to-row preparation in the global table

The checked cap bit is popped and the raw suffix, unary cap, and unary row
count are copied into the corrected row-loop bank. This owner stops at the
row handoff; it does not infer row acceptance from an output-size estimate.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalPrepareFromCap

open Turing BitMachineEncoding BitMachineInline

theorem prepare_from_cap (a q : Nat)
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
        ⟨some .rowHandoff, .prepare SourceCSPHeaderRowBridge.prepareStart, S⟩ ∧
      (fun k => S (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        SourceCSPHeaderRowBridge.ready rows cap unaryM ∧
      S SourceCSPHeaderRowBridge.source = rows ∧
      S SourceCSPHeaderRowBridge.capSource = cap ∧
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
  refine ⟨u + 1, S, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[u + 1]) _ = _
    rw [Function.iterate_succ_apply, hstart]
    simpa only [BitMachineInline.cfg, id_eq, Option.map_none,
      S] using hglobal
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

end EthInapproximability.CurrentPaper.SourceCSPGlobalPrepareFromCap
