import EthInapproximability.CurrentPaper.MatrixTableInterlaceProtectedBridge
import EthInapproximability.CurrentPaper.MatrixWeightedPostProtectedInterlace
import EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriterRuns

/-!
Full physical-bank join after the protected writer. The initial outer scalar
banks remain explicitly supplied; this file never treats the proof-side
ordinal permutations as machine-computed data.
-/

namespace EthInapproximability.CurrentPaper.ProtectedFullBankBridgeScratch

open MatrixTableInterlaceProtectedBridge

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-- The bridge changes no outer bank other than the five declared target
stacks. In particular all scalar, foreign, nested control, and inner banks
are carried unchanged from the explicitly supplied initial outer frame. -/
theorem bridge_outer_untouched
    (d : MatrixTableInterlaceOuterJoin.Config)
    (cf : MatrixWeightedOrderWriter.Config) (rows cols : ℕ)
    (k : OStack)
    (h₁ : k ≠ oSizeRows) (h₂ : k ≠ oSizeCols)
    (h₃ : k ≠ oWriterRows) (h₄ : k ≠ oWriterCols)
    (h₅ : k ≠ oWriterSource) :
    bridgeAfter (writerFrame (emptyOuter d) cf).stk rows cols (.inr k) =
      d.stk k := by
  have hs₁ : (Sum.inr k : Stack) ≠ sizeRows := by
    change (Sum.inr k : Stack) ≠ Sum.inr oSizeRows
    intro h; exact h₁ (Sum.inr.inj h)
  have hs₂ : (Sum.inr k : Stack) ≠ sizeCols := by
    change (Sum.inr k : Stack) ≠ Sum.inr oSizeCols
    intro h; exact h₂ (Sum.inr.inj h)
  have hs₃ : (Sum.inr k : Stack) ≠ writerRows := by
    change (Sum.inr k : Stack) ≠ Sum.inr oWriterRows
    intro h; exact h₃ (Sum.inr.inj h)
  have hs₄ : (Sum.inr k : Stack) ≠ writerCols := by
    change (Sum.inr k : Stack) ≠ Sum.inr oWriterCols
    intro h; exact h₄ (Sum.inr.inj h)
  have hs₅ : (Sum.inr k : Stack) ≠ writerSource := by
    change (Sum.inr k : Stack) ≠ Sum.inr oWriterSource
    intro h; exact h₅ (Sum.inr.inj h)
  have hbridge (S : Stack → List Bool) :
      bridgeAfter S rows cols (.inr k) = S (.inr k) := by
    simp [bridgeAfter, moved, duplicated, Function.update_apply,
      hs₁, hs₂, hs₃, hs₄, hs₅, wRows, wCols, wWord, wTemp]
  rw [hbridge]
  change (emptyOuter d).stk k = d.stk k
  simp [emptyOuter, Function.update_apply, h₁, h₂, h₃, h₄, h₅]

theorem outerReady_first_other
    (B r rows cols b c s lambda : ℕ)
    (f g : Fin rows → Fin cols → Bool)
    (k : MatrixTableInterlaceCombined.Stack)
    (hk₀ : k ≠ (.inl (0 : Fin 11)))
    (hks : k ≠ (.inr (.inl (.inl (17 : Fin 20))))) :
    (outerReady B r rows cols b c s lambda f).stk (firstCombinedO k) =
      (outerReady B r rows cols b c s lambda g).stk (firstCombinedO k) := by
  calc
    _ = (MatrixTableInterlaceCombined.bridgeCfg
        MatrixTableInterlaceCombined.start (2^r) rows cols
        (MatrixMaterialization.rowMajor f) [] [] [] [] []).stk k :=
      outerReady_first_bank B r rows cols b c s lambda f k hk₀
    _ = (MatrixTableInterlaceCombined.bridgeCfg
        MatrixTableInterlaceCombined.start (2^r) rows cols
        (MatrixMaterialization.rowMajor g) [] [] [] [] []).stk k :=
      MatrixTableInterlaceProtectedBridge.combined_other r rows cols f g k hks
    _ = _ :=
      (outerReady_first_bank B r rows cols b c s lambda g k hk₀).symm

theorem emptyOuter_other (d : MatrixTableInterlaceOuterJoin.Config)
    (k : OStack)
    (h₁ : k ≠ oSizeRows) (h₂ : k ≠ oSizeCols)
    (h₃ : k ≠ oWriterRows) (h₄ : k ≠ oWriterCols)
    (h₅ : k ≠ oWriterSource) :
    (emptyOuter d).stk k = d.stk k := by
  simp [emptyOuter, Function.update_apply, h₁, h₂, h₃, h₄, h₅]

/-- The supplied skeleton has no hidden dependence on the protected table:
its table-dependent first source word is precisely among the five cleared
cells, while the future second-restoration word is not in the initial bank. -/
theorem emptyOuter_table_independent
    (B r rows cols b c s lambda : ℕ)
    (f g : Fin rows → Fin cols → Bool) :
    emptyOuter (outerReady B r rows cols b c s lambda f) =
      emptyOuter (outerReady B r rows cols b c s lambda g) := by
  have hl : (emptyOuter (outerReady B r rows cols b c s lambda f)).l =
      (emptyOuter (outerReady B r rows cols b c s lambda g)).l := by
    change (outerReady B r rows cols b c s lambda f).l =
      (outerReady B r rows cols b c s lambda g).l
    simp only [outerReady, MatrixTableInterlaceOuterJoin.outerFrame,
      BitMachineComposition.liftCfg, MatrixOuterWidthMachine.startCfg,
      BitMachine.Machine.init]
  have hv : (emptyOuter (outerReady B r rows cols b c s lambda f)).var =
      (emptyOuter (outerReady B r rows cols b c s lambda g)).var := by
    change (outerReady B r rows cols b c s lambda f).var =
      (outerReady B r rows cols b c s lambda g).var
    simp only [outerReady, MatrixTableInterlaceOuterJoin.outerFrame,
      BitMachineComposition.liftCfg,
      MatrixTableInterlaceOuterJoin.emptyInner,
      MatrixTableInterlaceOuterJoin.readyInner,
      MatrixTableInterlaceScalarJoin.restorationFrame,
      MatrixTableInterlaceScalarJoin.emptyDouble,
      MatrixTableInterlaceDouble.firstFrame,
      MatrixTableInterlaceDouble.secondPrepared,
      MatrixTableInterlaceDouble.firstPrepared,
      MatrixTableInterlaceFirstTranspose.firstFrame,
      MatrixTableInterlaceFirstRestoration.combinedFrame,
      MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.cfg]
  have hs : (emptyOuter (outerReady B r rows cols b c s lambda f)).stk =
      (emptyOuter (outerReady B r rows cols b c s lambda g)).stk := by
    funext k
    cases k with
    | inl k =>
      simpa only [emptyOuter, Function.update_apply,
        oSizeRows, oSizeCols, oWriterRows, oWriterCols,
        oWriterSource, firstCombinedO, Sum.inl_ne_inr,
        Sum.inl.injEq, if_false] using
        (outerReady_outer_bank B r rows cols b c s lambda f g k)
    | inr k =>
      cases k with
      | inl k =>
        have h :
            (outerReady B r rows cols b c s lambda f).stk
              (.inr (.inl k)) =
            (outerReady B r rows cols b c s lambda g).stk
              (.inr (.inl k)) := by
          simp only [outerReady, MatrixTableInterlaceOuterJoin.outerFrame,
            MatrixTableInterlaceOuterJoin.emptyInner,
            MatrixTableInterlaceOuterJoin.readyInner,
            MatrixTableInterlaceScalarJoin.restorationFrame,
            BitMachineComposition.liftCfg,
            MatrixTableInterlaceOuterJoin.firstSlot,
            Function.update_apply, Sum.inl_ne_inr, Sum.elim_inl,
            Sum.elim_inr, if_false]
        simpa only [emptyOuter, Function.update_apply,
          oSizeRows, oSizeCols, oWriterRows, oWriterCols,
          oWriterSource, firstCombinedO, Sum.inl_ne_inr,
          Sum.inr.injEq, if_false] using h
      | inr k =>
        cases k with
        | inr k =>
          have h :
              (outerReady B r rows cols b c s lambda f).stk
                (.inr (.inr (.inr k))) =
              (outerReady B r rows cols b c s lambda g).stk
                (.inr (.inr (.inr k))) := by
            simp only [outerReady,
              MatrixTableInterlaceOuterJoin.outerFrame,
              MatrixTableInterlaceOuterJoin.emptyInner,
              MatrixTableInterlaceOuterJoin.readyInner,
              MatrixTableInterlaceScalarJoin.restorationFrame,
              MatrixTableInterlaceScalarJoin.emptyDouble,
              MatrixTableInterlaceDouble.firstFrame,
              BitMachineComposition.liftCfg,
              MatrixTableInterlaceOuterJoin.firstSlot,
              Function.update_apply, Sum.elim_inr,
              Sum.inl_ne_inr, if_false]
          simpa only [emptyOuter, Function.update_apply,
            oSizeRows, oSizeCols, oWriterRows, oWriterCols,
            oWriterSource, firstCombinedO, Sum.inl_ne_inr,
            Sum.inr.injEq, if_false] using h
        | inl k =>
          cases k with
          | inr k =>
            have h :
                (outerReady B r rows cols b c s lambda f).stk
                  (.inr (.inr (.inl (.inr k)))) =
                (outerReady B r rows cols b c s lambda g).stk
                  (.inr (.inr (.inl (.inr k)))) := by
              simp only [outerReady,
                MatrixTableInterlaceOuterJoin.outerFrame,
                MatrixTableInterlaceOuterJoin.emptyInner,
                MatrixTableInterlaceOuterJoin.readyInner,
                MatrixTableInterlaceScalarJoin.restorationFrame,
                MatrixTableInterlaceScalarJoin.emptyDouble,
                MatrixTableInterlaceDouble.firstFrame,
                MatrixTableInterlaceDouble.firstPrepared,
                MatrixTableInterlaceFirstTranspose.firstFrame,
                BitMachineComposition.liftCfg,
                MatrixTableInterlaceOuterJoin.firstSlot,
                MatrixTableInterlaceOuterJoin.firstBlock,
                Function.update_apply, Sum.elim_inr, Sum.elim_inl,
                Sum.inl_ne_inr, if_false]
            simpa only [emptyOuter, Function.update_apply,
              oSizeRows, oSizeCols, oWriterRows, oWriterCols,
              oWriterSource, firstCombinedO, Sum.inl_ne_inr,
              Sum.inr.injEq, if_false] using h
          | inl k =>
            cases k with
            | inr k =>
              have h :
                  (outerReady B r rows cols b c s lambda f).stk
                    (.inr (.inr (.inl (.inl (.inr k))))) =
                  (outerReady B r rows cols b c s lambda g).stk
                    (.inr (.inr (.inl (.inl (.inr k))))) := by
                simp only [outerReady,
                  MatrixTableInterlaceOuterJoin.outerFrame,
                  MatrixTableInterlaceOuterJoin.emptyInner,
                  MatrixTableInterlaceOuterJoin.readyInner,
                  MatrixTableInterlaceScalarJoin.restorationFrame,
                  MatrixTableInterlaceScalarJoin.emptyDouble,
                  MatrixTableInterlaceDouble.firstFrame,
                  MatrixTableInterlaceDouble.firstPrepared,
                  MatrixTableInterlaceFirstTranspose.firstFrame,
                  MatrixTableInterlaceFirstRestoration.combinedFrame,
                  BitMachineComposition.liftCfg,
                  MatrixTableInterlaceOuterJoin.firstSlot,
                  MatrixTableInterlaceOuterJoin.firstBlock,
                  Function.update_apply, Sum.elim_inr, Sum.elim_inl,
                  Sum.inl_ne_inr, if_false]
              simpa only [emptyOuter, Function.update_apply,
                oSizeRows, oSizeCols, oWriterRows, oWriterCols,
                oWriterSource, firstCombinedO, Sum.inl_ne_inr,
                Sum.inr.injEq, if_false] using h
            | inl k =>
              by_cases h₁ : k = (.inl (1 : Fin 11))
              · subst k
                change (emptyOuter (outerReady B r rows cols b c s lambda f)).stk
                    oSizeRows =
                  (emptyOuter (outerReady B r rows cols b c s lambda g)).stk
                    oSizeRows
                rw [emptyOuter_sizeRows, emptyOuter_sizeRows]
              by_cases h₂ : k = (.inl (2 : Fin 11))
              · subst k
                change (emptyOuter (outerReady B r rows cols b c s lambda f)).stk
                    oSizeCols =
                  (emptyOuter (outerReady B r rows cols b c s lambda g)).stk
                    oSizeCols
                rw [emptyOuter_sizeCols, emptyOuter_sizeCols]
              by_cases h₃ : k = (.inr (.inl (.inl (0 : Fin 20))))
              · subst k
                change (emptyOuter (outerReady B r rows cols b c s lambda f)).stk
                    oWriterRows =
                  (emptyOuter (outerReady B r rows cols b c s lambda g)).stk
                    oWriterRows
                rw [emptyOuter_writerRows, emptyOuter_writerRows]
              by_cases h₄ : k = (.inr (.inl (.inl (7 : Fin 20))))
              · subst k
                change (emptyOuter (outerReady B r rows cols b c s lambda f)).stk
                    oWriterCols =
                  (emptyOuter (outerReady B r rows cols b c s lambda g)).stk
                    oWriterCols
                rw [emptyOuter_writerCols, emptyOuter_writerCols]
              by_cases h₅ : k = (.inr (.inl (.inl (17 : Fin 20))))
              · subst k
                change (emptyOuter (outerReady B r rows cols b c s lambda f)).stk
                    oWriterSource =
                  (emptyOuter (outerReady B r rows cols b c s lambda g)).stk
                    oWriterSource
                rw [emptyOuter_writerSource, emptyOuter_writerSource]
              have hk₁ : firstCombinedO k ≠ oSizeRows := by
                intro h; exact h₁ (by simpa [firstCombinedO, oSizeRows] using h)
              have hk₂ : firstCombinedO k ≠ oSizeCols := by
                intro h; exact h₂ (by simpa [firstCombinedO, oSizeCols] using h)
              have hk₃ : firstCombinedO k ≠ oWriterRows := by
                intro h; exact h₃ (by simpa [firstCombinedO, oWriterRows] using h)
              have hk₄ : firstCombinedO k ≠ oWriterCols := by
                intro h; exact h₄ (by simpa [firstCombinedO, oWriterCols] using h)
              have hk₅ : firstCombinedO k ≠ oWriterSource := by
                intro h; exact h₅ (by simpa [firstCombinedO, oWriterSource] using h)
              change (emptyOuter (outerReady B r rows cols b c s lambda f)).stk
                  (firstCombinedO k) =
                (emptyOuter (outerReady B r rows cols b c s lambda g)).stk
                  (firstCombinedO k)
              rw [emptyOuter_other _ _ hk₁ hk₂ hk₃ hk₄ hk₅,
                emptyOuter_other _ _ hk₁ hk₂ hk₃ hk₄ hk₅]
              by_cases h₀ : k = (.inl (0 : Fin 11))
              · subst k
                have hf :
                    (outerReady B r rows cols b c s lambda f).stk
                      (firstCombinedO (.inl (0 : Fin 11))) = [] := by
                  simpa only [outerReady, firstCombinedO,
                    MatrixTableInterlaceOuterJoin.outerFrame,
                    BitMachineComposition.liftCfg, Sum.elim_inr] using
                    (MatrixTableInterlaceOuterJoin.emptyInner_first
                      B r rows cols b c s f)
                have hg :
                    (outerReady B r rows cols b c s lambda g).stk
                      (firstCombinedO (.inl (0 : Fin 11))) = [] := by
                  simpa only [outerReady, firstCombinedO,
                    MatrixTableInterlaceOuterJoin.outerFrame,
                    BitMachineComposition.liftCfg, Sum.elim_inr] using
                    (MatrixTableInterlaceOuterJoin.emptyInner_first
                      B r rows cols b c s g)
                rw [hf,hg]
              · exact outerReady_first_other B r rows cols b c s lambda
                  f g k h₀ h₅
  cases hleft : emptyOuter (outerReady B r rows cols b c s lambda f) with
  | mk l v stk =>
    cases hright : emptyOuter (outerReady B r rows cols b c s lambda g) with
    | mk l' v' stk' =>
      simp only [hleft, hright] at hl hv hs ⊢
      cases hl; cases hv; cases hs; rfl

/-- All five slots populated by the charged protected-to-outer transfer have
the literal values expected by the prepared outer controller. -/
theorem outerReady_transfer_slots
    (B r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    (outerReady B r rows cols b c s lambda f).stk oSizeRows =
      List.replicate rows true ∧
    (outerReady B r rows cols b c s lambda f).stk oSizeCols =
      List.replicate cols true ∧
    (outerReady B r rows cols b c s lambda f).stk oWriterRows =
      List.replicate rows true ∧
    (outerReady B r rows cols b c s lambda f).stk oWriterCols =
      List.replicate cols true ∧
    (outerReady B r rows cols b c s lambda f).stk oWriterSource =
      MatrixMaterialization.rowMajor f := by
  have h₁ := outerReady_first_bank B r rows cols b c s lambda f
    (.inl (1 : Fin 11)) (by decide)
  have h₂ := outerReady_first_bank B r rows cols b c s lambda f
    (.inl (2 : Fin 11)) (by decide)
  have h₃ := outerReady_first_bank B r rows cols b c s lambda f
    (.inr (.inl (.inl (0 : Fin 20)))) (by decide)
  have h₄ := outerReady_first_bank B r rows cols b c s lambda f
    (.inr (.inl (.inl (7 : Fin 20)))) (by decide)
  have h₅ := outerReady_first_bank B r rows cols b c s lambda f
    (.inr (.inl (.inl (17 : Fin 20)))) (by decide)
  constructor
  · simpa only [oSizeRows, MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.cfg, MatrixTableInterlaceCombined.sizeBank,
      Function.update_apply] using h₁
  constructor
  · simpa only [oSizeCols, MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.cfg, MatrixTableInterlaceCombined.sizeBank,
      Function.update_apply] using h₂
  constructor
  · simpa only [oWriterRows, MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.cfg, MatrixTableInterlaceCombined.writerData,
      MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
      Function.update_apply] using h₃
  constructor
  · simpa only [oWriterCols, MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.cfg, MatrixTableInterlaceCombined.writerData,
      MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
      Function.update_apply] using h₄
  · simpa only [oWriterSource, MatrixTableInterlaceCombined.bridgeCfg,
      MatrixTableInterlaceCombined.cfg, MatrixTableInterlaceCombined.writerData,
      MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
      Function.update_apply] using h₅

/-- A bridge fed the actual writer's headers, source word, and empty buffer
reconstructs the entire prepared outer bank, not merely its five named
transfer slots. All other cells come from the supplied, table-independent
outer skeleton. -/
theorem bridge_matches_outer
    (B r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixWeightedOrderWriter.Config)
    (hr : cf.stk (.inr .rows) = List.replicate rows true)
    (hc : cf.stk (.inr .cols) = List.replicate cols true)
    (hw : cf.stk (.inr .output) = MatrixMaterialization.rowMajor f)
    (ht : cf.stk (.inr .buffer) = []) :
    (fun k : OStack =>
      bridgeAfter
        (writerFrame
          (emptyOuter (outerReady B r rows cols b c s lambda f)) cf).stk
        rows cols (.inr k)) =
      (outerReady B r rows cols b c s lambda f).stk := by
  let d := outerReady B r rows cols b c s lambda f
  let S := (writerFrame (emptyOuter d) cf).stk
  have hslots := outerReady_transfer_slots B r rows cols b c s lambda f
  rcases hslots with ⟨hd₁,hd₂,hd₃,hd₄,hd₅⟩
  have hs₁ : S wRows = List.replicate rows true := by
    change cf.stk (.inr .rows) = _
    exact hr
  have hs₂ : S wCols = List.replicate cols true := by
    change cf.stk (.inr .cols) = _
    exact hc
  have hs₃ : S wWord = MatrixMaterialization.rowMajor f := by
    change cf.stk (.inr .output) = _
    exact hw
  have hs₄ : S wTemp = [] := by
    change cf.stk (.inr .buffer) = []
    exact ht
  funext k
  by_cases h₁ : k = oSizeRows
  · subst k
    exact (bridgeAfter_sizeRows S rows cols
      (MatrixMaterialization.rowMajor f) hs₁
      (by change (emptyOuter d).stk oSizeRows = []
          exact emptyOuter_sizeRows d)).trans hd₁.symm
  by_cases h₂ : k = oSizeCols
  · subst k
    exact (bridgeAfter_sizeCols S rows cols
      (by change (emptyOuter d).stk oSizeCols = []
          exact emptyOuter_sizeCols d)).trans hd₂.symm
  by_cases h₃ : k = oWriterRows
  · subst k
    exact (bridgeAfter_writerRows S rows cols
      (by change (emptyOuter d).stk oWriterRows = []
          exact emptyOuter_writerRows d)).trans hd₃.symm
  by_cases h₄ : k = oWriterCols
  · subst k
    exact (bridgeAfter_writerCols S rows cols
      (by change (emptyOuter d).stk oWriterCols = []
          exact emptyOuter_writerCols d)).trans hd₄.symm
  by_cases h₅ : k = oWriterSource
  · subst k
    exact (bridgeAfter_source S rows cols
      (MatrixMaterialization.rowMajor f) hs₃ hs₄
      (by change (emptyOuter d).stk oWriterSource = []
          exact emptyOuter_writerSource d)).trans hd₅.symm
  exact bridge_outer_untouched d cf rows cols k h₁ h₂ h₃ h₄ h₅

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-- Charged physical handoff from the actual protected writer into the
complete outer prepared bank. The outer skeleton is supplied initially;
`emptyOuter_table_independent` proves it does not contain the protected table
or the future first-restoration table. -/
theorem full_writer_bridge_run
    (B r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (c0 cf : MatrixWeightedOrderWriter.Config) (N : ℕ)
    (hrun : ∃ t ≤ N, MatrixWeightedOrderWriter.run t c0 = cf)
    (hh : cf.l = none)
    (hr : cf.stk (.inr .rows) = List.replicate rows true)
    (hc : cf.stk (.inr .cols) = List.replicate cols true)
    (hw : cf.stk (.inr .output) = MatrixMaterialization.rowMajor f)
    (ht : cf.stk (.inr .buffer) = []) :
    let d := outerReady B r rows cols b c s lambda f
    ∃ t ≤ N + transferTime rows cols (MatrixMaterialization.rowMajor f),
      ∃ S : Stack → List Bool,
        run t (writerFrame (emptyOuter d) c0) =
          ⟨some outerStart,(cf.var,(d.var,none)),S⟩ ∧
        (fun k : OStack => S (.inr k)) = d.stk := by
  dsimp only
  let d := outerReady B r rows cols b c s lambda f
  let S := (writerFrame (emptyOuter d) cf).stk
  obtain ⟨tw,htw,hweighted⟩ := hrun
  obtain ⟨u,hu,hphase⟩ :=
    writer_phase (emptyOuter d) c0 cf tw hweighted hh
  have hSrows : S wRows = List.replicate rows true := by
    change cf.stk (.inr .rows) = _
    exact hr
  have hScols : S wCols = List.replicate cols true := by
    change cf.stk (.inr .cols) = _
    exact hc
  have hSword : S wWord = MatrixMaterialization.rowMajor f := by
    change cf.stk (.inr .output) = _
    exact hw
  have hStemp : S wTemp = [] := by
    change cf.stk (.inr .buffer) = []
    exact ht
  have hstart : writerFrame (emptyOuter d) cf =
      (⟨some (.inr (.inl .rows)),
        (cf.var,((emptyOuter d).var,none)),S⟩ : Config) := by
    cases cf with
    | mk l v stk =>
      cases l <;> simp_all [writerFrame, BitMachineComposition.liftCfg, S]
  have hbridge := bridge_run rows cols (MatrixMaterialization.rowMajor f)
    cf.var (emptyOuter d).var S hSrows hScols hSword hStemp
  have htotal := run_add hphase
    (transferTime rows cols (MatrixMaterialization.rowMajor f))
  rw [hstart] at htotal
  change run (u + transferTime rows cols (MatrixMaterialization.rowMajor f))
    (writerFrame (emptyOuter d) c0) =
    run ((rows+1)+(cols+1)+
      ((MatrixMaterialization.rowMajor f).length+1)+
      ((MatrixMaterialization.rowMajor f).length+1))
      ⟨some (.inr (.inl .rows)),
        (cf.var,((emptyOuter d).var,none)),S⟩ at htotal
  rw [hbridge] at htotal
  refine ⟨u + transferTime rows cols (MatrixMaterialization.rowMajor f),
    ?_,bridgeAfter S rows cols,?_,?_⟩
  · omega
  · simpa only [d,emptyOuter] using htotal
  · exact bridge_matches_outer B r rows cols b c s lambda f cf
      hr hc hw ht

/-- Existing outer execution lifted into the same protected-writer/bridge
program, with the writer banks held fixed. The outer phase has at most its
own exact transition bound; no fresh data preparation is performed here. -/
theorem outer_phase
    (cw : MatrixWeightedOrderWriter.Config)
    (d z : MatrixTableInterlaceOuterJoin.Config) (t : ℕ)
    (hrun : MatrixTableInterlaceOuterJoin.run t d = z)
    (hh : z.l = none) :
    ∃ u ≤ t, run u (outerFrame cw d) = outerFrame cw z := by
  letI : DecidableEq Stack :=
    @instDecidableEqSum WStack OStack inferInstance inferInstance
  have hhalt : (MatrixTableInterlaceOuterJoin.run t d).l = none := by
    rw [hrun]
    exact hh
  obtain ⟨u,hu,he⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (Equiv.sumComm OStack WStack) outerLabels outerControl
    MatrixTableInterlaceOuterJoin.program program none (fun _ => rfl)
    (cw.var,none) cw.stk d t hhalt
  change run u (outerFrame cw d) =
    outerFrame cw (MatrixTableInterlaceOuterJoin.run t d) at he
  rw [hrun] at he
  exact ⟨u,hu,he⟩

noncomputable def writerProjection
    (cf : MatrixWeightedOrderWriter.Config) (S : Stack → List Bool) :
    MatrixWeightedOrderWriter.Config :=
  ⟨none, cf.var, fun k => S (.inl k)⟩

/-- The charged transfer endpoint is literally the starting frame for the
next outer subroutine once its entire outer-bank projection is identified. -/
theorem bridge_end_outerFrame
    (B r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (cf : MatrixWeightedOrderWriter.Config) (S : Stack → List Bool)
    (hS : (fun k : OStack => S (.inr k)) =
      (outerReady B r rows cols b c s lambda f).stk) :
    (⟨some outerStart,
      (cf.var,((outerReady B r rows cols b c s lambda f).var,none)),
      S⟩ : Config) =
    outerFrame (writerProjection cf S)
      (outerReady B r rows cols b c s lambda f) := by
  simp only [outerFrame, writerProjection,
    BitMachineEncoding.renameCfg,
    BitMachineComposition.liftCfg]
  have hl : (outerReady B r rows cols b c s lambda f).l =
      some (.inl MatrixOuterWidthMachine.machine.start) := by
    simp only [outerReady, MatrixTableInterlaceOuterJoin.outerFrame,
      BitMachineComposition.liftCfg, MatrixOuterWidthMachine.startCfg,
      BitMachine.Machine.init]
  rw [hl, ←hS]
  simp [outerLabels, outerControl, outerStart]
  funext k
  cases k <;> rfl

/-- One uninterrupted run of the protected writer, charged word/header
transfer, outer-width controller, scalar restoration, and double interlace.
The initial scalar/foreign/inner skeleton is explicit and table-independent;
the protected word itself is generated by `c0` and transferred by the program. -/
theorem full_protected_outer_run
    (R r rows cols b c s lambda : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hq : MatrixOuterWidthMachine.width lambda = 2^r)
    (hB : MatrixRestorationWidthMachine.width b c s (2^r) = 2^R)
    (hfirst : 0 < rows * (cols ^ (2^r)))
    (hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows) ^ (2^R)))
    (c0 cf : MatrixWeightedOrderWriter.Config) (N : ℕ)
    (hrun : ∃ t ≤ N, MatrixWeightedOrderWriter.run t c0 = cf)
    (hh : cf.l = none)
    (hr : cf.stk (.inr .rows) = List.replicate rows true)
    (hc : cf.stk (.inr .cols) = List.replicate cols true)
    (hw : cf.stk (.inr .output) = MatrixMaterialization.rowMajor f)
    (ht : cf.stk (.inr .buffer) = []) :
    let d := outerReady (2^R) r rows cols b c s lambda f
    ∃ t ≤ N + transferTime rows cols (MatrixMaterialization.rowMajor f) +
        MatrixTableInterlaceOuterJoin.totalBound R r rows cols b c s lambda f,
      ∃ z : Config,
        run t (writerFrame (emptyOuter d) c0) = z ∧
        z.l = none ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          MatrixMaterialization.rowMajor
            (MatrixTableInterlaceDouble.secondResult R r rows cols f) := by
  dsimp only
  let d := outerReady (2^R) r rows cols b c s lambda f
  obtain ⟨t₁,ht₁,S,h₁,hS⟩ := full_writer_bridge_run
    (2^R) r rows cols b c s lambda f c0 cf N hrun hh hr hc hw ht
  let cw := writerProjection cf S
  have hjoin :
      (⟨some outerStart,(cf.var,(d.var,none)),S⟩ : Config) =
      outerFrame cw d :=
    bridge_end_outerFrame (2^R) r rows cols b c s lambda f cf S hS
  obtain ⟨t₂,ht₂,z,h₂,hz,hout⟩ :=
    MatrixTableInterlaceOuterJoin.outer_join_run R r rows cols
      b c s lambda f hq hB hfirst hsecond
  have h₂' : MatrixTableInterlaceOuterJoin.run t₂ d = z := by
    simpa only [d, outerReady] using h₂
  obtain ⟨u,hu,hlift⟩ := outer_phase cw d z t₂ h₂' hz
  have htotal := run_add h₁ u
  rw [hjoin, hlift] at htotal
  refine ⟨t₁+u, ?_, outerFrame cw z, htotal, ?_, ?_⟩
  · omega
  · simp [outerFrame, BitMachineEncoding.renameCfg,
      BitMachineComposition.liftCfg, hz]
  · change z.stk MatrixTableInterlaceOuterJoin.secondOutput = _
    exact hout

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedNumberedWriter

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

abbrev actualRows :=
  Fintype.card (Iteration.NRow G sourceConstant b y level M)
abbrev actualCols :=
  Fintype.card (Iteration.NCol G sourceConstant b y level M)
abbrev actualF :=
  physicalNumberedEntry G sourceConstant b y level M
abbrev actualP :=
  Iteration.stepParameters G sourceConstant b y level M

abbrev actualD :=
  let a := Iteration.a G sourceConstant b y level M
  let s := Iteration.s G sourceConstant b y level M
  let q := Iteration.q₂ G sourceConstant b y level M
  let L := Iteration.labels G sourceConstant b y level M
  let nv := GraphVectors.vertexCount VG s
  let nb := GraphVectors.auxiliaryCount s
  let hs : 0 < s := lt_of_lt_of_le (by decide : 0 < 4)
    (Iteration.bins_ge_four G sourceConstant b y level M)
  let order := GraphVectors.itemOrder G s
  MatrixWeightedEntrySemantic.actualInput M.entry a s q L nv nb hs
    (Iteration.secondFamily G sourceConstant b y level M) order
    (GraphVectors.vectors G s)
    (GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4)
        (Iteration.bins_ge_four G sourceConstant b y level M)))

abbrev actualWriterStart : MatrixWeightedOrderWriter.Config :=
  let s := Iteration.s G sourceConstant b y level M
  let d := actualD G sourceConstant b y level M
  MatrixWeightedOrderWriter.cfg
    (some (BitMachineRawSequence.leftLabel
      MatrixWeightedOrderPreparation.start))
    (MatrixWeightedOrderPreparation.initial,
      MatrixWeightedOrderWriter.writerInitial)
    (MatrixTableWriter.ready
      (MatrixWeightedOrderPreparation.sourceBank
        (MatrixWeightedEntryController.persistentBank d)
        (Fintype.card VG) (s-3) (4*s))
      (actualRows G sourceConstant b y level M)
      (actualCols G sourceConstant b y level M)
      0 0 0 0 [] []).contents

abbrev actualWriterBound :=
  let s := Iteration.s G sourceConstant b y level M
  let order := GraphVectors.itemOrder G s
  let d := actualD G sourceConstant b y level M
  MatrixWeightedOrderPreparation.prepCost (Fintype.card VG)
    (s-3) (4*s) +
    MatrixTableWriter.writerBound
      (actualRows G sourceConstant b y level M)
      (actualCols G sourceConstant b y level M)
      (MatrixWeightedEntryCost.commonCost d
        (actualRows G sourceConstant b y level M)
        (actualCols G sourceConstant b y level M) order) + 1

abbrev blankTable (rows cols : ℕ) :
    Fin rows → Fin cols → Bool := fun _ _ => false

noncomputable def actualPhysicalStart : Config :=
  let P := actualP G sourceConstant b y level M
  let R := Iteration.rQ G sourceConstant b y level M
  let r := Iteration.rq G sourceConstant b y level M
  let rows := actualRows G sourceConstant b y level M
  let cols := actualCols G sourceConstant b y level M
  writerFrame
    (emptyOuter (outerReady (2^R) r rows cols P.nextDepth
      P.sourceConstant (Parameters.bins P) (Parameters.scale P)
      (blankTable rows cols)))
    (actualWriterStart G sourceConstant b y level M)

def actualPhysicalBudget : ℕ :=
  let P := actualP G sourceConstant b y level M
  let R := Iteration.rQ G sourceConstant b y level M
  let r := Iteration.rq G sourceConstant b y level M
  let rows := actualRows G sourceConstant b y level M
  let cols := actualCols G sourceConstant b y level M
  let f := actualF G sourceConstant b y level M
  actualWriterBound G sourceConstant b y level M +
    transferTime rows cols (MatrixMaterialization.rowMajor f) +
    MatrixTableInterlaceOuterJoin.totalBound R r rows cols
      P.nextDepth P.sourceConstant (Parameters.bins P)
      (Parameters.scale P) f

noncomputable def actualPhysicalOutput : List Bool :=
  MatrixMaterialization.rowMajor
    (fun x z =>
      (Iteration.step G sourceConstant b y level M).entry
        (PostProtectedInterlaceScratch.physicalToStepRow
          G sourceConstant b y level M x)
        (PostProtectedInterlaceScratch.physicalToStepCol
          G sourceConstant b y level M z))

set_option maxHeartbeats 10000000


end
end EthInapproximability.CurrentPaper.ProtectedFullBankBridgeScratch
