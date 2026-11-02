import EthInapproximability.CurrentPaper.MatrixWeightedFullBankBridge

/-!
Pinned literal-parameter specialization of the compiled generic physical
protected writer/outer-interlace run. The complete explicit specialization
is kernel checked using selective wrapper unfolding; no mathematical definition,
conclusion, runtime charge or input bank is changed. Frozen dependencies and
replay details are recorded in RECEIPT.md.
-/

namespace EthInapproximability.CurrentPaper.ProtectedFullBankBridgeScratch

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedNumberedWriter MatrixTableInterlaceProtectedBridge

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

attribute [local irreducible] GraphVectors.vertexCount GraphVectors.auxiliaryCount
attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering
attribute [local irreducible] Iteration.outputRowNumbering Iteration.outputColNumbering

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

/-- Target: one actual physical program run with an all-false prepared
skeleton, ending in the relabelled next-stage Iteration word. -/
theorem actual_physical_step_run :
    ∃ t ≤ actualPhysicalBudget G sourceConstant b y level M,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        MatrixTableInterlaceProtectedBridge.run t
          (actualPhysicalStart G sourceConstant b y level M) = z ∧
        z.l = none ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          actualPhysicalOutput G sourceConstant b y level M := by
  let P := actualP G sourceConstant b y level M
  let R := Iteration.rQ G sourceConstant b y level M
  let r := Iteration.rq G sourceConstant b y level M
  let rows := actualRows G sourceConstant b y level M
  let cols := actualCols G sourceConstant b y level M
  let f := actualF G sourceConstant b y level M
  let N := actualWriterBound G sourceConstant b y level M
  let c0 := actualWriterStart G sourceConstant b y level M
  obtain ⟨tw, htw, w, hw⟩ :=
    PostProtectedWriterRunScratch.actual_writer_source_run
      G sourceConstant b y level M
  let cf : MatrixWeightedOrderWriter.Config :=
    MatrixWeightedOrderWriter.cfg none
      (MatrixWeightedOrderPreparation.initial,w)
      (MatrixTableWriter.ready
        (MatrixWeightedEntryController.persistentBank
          (actualD G sourceConstant b y level M))
        rows cols 0 0 0 0 [] (MatrixMaterialization.rowMajor f)).contents
  have hrun : ∃ t ≤ N, MatrixWeightedOrderWriter.run t c0 = cf := by
    refine ⟨tw, ?_, ?_⟩
    · simpa only [N,actualWriterBound,rows,cols,actualRows,actualCols,
        actualD] using htw
    · simpa only [c0,actualWriterStart,cf,rows,cols,actualRows,actualCols,
        f,actualF,actualD] using hw
  have hh : cf.l = none := rfl
  have hr : cf.stk (.inr .rows) = List.replicate rows true := by
    simp only [cf, MatrixWeightedOrderWriter.cfg, MatrixTableWriter.Data.contents,
      Sum.elim_inr, MatrixTableWriter.Data.foreign, MatrixTableWriter.ready]
  have hc : cf.stk (.inr .cols) = List.replicate cols true := by
    simp only [cf, MatrixWeightedOrderWriter.cfg, MatrixTableWriter.Data.contents,
      Sum.elim_inr, MatrixTableWriter.Data.foreign, MatrixTableWriter.ready]
  have hword : cf.stk (.inr .output) =
      MatrixMaterialization.rowMajor f := by
    simp only [cf, MatrixWeightedOrderWriter.cfg, MatrixTableWriter.Data.contents,
      Sum.elim_inr, MatrixTableWriter.Data.foreign, MatrixTableWriter.ready]
  have htemp : cf.stk (.inr .buffer) = [] := by
    simp only [cf, MatrixWeightedOrderWriter.cfg, MatrixTableWriter.Data.contents,
      Sum.elim_inr, MatrixTableWriter.Data.foreign, MatrixTableWriter.ready]
  have hq : MatrixOuterWidthMachine.width (Parameters.scale P) = 2^r := by
    simpa only [Parameters.outerWidth] using
      (MatrixOuterWidthMachine.width_eq_parameters P)
  have hB : MatrixRestorationWidthMachine.width P.nextDepth
      P.sourceConstant (Parameters.bins P) (2^r) = 2^R := by
    simpa only [Parameters.outerWidth, Parameters.restorationWidth] using
      (MatrixRestorationWidthMachine.width_eq_parameters P)
  have hrows : 0 < rows := by
    dsimp only [rows,actualRows]
    exact Fintype.card_pos
  have hcols : 0 < cols := by
    dsimp only [cols,actualCols]
    exact Fintype.card_pos
  have hfirst : 0 < rows*(cols^(2^r)) := by positivity
  have hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount r cols *
      ((MatrixTableInterlaceDouble.firstRowsCount r rows)^(2^R)) := by
    unfold MatrixTableInterlaceDouble.firstColsCount
      MatrixTableInterlaceDouble.firstRowsCount
    positivity
  obtain ⟨t,ht,z,hz,hhz,hout⟩ := full_protected_outer_run
    R r rows cols P.nextDepth P.sourceConstant (Parameters.bins P)
    (Parameters.scale P) f hq hB hfirst hsecond
    c0 cf N hrun hh hr hc hword htemp
  have hblank := emptyOuter_table_independent
    (2^R) r rows cols P.nextDepth P.sourceConstant
    (Parameters.bins P) (Parameters.scale P)
    (blankTable rows cols) f
  refine ⟨t,ht,z,?_,hhz,?_⟩
  · dsimp only [actualPhysicalStart]
    rw [hblank]
    with_reducible exact hz
  · unfold actualPhysicalOutput
    rw [hout]
    apply congrArg MatrixMaterialization.rowMajor
    funext x z
    with_reducible
      exact PostProtectedInterlaceScratch.physical_secondResult_step_entry
        G sourceConstant b y level M x z


end
end EthInapproximability.CurrentPaper.ProtectedFullBankBridgeScratch
