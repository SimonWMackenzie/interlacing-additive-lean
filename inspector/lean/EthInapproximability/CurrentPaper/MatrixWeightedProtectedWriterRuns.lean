import EthInapproximability.CurrentPaper.MatrixWeightedPostProtectedInterlace
import EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriterIteration
import EthInapproximability.CurrentPaper.MatrixTableInterlaceDouble

/-!
Actual protected writer and subsequent double-restoration run, using the
frozen semantic conjugacy. This scratch module keeps the two executions
distinct until their bank configurations are proved composable.
-/

namespace EthInapproximability.CurrentPaper.PostProtectedWriterRunScratch

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedProtectedWriterIteration MatrixWeightedNumberedWriter
open MatrixWeightedOrdinalConjugacy PostProtectedInterlaceScratch

noncomputable section

set_option maxHeartbeats 1000000

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

private abbrev rows := Fintype.card (Iteration.NRow G sourceConstant b y level M)
private abbrev cols := Fintype.card (Iteration.NCol G sourceConstant b y level M)
private abbrev r := Iteration.rq G sourceConstant b y level M
private abbrev R := Iteration.rQ G sourceConstant b y level M
private abbrev f := physicalNumberedEntry G sourceConstant b y level M

/-- The actual protected writer's source word is exactly the initial source
word expected by the numerical double-interlace writer. This is a word
identity, not a bank-state handoff theorem. -/
theorem physical_source_word :
    permutedNumberedWord G sourceConstant b y level M =
      MatrixMaterialization.rowMajor (f G sourceConstant b y level M) := rfl

/-- Actual weighted-writer run with the literal supplied graph/source/scalar
banks; the final output bank has precisely the source word for the following
double interlace. No target ordinal permutation is computed in this run. -/
theorem actual_writer_source_run :
    let a := Iteration.a G sourceConstant b y level M
    let s := Iteration.s G sourceConstant b y level M
    let q := Iteration.q₂ G sourceConstant b y level M
    let L := Iteration.labels G sourceConstant b y level M
    let nv := GraphVectors.vertexCount VG s
    let nb := GraphVectors.auxiliaryCount s
    let hs : 0 < s := lt_of_lt_of_le (by decide : 0 < 4)
      (Iteration.bins_ge_four G sourceConstant b y level M)
    let order := GraphVectors.itemOrder G s
    let d := MatrixWeightedEntrySemantic.actualInput M.entry a s q L nv nb hs
      (Iteration.secondFamily G sourceConstant b y level M) order
      (GraphVectors.vectors G s)
      (GraphVectors.supportCap G
        (le_trans (by decide : 3 ≤ 4)
          (Iteration.bins_ge_four G sourceConstant b y level M)))
    let rows := rows G sourceConstant b y level M
    let cols := cols G sourceConstant b y level M
    let T := MatrixWeightedEntryCost.commonCost d rows cols order
    ∃ t ≤ MatrixWeightedOrderPreparation.prepCost (Fintype.card VG)
        (s - 3) (4 * s) + MatrixTableWriter.writerBound rows cols T + 1,
      ∃ w,
        MatrixWeightedOrderWriter.run t
          (MatrixWeightedOrderWriter.cfg
            (some (BitMachineRawSequence.leftLabel
              MatrixWeightedOrderPreparation.start))
            (MatrixWeightedOrderPreparation.initial,
              MatrixWeightedOrderWriter.writerInitial)
            (MatrixTableWriter.ready
              (MatrixWeightedOrderPreparation.sourceBank
                (MatrixWeightedEntryController.persistentBank d)
                (Fintype.card VG) (s - 3) (4 * s))
              rows cols 0 0 0 0 [] []).contents) =
          MatrixWeightedOrderWriter.cfg none
            (MatrixWeightedOrderPreparation.initial, w)
            (MatrixTableWriter.ready
              (MatrixWeightedEntryController.persistentBank d)
              rows cols 0 0 0 0 []
              (MatrixMaterialization.rowMajor
                (f G sourceConstant b y level M))).contents := by
  dsimp only
  simpa only [List.append_nil,
    physical_source_word G sourceConstant b y level M] using
    (MatrixWeightedProtectedWriterIteration.actual_protected_writer_run
      G sourceConstant b y level M [])

/-- The separately initialized, actual two-interlace writer run ends in the
row-major word of the next Iteration matrix under the explicit proof-side
ordinal relabellings. Its starting banks are `firstPrepared`; the preceding
theorem does not assert that the protected writer prepares these banks. -/
theorem actual_double_word_run :
    let rows := rows G sourceConstant b y level M
    let cols := cols G sourceConstant b y level M
    let r := r G sourceConstant b y level M
    let R := R G sourceConstant b y level M
    let f := f G sourceConstant b y level M
    ∃ t ≤ MatrixTableInterlaceDouble.totalBound (2^R) r rows cols f,
      ∃ c : MatrixTableInterlaceDouble.Config,
        MatrixTableInterlaceDouble.run t
          (MatrixTableInterlaceDouble.firstFrame
            (MatrixTableInterlaceDouble.secondPrepared
              (2^R) r rows cols f).var
            (MatrixTableInterlaceDouble.initialForeign (2^R))
            (MatrixTableInterlaceDouble.firstPrepared r rows cols f)) = c ∧
        c.l = none ∧
        c.stk MatrixTableInterlaceDouble.secondOutput =
          MatrixMaterialization.rowMajor
            (fun x z =>
              (Iteration.step G sourceConstant b y level M).entry
                (physicalToStepRow G sourceConstant b y level M x)
                (physicalToStepCol G sourceConstant b y level M z)) := by
  dsimp only
  have hrows : 0 < rows G sourceConstant b y level M := by
    unfold rows
    exact Fintype.card_pos
  have hcols : 0 < cols G sourceConstant b y level M := by
    unfold cols
    exact Fintype.card_pos
  have hfirst : 0 < rows G sourceConstant b y level M *
      ((cols G sourceConstant b y level M) ^
        (2 ^ r G sourceConstant b y level M)) := by positivity
  have hsecond : 0 < MatrixTableInterlaceDouble.firstColsCount
      (r G sourceConstant b y level M)
      (cols G sourceConstant b y level M) *
      ((MatrixTableInterlaceDouble.firstRowsCount
        (r G sourceConstant b y level M)
        (rows G sourceConstant b y level M)) ^
        (2 ^ R G sourceConstant b y level M)) := by
    unfold MatrixTableInterlaceDouble.firstColsCount
      MatrixTableInterlaceDouble.firstRowsCount
    positivity
  obtain ⟨t, ht, c, hc, hhalt, hout⟩ :=
    MatrixTableInterlaceDouble.double_restoration_run
      (R G sourceConstant b y level M)
      (r G sourceConstant b y level M)
      (rows G sourceConstant b y level M)
      (cols G sourceConstant b y level M)
      (f G sourceConstant b y level M) hfirst hsecond
  refine ⟨t, ht, c, hc, hhalt, ?_⟩
  rw [hout]
  apply congrArg MatrixMaterialization.rowMajor
  funext x z
  exact physical_secondResult_step_entry G sourceConstant b y level M x z


end
end EthInapproximability.CurrentPaper.PostProtectedWriterRunScratch
