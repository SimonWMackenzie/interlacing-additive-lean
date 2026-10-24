import EthInapproximability.CurrentPaper.MatrixWeightedNumberedWriter

/-! Literal actual weighted writer run with the protected output identified
as a row-major word of the permuted Iteration-numbered matrix. The input bank
remains an explicit supplied initial state. -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriterIteration

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab
open MatrixWeightedOrderWriter MatrixWeightedOrderPreparation
open MatrixWeightedEntryController
open MatrixWeightedOrdinalConjugacy MatrixWeightedNumberedWriter

noncomputable section

set_option maxHeartbeats 1000000
attribute [local irreducible] Iteration.nRowNumbering Iteration.nColNumbering
attribute [local irreducible] GraphVectors.vertexCount GraphVectors.auxiliaryCount

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]
variable (G : EndpointGraph VG EG) (sourceConstant b y level : ℕ)
  (M : Iteration.Matrix)

/-- The writer's radix guard follows from the actual source width and the
nonempty input column domain; it is not an extra promise or bank premise. -/
theorem actual_binBase_ge_two :
    2 ≤ MatrixStage4Digits.binBase
      (Iteration.a G sourceConstant b y level M)
      (Iteration.s G sourceConstant b y level M)
      (Iteration.q₂ G sourceConstant b y level M) M.columns := by
  let s := Iteration.s G sourceConstant b y level M
  have hs : 4 ≤ s := Iteration.bins_ge_four G sourceConstant b y level M
  have he : 1 ≤ Fintype.card EG := G.card_edge_pos
  have hprod : 4 ≤ s * Fintype.card EG := by
    have h := Nat.mul_le_mul hs he
    nlinarith
  have hq : 2 ≤ Iteration.q₂ G sourceConstant b y level M := by
    have h := card_le_q2 G s
    dsimp only [Iteration.q₂]
    nlinarith
  have hw : 1 ≤ MatrixStage4Digits.wordBase
      (Iteration.a G sourceConstant b y level M) s M.columns := by
    unfold MatrixStage4Digits.wordBase
    exact pow_pos M.columns_pos _
  change 2 ≤ Iteration.q₂ G sourceConstant b y level M *
    MatrixStage4Digits.wordBase
      (Iteration.a G sourceConstant b y level M) s M.columns
  exact le_trans (by norm_num : 2 ≤ 2 * 1) (Nat.mul_le_mul hq hw)

/-- Execute the existing canonical-order preparation and protected-table
writer on the actual Iteration stage inputs. The raw table, scalar words, and
three order-seed counts are still supplied in the exact initial bank. -/
theorem actual_protected_writer_run
    (output : List Bool) :
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
    let rows := Fintype.card (Iteration.NRow G sourceConstant b y level M)
    let cols := Fintype.card (Iteration.NCol G sourceConstant b y level M)
    let T := MatrixWeightedEntryCost.commonCost d rows cols order
    ∃ t ≤ prepCost (Fintype.card VG) (s - 3) (4 * s) +
        MatrixTableWriter.writerBound rows cols T + 1, ∃ w,
      run t (cfg (some (BitMachineRawSequence.leftLabel
          MatrixWeightedOrderPreparation.start))
        (MatrixWeightedOrderPreparation.initial, writerInitial)
        (MatrixTableWriter.ready
          (sourceBank (persistentBank d) (Fintype.card VG) (s - 3) (4 * s))
          rows cols 0 0 0 0 [] output).contents) =
      cfg none (MatrixWeightedOrderPreparation.initial, w)
        (MatrixTableWriter.ready (persistentBank d)
          rows cols 0 0 0 0 []
          (permutedNumberedWord G sourceConstant b y level M ++ output)).contents := by
  dsimp only
  have hbin := actual_binBase_ge_two G sourceConstant b y level M
  have h := graph_order_write_actual G
    (Iteration.s G sourceConstant b y level M) M.entry
    (Iteration.a G sourceConstant b y level M)
    (Iteration.s G sourceConstant b y level M)
    (Iteration.q₂ G sourceConstant b y level M)
    (Iteration.labels G sourceConstant b y level M)
    (lt_of_lt_of_le (by decide : 0 < 4)
      (Iteration.bins_ge_four G sourceConstant b y level M))
    (Iteration.secondFamily G sourceConstant b y level M)
    (GraphVectors.vectors G (Iteration.s G sourceConstant b y level M))
    (GraphVectors.supportCap G
      (le_trans (by decide : 3 ≤ 4)
        (Iteration.bins_ge_four G sourceConstant b y level M)))
    M.columns_pos hbin M.rows_pos output
  dsimp only at h
  rw [← physical_word_eq_permuted_numbered_word G sourceConstant b y level M]
  exact h


end
end EthInapproximability.CurrentPaper.MatrixWeightedProtectedWriterIteration

