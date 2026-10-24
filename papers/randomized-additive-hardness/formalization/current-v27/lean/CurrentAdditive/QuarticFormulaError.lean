import CurrentAdditive.QuarticSquareActual
import Paper2.A4T10Size

open _root_.CurrentAdditive.Eventual

/-!
# The literal v27 joint error at the encoded source formula

The two random sources are the current quartic selector tape and the selected
estimator tape. This theorem substitutes the source graph into the previously
proved square-word joint bound; the cited Dinur and BOT reductions remain
explicit parameters.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.T10Size
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem source_square_joint_at_large27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      2 ^ (2 ^ (Dsrc.sizeExponent + 1) * t45C Dsrc Bsrc cs) ≤ Φ.val.variables →
      let g := t10Graph Dsrc Bsrc Φ
      let edge := CanonicalEdgeTape.graphEdge g (t10Graph_valid Dsrc Bsrc Φ)
      let exp := experiment27 (t10_vertices_pos Dsrc Bsrc Φ) edge
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) (Paper2.Unit4Shell.Asymptotics.kOf Φ.val.variables)
      letI : Fintype exp.output.Tape := exp.tapeFintype
      let q := SquarePadding.side exp.output.rows exp.output.cols
      let s := (HeaderStrip.selectedClassifier E).cR *
        ((natField (2 * exp.output.budget + Paper2.Unit4Shell.Asymptotics.kOf Φ.val.variables)).length +
          2 * (natField q).length + q * q + 1) ^
            (HeaderStrip.selectedClassifier E).dR
      (EncodedCNF.Satisfiable Φ.val →
        99 / 100 ≤ (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
          (HeaderStrip.selectedClassifier E).output
            (natField (2 * exp.output.budget + Paper2.Unit4Shell.Asymptotics.kOf Φ.val.variables) ++
              AModel.matrixWord q q
                (MatrixMaterialization.rowMajor
                  (ASquare.squareTable exp.output x.1)))
            (List.ofFn x.2) = [true])) ∧
      (¬ EncodedCNF.Satisfiable Φ.val →
        (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
          (HeaderStrip.selectedClassifier E).output
            (natField (2 * exp.output.budget + Paper2.Unit4Shell.Asymptotics.kOf Φ.val.variables) ++
              AModel.matrixWord q q
                (MatrixMaterialization.rowMajor
                  (ASquare.squareTable exp.output x.1)))
            (List.ofFn x.2) = [true]) ≤
          (1 / 2 : ℝ) ^ 11 + 1 / 100) ∧
      (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3 := by
  obtain ⟨N₀, hN₀⟩ := actual_square_joint_at_large27 E c hc0 hc hE
    Bsrc.degreeBound (Dsrc.sizeExponent + 2) Bsrc.degreeBound_pos
    (sourceGap Dsrc Bsrc) (source_gap_pos Dsrc Bsrc)
  refine ⟨N₀, ?_⟩
  intro Φ hsparse hlarge hbig g edge exp q s
  obtain ⟨_, hNm, hinc, hdeg, hloop, hyes, hno⟩ :=
    t10_source Dsrc Bsrc Φ
  have hmn := (t45_relations Dsrc Bsrc Φ).2.1
  have hsize := t45_shell_form Dsrc Bsrc cs Φ hsparse hbig
  have hj := hN₀ Φ.val.variables hlarge (t10_vertices_pos Dsrc Bsrc Φ)
    edge hloop hinc hdeg hNm hmn hsize
  exact ⟨fun hsat => hj.1 (hyes hsat),
    fun hunsat => hj.2.1 (hno hunsat), hj.2.2⟩

#print axioms source_square_joint_at_large27

end Paper2.CurrentAdditive.QuarticClassEndpoint
