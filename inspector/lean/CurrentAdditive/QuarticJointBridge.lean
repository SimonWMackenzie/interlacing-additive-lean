import CurrentAdditive.QuarticFormulaDecision
import CurrentAdditive.QuarticSourceDeciderError
import CurrentAdditive.QuarticJointSampler

/-!
The exact fair-bit split turns a physical output identity into the v27
source/error interface.  No v12 selector or successful-tape search occurs.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.AEth2 Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.Definitions (uniformTape)
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)

theorem joint_of_physical_output27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (x : List Bool) (Φ : ValidFormula) (E : SelectedTape.Algorithm)
    (A : ETape.Algorithm) (r L : ℕ) :
    let g := t10Graph Dsrc Bsrc Φ
    let edge := CanonicalEdgeTape.graphEdge g (t10Graph_valid Dsrc Bsrc Φ)
    let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.val.variables
    let exp := experiment27 (t10_vertices_pos Dsrc Bsrc Φ) edge
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) k
    letI : Fintype exp.output.Tape := exp.tapeFintype
    let q := SquarePadding.side exp.output.rows exp.output.cols
    let s := (HeaderStrip.selectedClassifier E).cR *
      ((natField (2 * exp.output.budget + k)).length +
        2 * (natField q).length + q * q + 1) ^
          (HeaderStrip.selectedClassifier E).dR
    (∀ a : exp.output.Tape, (exp.output.tapeBits a).length = r) →
    r ≤ L →
    L + s ≤ A.tapeLen x.length →
    (∀ dec : List Bool → exp.output.Tape,
      (∀ a, dec (exp.output.tapeBits a) = a) →
      ∀ t : Fin (A.tapeLen x.length) → Bool,
      A.output x (List.ofFn t) =
        (HeaderStrip.selectedClassifier E).output
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord q q
              (MatrixMaterialization.rowMajor (ASquare.squareTable exp.output
                (dec ((List.ofFn t).take r)))))
          (((List.ofFn t).drop L).take s)) →
    JoinRealisesSqAt27 Dsrc Bsrc x Φ E A := by
  intro g edge k exp q s hlen0 hL hR houtput
  letI : Fintype exp.output.Tape := exp.tapeFintype
  obtain ⟨r₂, dec, hlen, hdec, hsplit⟩ :=
    experiment_joint_split27 (t10_vertices_pos Dsrc Bsrc Φ) edge
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) k
  obtain ⟨a₀⟩ := Paper2.FiniteLaw.nonempty exp.tapeLaw
  have hr : r₂ = r := (hlen a₀).symm.trans (hlen0 a₀)
  subst r₂
  let π : (Fin (A.tapeLen x.length) → Bool) →
      exp.output.Tape × (Fin s → Bool) := fun t =>
    (dec ((List.ofFn t).take r),
      Paper2.AEth5.vecOf (((List.ofFn t).drop L).take s) s)
  refine ⟨π, ?_, ?_⟩
  · intro P
    exact hsplit hL hR P
  · intro t
    have hout := houtput dec hdec t
    have hblock : (((List.ofFn t).drop L).take s).length = s := by
      rw [List.length_take, List.length_drop, List.length_ofFn]
      omega
    simpa only [π, Paper2.AEth5.ofFn_vecOf _ _ hblock] using hout

#print axioms joint_of_physical_output27

end Paper2.CurrentAdditive.QuarticClassEndpoint
