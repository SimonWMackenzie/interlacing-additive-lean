import CurrentAdditive.QuarticSquareMachine
import Paper2.E7SqJoin

/-!
# The v27 square law as a source decider error bound

`JoinRealisesSqAt27` states the precise tape pushforward and output identity
that a physical v27 composite decider must satisfy. It refers to the current
`experiment27`, not the preserved v12 experiment. No machine realization is
asserted here.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.T10Size
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.AEth2
open _root_.CurrentAdditive.Eventual
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)

def JoinRealisesSqAt27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (x : List Bool) (Φ : ValidFormula) (E : SelectedTape.Algorithm)
    (A : ETape.Algorithm) : Prop :=
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
  ∃ π : (Fin (A.tapeLen x.length) → Bool) → exp.output.Tape × (Fin s → Bool),
    (∀ P : exp.output.Tape × (Fin s → Bool) → Prop,
      (uniformTape (A.tapeLen x.length)).prob (fun t => P (π t)) =
        (exp.tapeLaw.prod (uniformTape s)).prob P) ∧
    ∀ t, A.output x (List.ofFn t) =
      (HeaderStrip.selectedClassifier E).output
        (natField (2 * exp.output.budget + k) ++
          AModel.matrixWord q q
            (MatrixMaterialization.rowMajor
              (ASquare.squareTable exp.output (π t).1)))
        (List.ofFn (π t).2)

theorem source_decider_error_at_large27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ)
    (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      2 ^ (2 ^ (Dsrc.sizeExponent + 1) * t45C Dsrc Bsrc cs) ≤ Φ.val.variables →
      ∀ (A : ETape.Algorithm) (x : List Bool),
      JoinRealisesSqAt27 Dsrc Bsrc x Φ E A →
      (EncodedCNF.Satisfiable Φ.val →
        1 - 1 / 3 ≤ A.prob x (· = [true])) ∧
      (¬ EncodedCNF.Satisfiable Φ.val →
        A.prob x (· = [true]) ≤ 1 / 3) := by
  obtain ⟨N₀, hN₀⟩ :=
    source_square_joint_at_large27 Dsrc Bsrc E c hc0 hc hE cs
  refine ⟨N₀, ?_⟩
  intro Φ hsparse hlarge hbig A x hJ
  obtain ⟨π, hpush, hout⟩ := hJ
  have hsource := hN₀ Φ hsparse hlarge hbig
  have hprob : A.prob x (· = [true]) =
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
      (exp.tapeLaw.prod (uniformTape s)).prob (fun y =>
        (HeaderStrip.selectedClassifier E).output
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord q q
              (MatrixMaterialization.rowMajor
                (ASquare.squareTable exp.output y.1)))
          (List.ofFn y.2) = [true]) := by
    unfold ETape.Algorithm.prob
    rw [← hpush]
    congr 1
    funext t
    exact congrArg (· = [true]) (hout t)
  rw [hprob]
  exact ⟨fun hsat => by linarith [hsource.1 hsat],
    fun hunsat => le_trans (hsource.2.1 hunsat) (le_of_lt hsource.2.2)⟩

#print axioms source_decider_error_at_large27

end Paper2.CurrentAdditive.QuarticClassEndpoint
