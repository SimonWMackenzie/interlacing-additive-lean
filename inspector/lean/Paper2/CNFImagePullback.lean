import Paper2.ImagePullback
import Paper2.CNFGraphMachine

/-!
Specialization of image-qualified selected-tape pullback to Paper A's
all-input CNF-to-T10 graph compiler. The graph machine may be specified only
on the actual routed graph image; no arbitrary malformed-graph run or
probability statement is required. The *resulting CNF machine* is total on
every raw CNF word and every selected outer tape.
-/

noncomputable section

namespace Paper2.CNFImagePullback

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.CNFGraphGuard

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

abbrev GraphImageStage {N : ℕ} (hN : 1 ≤ N) :=
  ImagePullback.Stage (graphWord D B hN)

/-- Probability on the graph-stage tape, evaluated only at actual graph
words produced by the all-input CNF compiler. -/
noncomputable def imageProb {N : ℕ} (hN : 1 ≤ N)
    (A : GraphImageStage D B hN) (w : List Bool) (E : List Bool → Prop) : ℝ :=
  (Paper2.Unit4Shell.Definitions.uniformTape
    (A.tapeLength (graphWord D B hN w))).prob
      (fun tape => E (A.output (graphWord D B hN w) (List.ofFn tape)))

/-- Error hypothesis at the ACTUAL routed image only, including the fixed
NO/YES graph images chosen for malformed/small CNF inputs. This does not
require a graph-language algorithm or correctness on arbitrary graphs. -/
def SourceImageDecides {N : ℕ} (hN : 1 ≤ N)
    (A : GraphImageStage D B hN) : Prop :=
  ∀ w, (w ∈ EncodedCNF.Language →
      1 - (1 / 3 : ℝ) ≤ imageProb D B hN A w (· = [true])) ∧
    (w ∉ EncodedCNF.Language →
      imageProb D B hN A w (· = [true]) ≤ (1 / 3 : ℝ))

/-- Actual selected-tape CNF algorithm obtained by physical preprocessing,
length-dependent truncation, and a graph-stage machine that runs only on
preprocessor images. -/
noncomputable def cnfAlgorithm {N : ℕ} (hN : 1 ≤ N)
    (A : GraphImageStage D B hN) : SelectedTape.Algorithm :=
  ImagePullback.pullback (graphWord_polytime D B hN) A

theorem cnfAlgorithm_prob {N : ℕ} (hN : 1 ≤ N)
    (A : GraphImageStage D B hN) (w : List Bool) (E : List Bool → Prop) :
    (cnfAlgorithm D B hN A).prob w E = imageProb D B hN A w E :=
  ImagePullback.pullback_prob (graphWord_polytime D B hN) A w E

theorem cnfAlgorithm_decides {N : ℕ} (hN : 1 ≤ N)
    (A : GraphImageStage D B hN) (hA : SourceImageDecides D B hN A) :
    (cnfAlgorithm D B hN A).Decides EncodedCNF.Language (1 / 3) := by
  intro w
  rw [cnfAlgorithm_prob]
  exact hA w

theorem cnf_inBPP_of_image_stage {N : ℕ} (hN : 1 ≤ N)
    (A : GraphImageStage D B hN) (hA : SourceImageDecides D B hN A) :
    SelectedTape.InBPP EncodedCNF.Language :=
  ⟨cnfAlgorithm D B hN A, cnfAlgorithm_decides D B hN A hA⟩

#print axioms cnfAlgorithm
#print axioms cnfAlgorithm_prob
#print axioms cnfAlgorithm_decides
#print axioms cnf_inBPP_of_image_stage

end Paper2.CNFImagePullback
