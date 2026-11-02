import CurrentAdditive.V42GraphRuntime
import CurrentAdditive.V42FixedPromiseCutoff
import CurrentAdditive.V42DeterministicRequest
import CurrentAdditive.V39CurrentSourceJoin
import CurrentAdditive.EdgeScanValue

/-! The actual v42 deterministic table for the approved Dinur/BOT CNF
source. These definitions are shared by the fixed-gap and ETH consumers. -/
namespace CurrentAdditive.V42ActualSource
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V42Schedule V39GeneratedConstruction
open Workspace.Types.CommComplexity
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def k0 : ℕ := fixedPromiseCutoff (sourceGap D B) B.degreeBound
theorem k0_two : 2 ≤ k0 D B := by
  have h := (fixedPromiseCutoff_ge (sourceGap D B) B.degreeBound).1
  exact (by decide : 2 ≤ 200).trans h
theorem k0_degree : 2*B.degreeBound ≤ k0 D B :=
  (fixedPromiseCutoff_ge (sourceGap D B) B.degreeBound).2
def selected (Φ : ValidFormula) := V42RuntimePrefix.selected (k0 D B) (t10Graph D B Φ)
theorem selected_two (Φ : ValidFormula) : 2 ≤ selected D B Φ :=
  V42GraphRuntime.selected_ge_two _ (k0_two D B) _

def run (Φ : ValidFormula) (K : ℕ) : StoredMatrix :=
  V42GraphRuntime.publicRun B.degreeBound (k0 D B) (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (k0_two D B) (V39CurrentSourceJoin.source_geometry D B Φ).1
    (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B) K
def threshold (Φ : ValidFormula) (K : ℕ) : ℕ :=
  LookupSeed.exponent (4*selected D B Φ)+1+K*(40*selected D B Φ)
def word (Φ : ValidFormula) (K : ℕ) : List Bool := (run D B Φ K).squareWord
def request (Φ : ValidFormula) (K : ℕ) : List Bool :=
  natField (2*threshold D B Φ K+K)++word D B Φ K
def envelope (Φ : ValidFormula) (K : ℕ) : List Bool :=
  V42RuntimeWords.word (t10Graph D B Φ) (t10Graph_valid D B Φ) (selected D B Φ) K
    (selected_two D B Φ) (V39CurrentSourceJoin.source_geometry D B Φ).1
    (V42GraphRuntime.selected_width B.degreeBound (k0 D B) (t10Graph D B Φ)
      (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B)) K

theorem word_target (Φ : ValidFormula) (K : ℕ) :
    AModel.targetD (word D B Φ K)=some (Workspace.Types.CommComplexity.D (run D B Φ K).entry) :=
  StoredMatrix.squareWord_target _

theorem run_yes (Φ : ValidFormula) (K : ℕ) (hyes : EncodedCNF.Satisfiable Φ.val) :
    Workspace.Types.CommComplexity.D (run D B Φ K).entry ≤ threshold D B Φ K := by
  obtain ⟨colour,proper⟩ :=
    (DeterministicETHSourceBridge.fixed_graph_source D B Φ).2.2.2.2.2.1 hyes
  have h := V42GeneratedConstruction.graphRun_yes (selected D B Φ) (4*selected D B Φ)
    (selected_two D B Φ) (V39CurrentSourceJoin.source_geometry D B Φ).1
    (V42GraphRuntime.selected_width B.degreeBound (k0 D B) (t10Graph D B Φ)
      (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B))
    (LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    (4*selected D B Φ) K colour (by
      simpa only [LiteralEdgeScanValue.edge_eq_canonical] using proper)
  simpa only [V42GeneratedConstruction.generated_overhead] using h

theorem request_tail_outputs (Φ : ValidFormula) (K : ℕ) :
    V42DeterministicRequest.request.machine.OutputsWithin (envelope D B Φ K)
      (request D B Φ K)
      (V42DeterministicRequest.request.coefficient*((envelope D B Φ K).length+1)^
        V42DeterministicRequest.request.degree) := by
  have h := V42DeterministicRequest.outputs (4*selected D B Φ) K
    (V42RuntimeWords.context (t10Graph D B Φ) (t10Graph_valid D B Φ) (selected D B Φ)
      (selected_two D B Φ) (V39CurrentSourceJoin.source_geometry D B Φ).1
      (V42GraphRuntime.selected_width B.degreeBound (k0 D B) (t10Graph D B Φ)
        (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B))) (run D B Φ K)
  rw [V42DeterministicRequest.generated_threshold] at h
  exact h

#print axioms run_yes
#print axioms word_target
#print axioms request_tail_outputs
end
end CurrentAdditive.V42ActualSource
