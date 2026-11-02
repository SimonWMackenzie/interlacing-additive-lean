import CurrentV43.GeneralRandom.Estimator
import CurrentV43.Parametric.Source

set_option autoImplicit false

namespace CurrentV43.GeneralRandom
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff V39PermittedNumericalExtraction
open scoped Classical
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

/-- This constant depends only on the fixed source theorem, and is chosen
before the estimator, approximation error, or paid gap schedule. -/
def sourceConstant (D : DinurReduction) : Nat :=
  (D.sizeExponent+4)*randomizedGraphExponent

theorem sourceConstant_pos (D : DinurReduction) : 1 ≤ sourceConstant D := by
  have h := randomizedGraphExponent_pos
  unfold sourceConstant
  nlinarith

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceCutoff (cs T₀ : Nat) : Nat :=
  1+V42SourceGeometry.originalCutoff D B cs+
    DeterministicETHSourceBridge.graphPolynomialCutoff D B cs+B.degreeBound*T₀+
    B.degreeBound*V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound

/-- Arbitrary positive schedule: every estimator-domain condition and
source promise is discharged above a finite original-variable cutoff. -/
theorem source_all_large (cs C0 : Nat) (hC0 : sourceConstant D ≤ C0)
    (A : NumericalEstimator) (a : Nat → Real) (ha : Monotone a)
    (T₀ : Nat) (hA : Accurate A a T₀) (G : Schedule)
    (hpos : ∀ N,1 ≤ G.gap N)
    (hgap : ∃ Ng : Nat,∀ N,Ng ≤ N →
      2*a (randomizedSize C0 N (G.gap N)) < (G.gap N:Real)) :
    ∃ N₀ : Nat, 1 ≤ N₀ ∧ V42SourceGeometry.originalCutoff D B cs ≤ N₀ ∧
      ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      ∀ ht : TimeTradeoff.SourceTests D B Φ,
      (EncodedCNF.Satisfiable Φ.val → (99:Real)/100 ≤
        (RandomizedRate.sourceLaw D B (G.gap Φ.val.variables) (selected A) Φ).prob
          (fun z => RandomizedRate.sourceAccepts D B (G.gap Φ.val.variables) Φ ht (selected A) z.1 z.2)) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (RandomizedRate.sourceLaw D B (G.gap Φ.val.variables) (selected A) Φ).prob
          (fun z => RandomizedRate.sourceAccepts D B (G.gap Φ.val.variables) Φ ht (selected A) z.1 z.2) ≤
            (3:Real)/100) := by
  obtain ⟨Ng,hgap⟩ := hgap
  refine ⟨max Ng (sourceCutoff D B cs T₀),?_,?_,?_⟩
  · unfold sourceCutoff; omega
  · unfold sourceCutoff; omega
  intro Φ hsp hN ht
  have hbase : sourceCutoff D B cs T₀ ≤ Φ.val.variables := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ Φ.val.variables := by unfold sourceCutoff at hbase; omega
  have hgraphcut : DeterministicETHSourceBridge.graphPolynomialCutoff D B cs ≤ Φ.val.variables := by
    unfold sourceCutoff at hbase; omega
  have hgraph := DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsp hgraphcut
  haveI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  have hr := (randomized_constructor_resources (t10Graph D B Φ) (t10Graph_valid D B Φ)
    Φ.val.variables (D.sizeExponent+3) (G.gap Φ.val.variables) hN1 hgraph
    (RandomizedRate.sourceCoefficient D B Φ) (RandomizedRate.sourceDeltaV D B Φ)
    (RandomizedRate.sourceZeta D B) ht).1
  have hS : V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices)
      (G.gap Φ.val.variables) ≤ randomizedSize C0 Φ.val.variables (G.gap Φ.val.variables) := by
    apply hr.trans
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_le_mul_right _ hC0
  have hT := randomized_source_entries_large D B Φ T₀ (G.gap Φ.val.variables) (hpos _)
    (show B.degreeBound*T₀ ≤ Φ.val.variables by unfold sourceCutoff at hbase; omega)
  have hlarge := (V39SourceGeometry.source_only D B Φ).vertices_floor
    (V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound)
    (show B.degreeBound*V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤ Φ.val.variables by
      unfold sourceCutoff at hbase; omega)
  exact source_correct D B A a ha T₀ (randomizedSize C0 Φ.val.variables (G.gap Φ.val.variables))
    (G.gap Φ.val.variables) hA Φ ht hlarge hT hS
      (hgap Φ.val.variables ((le_max_left _ _).trans hN))

#print axioms sourceConstant_pos
#print axioms source_all_large
end
end CurrentV43.GeneralRandom
