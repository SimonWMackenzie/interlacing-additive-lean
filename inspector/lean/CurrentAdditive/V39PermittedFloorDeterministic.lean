import CurrentAdditive.V39PermittedDeterministicExtraction
import CurrentAdditive.V39FloorHeaderBound
import CurrentAdditive.V39SourceFloorJoin

/-! The same permitted raw comparator serves the actual deterministic
constructor with original-formula search floor. The request-size bound is
proved from the actual entry count; no cost or graph promise is assumed.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedFloorDeterministic

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

open Paper2
open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39PermittedNumericalExtraction
open CurrentAdditive.V39PermittedDeterministicExtraction
open CurrentAdditive.V39FramedNumerical
open CurrentAdditive.Eventual (entries)
open CurrentAdditive.ModelEndpointReview.RationalEndpoint

theorem actual_entries (R : StoredMatrix) :
    entries R.squareWord = (Paper2.SquarePadding.side R.rows R.cols)^2 := by
  unfold entries
  rw [R.squareWord_decodes]
  simp only [pow_two]

theorem midpoint_code_length (p : SourceConstants) (floor : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    (rationalCode ((2*publicGraphThresholdFrom p floor n m hn hlow hdegree k+k:ℕ):ℤ) 1).length ≤
      64*(entries (publicGraphRunFrom p floor hn hlow hdegree edge k).squareWord+1)^2 := by
  have hb := (publicGraphRunFrom_header_bounds p floor hn hlow hdegree edge k).2.2
  have hm : 2*publicGraphThresholdFrom p floor n m hn hlow hdegree k+k ≤
      31*(entries (publicGraphRunFrom p floor hn hlow hdegree edge k).squareWord+1)^2 := by
    rw [actual_entries]
    exact hb.trans (Nat.mul_le_mul_left 31 (Nat.pow_le_pow_left (by omega) 2))
  exact code_length_of_numerator_bound _ _ 31 2 hm

structure FloorGraphInput where
  constants : SourceConstants
  floor : ℕ
  vertices : ℕ
  edges : ℕ
  nonempty : 0 < vertices
  lower : vertices ≤ 2*edges
  degree : 2*edges ≤ constants.degree*vertices
  edge : Fin edges → Bool → Fin vertices
  rounds : ℕ

def FloorGraphInput.word (x : FloorGraphInput) : List Bool :=
  (publicGraphRunFrom x.constants x.floor x.nonempty x.lower x.degree x.edge x.rounds).squareWord

def FloorGraphInput.midpoint (x : FloorGraphInput) : ℕ :=
  2*publicGraphThresholdFrom x.constants x.floor x.vertices x.edges x.nonempty
    x.lower x.degree x.rounds+x.rounds

theorem extract_all_floor_constructors (A : PermittedDeterministicEstimator) :
    ∃ E : Estimator, E.value=A.value ∧
      (∀ word, ValidTable word → E.output word=A.output word) ∧
      ∀ x : FloorGraphInput, ComparisonAt E x.word x.midpoint := by
  exact V39PermittedDeterministicExtraction.extract_family A
    FloorGraphInput.word FloorGraphInput.midpoint 64 2
    (fun x => valid_of_target (StoredMatrix.squareWord_target _))
    (fun x => midpoint_code_length x.constants x.floor x.nonempty
      x.lower x.degree x.edge x.rounds)

open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite
open CurrentAdditive.V39CurrentSourceJoin

def sourceInput (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (k : ℕ) : FloorGraphInput where
  constants := parameters D B
  floor := Φ.val.variables
  vertices := (t10Graph D B Φ).vertices
  edges := (t10Graph D B Φ).edges.length
  nonempty := (source_geometry D B Φ).1
  lower := (source_geometry D B Φ).2.1
  degree := (source_geometry D B Φ).2.2
  edge := CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)
  rounds := k

/-- One pair of physical machines serves every actual approved source word
and every round count; its numerical output is the original estimator's. -/
theorem extract_approved_source (A : PermittedDeterministicEstimator)
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) :
    ∃ E : Estimator, E.value=A.value ∧
      (∀ word, ValidTable word → E.output word=A.output word) ∧
      ∀ Φ : ValidFormula, ∀ k,
        ComparisonAt E (ethWord D B Φ k) (2*ethThreshold D B Φ k+k) := by
  obtain ⟨E,hvalue,hout,hcompare⟩ := extract_all_floor_constructors A
  exact ⟨E,hvalue,hout,fun Φ k => hcompare (sourceInput D B Φ k)⟩

end CurrentAdditive.V39PermittedFloorDeterministic

#print axioms CurrentAdditive.V39PermittedFloorDeterministic.midpoint_code_length
#print axioms CurrentAdditive.V39PermittedFloorDeterministic.extract_all_floor_constructors
#print axioms CurrentAdditive.V39PermittedFloorDeterministic.extract_approved_source
