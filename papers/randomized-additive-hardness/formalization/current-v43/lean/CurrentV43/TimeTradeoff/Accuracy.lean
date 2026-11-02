import CurrentAdditive.V42JointEstimatorLaw
import CurrentAdditive.V42ActualSourceGap
import CurrentAdditive.V42ActualSourceEstimator
import CurrentAdditive.V42RandomizedSourceData
import CurrentAdditive.V42ETHPhysical
import CurrentV43.TimeTradeoff.Numerics

/-! The estimator/comparison part of v43 `thm:time-tradeoff`, main.tex
3238--3287, SHA256 bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6.
The error function is arbitrary and monotone. All estimator correctness is
restricted to sufficiently large square tables of dyadic side length.
No ETH assumption occurs. Construction gaps remain the proved same-table
v42 gaps; this file does not take the desired SAT decision as a certificate. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction V39PermittedDeterministicExtraction
open V39ActualOutputMajority V39FramedNumerical V39GeneratedConstruction
open Workspace.Types.CommComplexity
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-- Ordinary randomized estimation, needed only on dyadic square tables. -/
def RandomizedSquareAccuracy (A : PermittedEstimator) (a : ℕ → ℝ) (T₀ : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0  <  m → (∃ e, m = 2^e) → T₀ ≤ m^2 →
    (2:ℝ)/3  ≤  A.raw.prob (AModel.matrixWord m m (MatrixMaterialization.rowMajor f))
      (fun out => |A.value out-(D f:ℝ)| ≤ a (m^2))

/-- Ordinary deterministic estimation on the same restricted table domain. -/
def DeterministicSquareAccuracy (A : PermittedDeterministicEstimator)
    (a : ℕ → ℝ) (T₀ : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0  <  m → (∃ e, m = 2^e) → T₀ ≤ m^2 →
    |A.value (A.output (AModel.matrixWord m m (MatrixMaterialization.rowMajor f)))-
      (D f:ℝ)| ≤ a (m^2)

/-- Accuracy at actual size T implies accuracy at a larger declared bound S. -/
theorem deterministic_error_mono (A : PermittedDeterministicEstimator)
    (a : ℕ → ℝ) (ha : Monotone a) (T₀ m S : ℕ)
    (hA : DeterministicSquareAccuracy A a T₀) (f : Fin m → Fin m → Bool)
    (hm : 0  <  m) (hp : ∃ e, m = 2^e) (hT : T₀ ≤ m^2) (hS : m^2 ≤ S) :
    |A.value (A.output (AModel.matrixWord m m (MatrixMaterialization.rowMajor f)))-
      (D f:ℝ)| ≤ a S :=
  (hA m f hm hp hT).trans (ha hS)

theorem randomized_error_mono (A : PermittedEstimator)
    (a : ℕ → ℝ) (ha : Monotone a) (T₀ m S : ℕ)
    (hA : RandomizedSquareAccuracy A a T₀) (f : Fin m → Fin m → Bool)
    (hm : 0  <  m) (hp : ∃ e, m = 2^e) (hT : T₀ ≤ m^2) (hS : m^2 ≤ S) :
    (2:ℝ)/3  ≤  A.raw.prob (AModel.matrixWord m m (MatrixMaterialization.rowMajor f))
      (fun out => |A.value out-(D f:ℝ)| ≤ a S) := by
  apply (hA m f hm hp hT).trans
  apply FiniteLaw.prob_mono
  intro t ht
  exact ht.trans (ha hS)

/-- One common estimator is extracted before either construction, the graph,
the round count, the actual sampled table or either random tape. -/
abbrev Request := Sum V42RandomPermittedFamily.Sample V42PermittedExtraction.Input

def requestWord : Request → List Bool
  | .inl x => V42RandomPermittedFamily.matrixWord x.L x.k x.table
  | .inr x => x.word

def requestNumerator : Request → ℕ
  | .inl x => V42RandomPermittedFamily.numerator x.L x.k
  | .inr x => x.midpoint

theorem request_valid (x : Request) : ValidTable (requestWord x) := by
  cases x with
  | inl x => exact V42RandomPermittedFamily.valid_table x.L x.k x.table
  | inr x => exact valid_of_target (StoredMatrix.squareWord_target _)

theorem request_midpoint (x : Request) :
    (ModelEndpointReview.RationalEndpoint.rationalCode (requestNumerator x:ℤ) 1).length  ≤ 
      48*(Eventual.entries (requestWord x)+1)^2 := by
  cases x with
  | inl x =>
    have h:=V42RandomPermittedFamily.midpoint_code_bound x.L x.k x.table
    apply h.trans
    simp only [pow_one]
    have ht : 1  ≤  Eventual.entries (V42RandomPermittedFamily.matrixWord x.L x.k x.table)+1 := by omega
    change 6*(Eventual.entries (V42RandomPermittedFamily.matrixWord x.L x.k x.table)+1)  ≤  _
    dsimp only [requestWord]
    nlinarith
  | inr x => exact V42PermittedExtraction.midpoint_code_length x

def randomEstimator (A : PermittedEstimator) : ActualEstimator :=
  Classical.choose (V39PermittedNumericalExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)

theorem randomEstimator_value (A : PermittedEstimator) :
    (randomEstimator A).value=A.value :=
  (Classical.choose_spec (V39PermittedNumericalExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)).2.1

theorem randomEstimator_comparison (A : PermittedEstimator) (x : Request) :
    (randomEstimator A).actualComparison (requestWord x) (requestNumerator x) :=
  (Classical.choose_spec (V39PermittedNumericalExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)).2.2.1 x

theorem randomEstimator_law (A : PermittedEstimator) (word : List Bool)
    (hv : ValidTable word) (P : List Bool → Prop) :
    (randomEstimator A).estimator.prob word P=A.raw.prob word P :=
  (Classical.choose_spec (V39PermittedNumericalExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)).2.2.2 word hv P

def deterministicEstimator (A : PermittedDeterministicEstimator) : Estimator :=
  Classical.choose (V39PermittedDeterministicExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)

theorem deterministicEstimator_value (A : PermittedDeterministicEstimator) :
    (deterministicEstimator A).value=A.value :=
  (Classical.choose_spec (V39PermittedDeterministicExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)).1

theorem deterministicEstimator_output (A : PermittedDeterministicEstimator)
    (word : List Bool) (hv : ValidTable word) :
    (deterministicEstimator A).output word=A.output word :=
  (Classical.choose_spec (V39PermittedDeterministicExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)).2.1 word hv

theorem deterministicEstimator_comparison (A : PermittedDeterministicEstimator) (x : Request) :
    ComparisonAt (deterministicEstimator A) (requestWord x) (requestNumerator x) :=
  (Classical.choose_spec (V39PermittedDeterministicExtraction.extract_family A
    requestWord requestNumerator 48 2 request_valid request_midpoint)).2.2 x

/-- Exact classifier output for an arbitrary deterministic-construction gap. -/
theorem deterministic_source_classification
    (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))
    (A : PermittedDeterministicEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S K : ℕ) (hA : DeterministicSquareAccuracy A a T₀)
    (Φ : ValidFormula)
    (hT : T₀ ≤ V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ K))
    (hS : V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ K) ≤ S)
    (hgap : 2*a S < (K:ℝ)) :
    (deterministicEstimator A).run (V42ActualSource.request Src Bsrc Φ K)=
      [decide (EncodedCNF.Satisfiable Φ.val)] := by
  let R:=V42ActualSource.run Src Bsrc Φ K
  have hv:ValidTable R.squareWord:=valid_of_target (StoredMatrix.squareWord_target R)
  have hacc:|(deterministicEstimator A).value ((deterministicEstimator A).output R.squareWord)-
      (D R.entry:ℝ)| ≤ a S := by
    rw [deterministicEstimator_value,deterministicEstimator_output A _ hv]
    simpa only [StoredMatrix.square_cost] using deterministic_error_mono A a ha T₀
      (SquarePadding.side R.rows R.cols) S hA R.square (SquarePadding.side_pos _ _)
      R.square_side_power hT hS
  have hm:=V39FramedNumerical.midpoint_outputs (deterministicEstimator A) R.squareWord
    (D R.entry) (V42ActualSource.threshold Src Bsrc Φ K) K (a S) hgap hacc
    (deterministicEstimator_comparison A (.inr (V42ActualSource.sourceInput Src Bsrc Φ K)))
  by_cases hs:EncodedCNF.Satisfiable Φ.val
  · simpa only [V42ActualSource.request,hs,decide_true] using
      hm.1 (V42ActualSource.run_yes Src Bsrc Φ K hs)
  · simpa only [V42ActualSource.request,hs,decide_false] using
      hm.2 (V42ActualSource.run_no Src Bsrc Φ K hs).ge

/-- A randomized estimator on the deterministic table has amplified error
below 1/100. No construction randomness is added. -/
theorem randomized_estimator_deterministic_source
    (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))
    (A : PermittedEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S K : ℕ) (hA : RandomizedSquareAccuracy A a T₀)
    (Φ : ValidFormula) (hu : 0 ≤ a S)
    (hT : T₀ ≤ V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ K))
    (hS : V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ K) ≤ S)
    (hgap : 2*a S < (K:ℝ)) :
    (EncodedCNF.Satisfiable Φ.val → (99:ℝ)/100 < 
      (randomEstimator A).classifier.prob (V42ActualSource.request Src Bsrc Φ K) (·=[true])) ∧
    (¬EncodedCNF.Satisfiable Φ.val →
      (randomEstimator A).classifier.prob (V42ActualSource.request Src Bsrc Φ K) (·=[true]) < (1:ℝ)/100) := by
  let R:=V42ActualSource.run Src Bsrc Φ K
  have hv:ValidTable R.squareWord:=valid_of_target (StoredMatrix.squareWord_target R)
  have hacc:(2:ℝ)/3 ≤ (randomEstimator A).estimator.prob R.squareWord
      (fun out=>|(randomEstimator A).value out-(D R.entry:ℝ)| ≤ a S) := by
    rw [randomEstimator_value,randomEstimator_law A _ hv]
    simpa only [StoredMatrix.square_cost] using randomized_error_mono A a ha T₀
      (SquarePadding.side R.rows R.cols) S hA R.square (SquarePadding.side_pos _ _)
      R.square_side_power hT hS
  have hm:=(randomEstimator A).fixed_midpoint_strict_law R.squareWord (D R.entry)
    (V42ActualSource.threshold Src Bsrc Φ K) K (a S) hu hgap
    (randomEstimator_comparison A (.inr (V42ActualSource.sourceInput Src Bsrc Φ K))) hacc
  exact ⟨fun hs=>hm.1 (V42ActualSource.run_yes Src Bsrc Φ K hs),
    fun hs=>hm.2 (V42ActualSource.run_no Src Bsrc Φ K hs).ge⟩

/-- Both sources of randomness are independent and the total NO error is
at most 3/100, with the actual construction failure charged as 1/50. -/
theorem randomized_estimator_randomized_construction
    (A : PermittedEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S L K : ℕ) (hA : RandomizedSquareAccuracy A a T₀)
    (hu : 0 ≤ a S) (hT : T₀ ≤ (V42PublicSchedule.sampleSide L K)^2)
    (hS : (V42PublicSchedule.sampleSide L K)^2 ≤ S) (hgap : 2*a S < (K:ℝ))
    {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (f : α → V42JointEstimatorLaw.Table L K) :
    ((∀ x,D (f x) ≤ V42PublicSchedule.B L K) → (99:ℝ)/100 ≤ 
      (V42JointEstimatorLaw.independentLaw μ (randomEstimator A) L K).prob
        (fun z=>V42JointEstimatorLaw.accepts (randomEstimator A) L K (f z.1) z.2)) ∧
    ((49:ℝ)/50 ≤ μ.prob (fun x=>D (f x)=V42PublicSchedule.B L K+K) →
      (V42JointEstimatorLaw.independentLaw μ (randomEstimator A) L K).prob
        (fun z=>V42JointEstimatorLaw.accepts (randomEstimator A) L K (f z.1) z.2) ≤ (3:ℝ)/100) := by
  have hc (x:α):=(randomEstimator_comparison A (.inl ⟨L,K,f x⟩))
  have hacc (x:α):(2:ℝ)/3 ≤ (randomEstimator A).estimator.prob
      (V42RandomPermittedFamily.matrixWord L K (f x))
      (fun out=>|(randomEstimator A).value out-(D (f x):ℝ)| ≤ a S) := by
    rw [randomEstimator_value,randomEstimator_law A _ (V42RandomPermittedFamily.valid_table L K (f x))]
    exact randomized_error_mono A a ha T₀ _ S hA (f x)
      (V42RandomPermittedFamily.side_pos L K) ⟨_,rfl⟩ hT hS
  exact ⟨fun hy=>V42JointEstimatorLaw.yes_product μ (randomEstimator A) L K f (a S)
      hu hgap hc hacc hy,
    fun hn=>V42JointEstimatorLaw.no_product μ (randomEstimator A) L K f (a S)
      hu hgap hc hacc hn⟩

/-- A deterministic estimator preserves the construction's one-sided YES
correctness and incurs only the construction's 1/50 NO failure. -/
theorem deterministic_estimator_randomized_construction
    (A : PermittedDeterministicEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S L K : ℕ) (hA : DeterministicSquareAccuracy A a T₀)
    (hT : T₀ ≤ (V42PublicSchedule.sampleSide L K)^2)
    (hS : (V42PublicSchedule.sampleSide L K)^2 ≤ S) (hgap : 2*a S < (K:ℝ))
    {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (f : α → V42JointEstimatorLaw.Table L K) :
    ((∀ x,D (f x) ≤ V42PublicSchedule.B L K) →
      ∀ x,(deterministicEstimator A).run (V42JointEstimatorLaw.request L K (f x))=[true]) ∧
    ((49:ℝ)/50 ≤ μ.prob (fun x=>D (f x)=V42PublicSchedule.B L K+K) →
      (49:ℝ)/50 ≤ μ.prob (fun x=>(deterministicEstimator A).run
        (V42JointEstimatorLaw.request L K (f x))=[false])) := by
  have hm (x:α):
      (D (f x) ≤ V42PublicSchedule.B L K → (deterministicEstimator A).run
        (V42JointEstimatorLaw.request L K (f x))=[true]) ∧
      (V42PublicSchedule.B L K+K ≤ D (f x) → (deterministicEstimator A).run
        (V42JointEstimatorLaw.request L K (f x))=[false]) := by
    have hv:=V42RandomPermittedFamily.valid_table L K (f x)
    have hacc:|(deterministicEstimator A).value
        ((deterministicEstimator A).output (V42RandomPermittedFamily.matrixWord L K (f x)))-
        (D (f x):ℝ)| ≤ a S := by
      rw [deterministicEstimator_value,deterministicEstimator_output A _ hv]
      exact deterministic_error_mono A a ha T₀ _ S hA (f x)
        (V42RandomPermittedFamily.side_pos L K) ⟨_,rfl⟩ hT hS
    exact V39FramedNumerical.midpoint_outputs (deterministicEstimator A)
      (V42RandomPermittedFamily.matrixWord L K (f x)) (D (f x))
      (V42PublicSchedule.B L K) K (a S) hgap hacc
      (deterministicEstimator_comparison A (.inl ⟨L,K,f x⟩))
  refine ⟨fun hy x=>(hm x).1 (hy x),fun hn=>hn.trans ?_⟩
  exact FiniteLaw.prob_mono μ (fun x hx=>(hm x).2 hx.ge)

#print axioms deterministic_source_classification
#print axioms randomized_estimator_deterministic_source
#print axioms randomized_estimator_randomized_construction
#print axioms deterministic_estimator_randomized_construction
end
end CurrentV43.TimeTradeoff


