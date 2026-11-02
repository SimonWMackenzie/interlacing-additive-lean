import CurrentV43.TimeTradeoff.ErrorNonnegative
import CurrentV43.Randomized.Parameters
import CurrentAdditive.SmallBiasDetTapeAdapter

namespace CurrentV43.GeneralRandom
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction V39PermittedDeterministicExtraction
open V39ActualOutputMajority V39FramedNumerical
open scoped BigOperators Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

/-- A deterministic numerical estimator is used through its original
physical output and comparator. This changes no numerical guarantee. -/
def deterministicActual (E : Estimator) : ActualEstimator where
  estimator := SmallBias.selectedDetEstimator E.output E.physical
  value := E.value
  comparator := E.comparator

theorem deterministicActual_output (E : Estimator) (word tape : List Bool) :
    (deterministicActual E).classifier.output word tape=E.run word := by
  rfl

abbrev NumericalEstimator := PermittedDeterministicEstimator ⊕ PermittedEstimator

def selected : NumericalEstimator → ActualEstimator
  | .inl A => deterministicActual (TimeTradeoff.deterministicEstimator A)
  | .inr A => TimeTradeoff.randomEstimator A

def Accurate : NumericalEstimator → (Nat → Real) → Nat → Prop
  | .inl A,a,T₀ => TimeTradeoff.DeterministicSquareAccuracy A a T₀
  | .inr A,a,T₀ => TimeTradeoff.RandomizedSquareAccuracy A a T₀

theorem prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (P : α → Prop) :
    (μ.prod ν).prob (fun z => P z.1)=μ.prob P := by
  rw [FiniteLaw.prod_prob μ ν (fun x _ => P x)]
  have hi (x : α) : ν.prob (fun _ => P x) = if P x then 1 else 0 := by
    by_cases h : P x <;> simp [h]
  simp_rw [hi,mul_ite,mul_one,mul_zero]
  rfl

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The finite correctness statement is derived from the actual source
gap and the original estimator's accuracy, for either estimator model. -/
theorem source_correct (A : NumericalEstimator) (a : Nat → Real) (ha : Monotone a)
    (T₀ S K : Nat) (hA : Accurate A a T₀) (Φ : ValidFormula)
    (ht : TimeTradeoff.SourceTests D B Φ)
    (hlarge : V42FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤
      (t10Graph D B Φ).vertices)
    (hT : T₀ ≤ V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices) K)
    (hS : V42PublicSchedule.sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices) K ≤ S)
    (hgap : 2*a S < (K:Real)) :
    (EncodedCNF.Satisfiable Φ.val → (99:Real)/100 ≤
      (RandomizedRate.sourceLaw D B K (selected A) Φ).prob
        (fun z => RandomizedRate.sourceAccepts D B K Φ ht (selected A) z.1 z.2)) ∧
    (¬EncodedCNF.Satisfiable Φ.val →
      (RandomizedRate.sourceLaw D B K (selected A) Φ).prob
        (fun z => RandomizedRate.sourceAccepts D B K Φ ht (selected A) z.1 z.2) ≤ (3:Real)/100) := by
  cases A with
  | inr A =>
    have hu := TimeTradeoff.randomized_sample_error_nonnegative A a ha T₀ S _ K hA hT hS
    exact TimeTradeoff.randomized_source_correctness D B A a ha T₀ S K hA Φ ht hu hlarge hT hS hgap
  | inl A =>
    let E := TimeTradeoff.deterministicEstimator A
    let μ := V42PrintedCompression.bitLaw (t10Graph D B Φ) K
    let ν := Unit4Shell.Definitions.uniformTape (V42JointEstimatorLaw.classifierLength
      (deterministicActual E) (Nat.clog 2 (t10Graph D B Φ).vertices) K)
    let result := fun bits => E.run
      (V42JointEstimatorLaw.request (Nat.clog 2 (t10Graph D B Φ).vertices) K
        (TimeTradeoff.sampledSource D B Φ K ht bits))
    have hc := TimeTradeoff.deterministic_estimator_sampled_source_correctness
      D B A a ha T₀ S K hA Φ ht hlarge hT hS hgap
    have hp : (RandomizedRate.sourceLaw D B K (selected (.inl A)) Φ).prob
        (fun z => RandomizedRate.sourceAccepts D B K Φ ht (selected (.inl A)) z.1 z.2)=
        μ.prob (fun bits => result bits=[true]) := by
      change (μ.prod ν).prob (fun z =>
        (deterministicActual E).classifier.output _ (List.ofFn z.2)=[true])=_
      simp_rw [deterministicActual_output]
      simpa only [result,TimeTradeoff.sampledSource,V42RawRequestPacket.request,
        V42JointEstimatorLaw.request] using prod_fst μ ν (fun bits => result bits=[true])
    rw [hp]
    constructor
    · intro hy
      have hall : (fun bits => result bits=[true])=(fun _ => True) := by
        funext bits
        exact propext ⟨fun _=>trivial,fun _=>hc.1 hy bits⟩
      rw [hall,FiniteLaw.prob_true]
      norm_num
    · intro hn
      have hno : (49:Real)/50 ≤ μ.prob (fun bits => result bits=[false]) := hc.2 hn
      have hm := FiniteLaw.prob_mono μ (E:=fun bits=>result bits=[true])
        (F:=fun bits=>¬result bits=[false]) (by intro bits h h'; rw [h] at h'; cases h')
      rw [Unit4Shell.Amplification.prob_not] at hm
      linarith

#print axioms deterministicActual_output
#print axioms source_correct
end
end CurrentV43.GeneralRandom
