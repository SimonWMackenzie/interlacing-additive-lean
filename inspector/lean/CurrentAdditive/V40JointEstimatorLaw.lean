import CurrentAdditive.V39PhysicalProbabilityConsumer
import CurrentAdditive.V40RandomPermittedFamily

set_option autoImplicit false

/-! Construction randomness precedes a separate independent classifier tape.
The common second tape length follows from the literal fixed matrix dimensions
and payload length. No law of a desired final decision is a hypothesis. -/

namespace CurrentAdditive.V40JointEstimatorLaw
noncomputable section
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open EthInapproximability.CurrentPaper
open V39PublicSchedule V39ActualOutputMajority V40RandomPermittedFamily
open Workspace.Types.CommComplexity
open scoped BigOperators
set_option maxHeartbeats 2000000

abbrev Table (L k : ℕ) := Fin (sampleSide L k) → Fin (sampleSide L k) → Bool

def request (L k : ℕ) (f : Table L k) : List Bool :=
  EncodedCommunication.natField (numerator L k) ++ matrixWord L k f

def classifierLength (E : ActualEstimator) (L k : ℕ) : ℕ :=
  E.classifier.tapeLength (request L k (fun _ _ => false))

theorem request_length (L k : ℕ) (f h : Table L k) :
    (request L k f).length=(request L k h).length := by
  simp only [request,matrixWord,AModel.matrixWord,List.length_append,
    MatrixMaterialization.rowMajor_length]

theorem classifier_length (E : ActualEstimator) (L k : ℕ) (f : Table L k) :
    E.classifier.tapeLength (request L k f)=classifierLength E L k := by
  unfold classifierLength SelectedTape.Algorithm.tapeLength
  rw [request_length L k f (fun _ _ => false)]

def accepts (E : ActualEstimator) (L k : ℕ) (f : Table L k)
    (t : Fin (classifierLength E L k) → Bool) : Prop :=
  E.classifier.output (request L k f) (List.ofFn t)=[true]

theorem conditional_probability (E : ActualEstimator) (L k : ℕ) (f : Table L k) :
    (uniformTape (classifierLength E L k)).prob (accepts E L k f)=
      E.classifier.prob (request L k f) (·=[true]) := by
  unfold SelectedTape.Algorithm.prob
  rw [classifier_length]
  rfl

/-- The first factor is the whole construction law; the second is a new
independent tape for the fixed amplified classifier. -/
def independentLaw {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (E : ActualEstimator) (L k : ℕ) :=
  μ.prod (uniformTape (classifierLength E L k))

theorem yes_product {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (E : ActualEstimator) (L k : ℕ) (f : α → Table L k) (u : ℝ)
    (hu : 0≤u) (hgap : 2*u<(k:ℝ))
    (hcompare : ∀ a, E.actualComparison (matrixWord L k (f a)) (numerator L k))
    (haccurate : ∀ a, (2:ℝ)/3≤E.estimator.prob (matrixWord L k (f a))
      (fun out => |E.value out-(D (f a):ℝ)|≤u))
    (hcost : ∀ a, D (f a)≤B L k) :
    (99:ℝ)/100≤(independentLaw μ E L k).prob
      (fun z => accepts E L k (f z.1) z.2) := by
  unfold independentLaw
  rw [Paper2.FiniteLaw.prod_prob μ (uniformTape (classifierLength E L k))
    (fun a t => accepts E L k (f a) t)]
  calc
    (99:ℝ)/100 = ∑ a, μ.weight a*((99:ℝ)/100) := by
      rw [←Finset.sum_mul,μ.total,one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (μ.nonneg a)
      rw [conditional_probability]
      exact (E.fixed_midpoint_law _ (D (f a)) (B L k) k u hu hgap
        (hcompare a) (haccurate a)).1 (hcost a)

theorem no_product {α : Type*} [Fintype α] (μ : FiniteLaw α)
    (E : ActualEstimator) (L k : ℕ) (f : α → Table L k) (u : ℝ)
    (hu : 0≤u) (hgap : 2*u<(k:ℝ))
    (hcompare : ∀ a, E.actualComparison (matrixWord L k (f a)) (numerator L k))
    (haccurate : ∀ a, (2:ℝ)/3≤E.estimator.prob (matrixWord L k (f a))
      (fun out => |E.value out-(D (f a):ℝ)|≤u))
    (hgood : (49:ℝ)/50≤μ.prob (fun a => D (f a)=B L k+k)) :
    (independentLaw μ E L k).prob
      (fun z => accepts E L k (f z.1) z.2)≤(3:ℝ)/100 := by
  have hbad : μ.prob (fun a => ¬D (f a)=B L k+k)≤(1:ℝ)/50 := by
    rw [V39BudgetPrintedLaw.prob_not]
    linarith
  have h:=two_stage_failure_le μ (uniformTape (classifierLength E L k))
    (fun a => D (f a)=B L k+k) (fun a t => accepts E L k (f a) t)
    ((1:ℝ)/50) ((1:ℝ)/100) hbad (by
      intro a ha
      rw [conditional_probability]
      exact (E.fixed_midpoint_law _ (D (f a)) (B L k) k u hu hgap
        (hcompare a) (haccurate a)).2 (by omega)) (by positivity)
  exact h.trans (by norm_num)

#print axioms conditional_probability
#print axioms yes_product
#print axioms no_product
end
end CurrentAdditive.V40JointEstimatorLaw
