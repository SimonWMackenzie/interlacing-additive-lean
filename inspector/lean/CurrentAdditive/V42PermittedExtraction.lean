import CurrentAdditive.V42ActualLower
import CurrentAdditive.V39PermittedFloorDeterministic

namespace CurrentAdditive.V42PermittedExtraction
noncomputable section
open Paper2 V42Schedule V42ActualLower V39GeneratedConstruction
open EthInapproximability.CurrentPaper V39PermittedDeterministicExtraction
open V39PermittedNumericalExtraction V39FramedNumerical
open CurrentAdditive.Eventual (entries)
open CurrentAdditive.ModelEndpointReview.RationalEndpoint

structure Input where
  k : ℕ
  hk : 2 ≤ k
  n : ℕ
  m : ℕ
  rep : ℕ
  hn : 0<n
  hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep
  edge : Fin m→Bool→Fin n
  rounds : ℕ

def Input.matrix (x:Input) := run x.k x.hk x.hn x.hwidth x.edge x.rounds
def Input.word (x:Input) := x.matrix.squareWord
def Input.midpoint (x:Input) := 2*threshold x.k x.rounds+x.rounds

theorem midpoint_code_length (x:Input) :
    (rationalCode (x.midpoint:ℤ) 1).length ≤ 48*(entries x.word+1)^2 := by
  have hb:=(header_bounds x.k x.hk x.hn x.hwidth x.edge x.rounds).2.2
  have hm:x.midpoint ≤ 23*(entries x.word+1)^2 := by
    unfold Input.word
    rw [V39PermittedFloorDeterministic.actual_entries]
    change 2*threshold x.k x.rounds+x.rounds ≤ 23*(entryCount (run x.k x.hk x.hn x.hwidth x.edge x.rounds)+1)^2
    exact hb.trans (Nat.mul_le_mul_left 23 (Nat.pow_le_pow_left (Nat.le_add_right _ 1) 2))
  exact code_length_of_numerator_bound _ _ 23 2 hm

theorem extract_all (A:PermittedDeterministicEstimator) :
    ∃ E:Estimator,E.value=A.value ∧
      (∀ word,ValidTable word→E.output word=A.output word) ∧
      ∀ x:Input,ComparisonAt E x.word x.midpoint :=
  extract_family A Input.word Input.midpoint 48 2
    (fun x=>valid_of_target (StoredMatrix.squareWord_target _)) midpoint_code_length

def estimator (A:PermittedDeterministicEstimator) : Estimator := Classical.choose (extract_all A)
theorem estimator_value (A:PermittedDeterministicEstimator) : (estimator A).value=A.value :=
  (Classical.choose_spec (extract_all A)).1
theorem estimator_output (A:PermittedDeterministicEstimator) (word:List Bool) (hv:ValidTable word) :
    (estimator A).output word=A.output word :=
  (Classical.choose_spec (extract_all A)).2.1 word hv
theorem estimator_comparison (A:PermittedDeterministicEstimator) (x:Input) :
    ComparisonAt (estimator A) x.word x.midpoint :=
  (Classical.choose_spec (extract_all A)).2.2 x

#print axioms extract_all
end
end CurrentAdditive.V42PermittedExtraction



