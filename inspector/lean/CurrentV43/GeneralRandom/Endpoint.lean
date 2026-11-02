import CurrentV43.GeneralRandom.Clock

namespace CurrentV43.GeneralRandom
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff V39PermittedNumericalExtraction V39PermittedDeterministicExtraction
set_option autoImplicit false

/-- Bounded-error decision on every valid formula at the stated clause
density. A machine accepts exactly when its output word is `[true]`. -/
def SparseCorrect (F : FairBitAlgorithm.Algorithm) (cs : Nat) : Prop :=
  ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
    (EncodedCNF.Satisfiable Φ.val → (2:Real)/3 ≤ F.prob (EncodedCNF.encode Φ.val) (·=[true])) ∧
    (¬EncodedCNF.Satisfiable Φ.val → F.prob (EncodedCNF.encode Φ.val) (·=[true]) ≤ (1:Real)/3)

/-- The actual total charge is a fixed polynomial of the manuscript's
bound, eventually in the original variable count. -/
def PolynomialClock (F : FairBitAlgorithm.Algorithm) (C0 cs : Nat) (G : Schedule) : Prop :=
  ∃ c d N₁ : Nat, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
    N₁ ≤ Φ.val.variables → F.totalTime (EncodedCNF.encode Φ.val) ≤
      c*(randomizedSize C0 Φ.val.variables (G.gap Φ.val.variables))^d

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
include D B

/-- The randomized-construction branch of v43 Theorem 9.7, permitting
either a deterministic or a randomized numerical estimator. The source
constant precedes both the estimator and the physically implemented gap
schedule. No final SAT-correctness or clock certificate is an input. -/
theorem time_tradeoff_of_larger_constant (C0 : Nat) (hC0 : sourceConstant D ≤ C0)
    (A : NumericalEstimator) (a : Nat → Real) (ha : Monotone a)
    (T₀ : Nat) (hA : Accurate A a T₀) (G : Schedule) (hpos : ∀ N,1 ≤ G.gap N)
    (hgap : ∃ Ng : Nat,∀ N,Ng ≤ N →
      2*a (randomizedSize C0 N (G.gap N)) < (G.gap N:Real)) (cs : Nat) :
    ∃ F : FairBitAlgorithm.Algorithm, SparseCorrect F cs ∧ PolynomialClock F C0 cs G := by
  obtain ⟨cutoff,hcut,hsource,hcorrect⟩ := algorithm_correct D B C0 hC0 A a ha T₀ hA G hpos hgap cs
  refine ⟨algorithm D B (selected A).classifier G cs cutoff hcut hsource,hcorrect,?_⟩
  exact algorithm_clock D B C0 hC0 (selected A).classifier G cs cutoff hcut hsource

/-- Explicit deterministic-estimator specialization. The resulting SAT
algorithm uses only the construction's fair-bit randomness. -/
theorem deterministic_estimator_time_tradeoff (C0 : Nat) (hC0 : sourceConstant D ≤ C0)
    (A : PermittedDeterministicEstimator) (a : Nat → Real) (ha : Monotone a)
    (T₀ : Nat) (hA : DeterministicSquareAccuracy A a T₀) (G : Schedule) (hpos : ∀ N,1 ≤ G.gap N)
    (hgap : ∃ Ng : Nat,∀ N,Ng ≤ N →
      2*a (randomizedSize C0 N (G.gap N)) < (G.gap N:Real)) (cs : Nat) :
    ∃ F : FairBitAlgorithm.Algorithm, SparseCorrect F cs ∧ PolynomialClock F C0 cs G :=
  time_tradeoff_of_larger_constant D B C0 hC0 (.inl A) a ha T₀ hA G hpos hgap cs

theorem randomized_estimator_time_tradeoff (C0 : Nat) (hC0 : sourceConstant D ≤ C0)
    (A : PermittedEstimator) (a : Nat → Real) (ha : Monotone a)
    (T₀ : Nat) (hA : RandomizedSquareAccuracy A a T₀) (G : Schedule) (hpos : ∀ N,1 ≤ G.gap N)
    (hgap : ∃ Ng : Nat,∀ N,Ng ≤ N →
      2*a (randomizedSize C0 N (G.gap N)) < (G.gap N:Real)) (cs : Nat) :
    ∃ F : FairBitAlgorithm.Algorithm, SparseCorrect F cs ∧ PolynomialClock F C0 cs G :=
  time_tradeoff_of_larger_constant D B C0 hC0 (.inr A) a ha T₀ hA G hpos hgap cs

/-- The construction constant is selected before every estimator and
schedule. It can be enlarged to the common constant of both constructions
by the preceding theorem. -/
theorem randomized_construction_time_tradeoff :
    ∃ C0 : Nat, 1 ≤ C0 ∧ ∀ (A : NumericalEstimator) (a : Nat → Real), Monotone a →
      ∀ T₀ : Nat, Accurate A a T₀ → ∀ G : Schedule, (∀ N,1 ≤ G.gap N) →
      (∃ Ng : Nat,∀ N,Ng ≤ N →
        2*a (randomizedSize C0 N (G.gap N)) < (G.gap N:Real)) →
      ∀ cs : Nat, ∃ F : FairBitAlgorithm.Algorithm, SparseCorrect F cs ∧ PolynomialClock F C0 cs G := by
  refine ⟨sourceConstant D,sourceConstant_pos D,?_⟩
  intro A a ha T₀ hA G hpos hgap cs
  exact time_tradeoff_of_larger_constant D B (sourceConstant D) le_rfl A a ha T₀ hA G hpos hgap cs

#print axioms time_tradeoff_of_larger_constant
#print axioms deterministic_estimator_time_tradeoff
#print axioms randomized_estimator_time_tradeoff
#print axioms randomized_construction_time_tradeoff
end
end CurrentV43.GeneralRandom
