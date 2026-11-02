import CurrentV43.TimeTradeoff.CommonConstants
import CurrentV43.MixedCaller.LargerBound
import CurrentV43.GeneralRandom.Endpoint

/-! Source-locked v43 Theorem 9.7 `thm:time-tradeoff`.
SHA256 bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6.
Exact theorem lines 3229--3256 (label 3230); proof lines 3258--3280
(label 3259). This module joins four proved algorithmic implications under
one common amplification and size constant. It assumes neither ETH nor
a SAT program/correctness/runtime certificate. -/
namespace CurrentV43.General
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction V39PermittedDeterministicExtraction
open ParametricSource TimeTradeoff
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Both construction bounds use this fixed amplification constant. It is
chosen by the fixed source/compiler before clause density or estimator. -/
def amplification (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) : Nat :=
  V42ETHPhysical.amplification D B

/-- The maximum permits the same displayed C for either construction.
Neither an estimator nor a gap program appears in its definition. -/
def sizeConstant (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) : Nat :=
  max (deterministicSourceConstant D B) (GeneralRandom.sourceConstant D)

 theorem amplification_ge (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) :
    2 ≤ amplification D B :=
  (by decide : 2 ≤ (2:Nat)^64).trans (V42GraphRuntime.amplification_ge (V42ActualSource.k0 D B))

 theorem sizeConstant_pos (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) :
    1 ≤ sizeConstant D B :=
  (deterministicSourceConstant_pos D B).trans (le_max_left _ _)

/-- The two literal size bounds from the source theorem, in original N. -/
def randomizedBound (C : Nat) (G : Schedule) (N : Nat) : Nat :=
  randomizedSize C N (G.gap N)

def deterministicBound (Amp C : Nat) (G : Schedule) (N : Nat) : Nat :=
  deterministicSize Amp C N (G.gap N)

/-- The user-supplied error margin holds eventually at the displayed S. -/
def GapCondition (a : Nat → Real) (bound : Nat → Nat) (G : Schedule) : Prop :=
  ∃ N₀ : Nat,∀ N,N₀ ≤ N → 2*a (bound N)<(G.gap N:Real)

/-- An actual fixed deterministic machine, exact on every sparse formula,
with its executed clock polynomial in S in the original variable count.
The Producer record also contains a run proof on every raw input word. -/
def DeterministicOutcome (cs : Nat) (bound : Nat → Nat) : Prop :=
  ∃ M : PhysicalConcat.Producer,
    (∀ Φ : ValidFormula,Φ.val.clauses.length ≤ cs*Φ.val.variables →
      M.result (EncodedCNF.encode Φ.val)=[decide (EncodedCNF.Satisfiable Φ.val)]) ∧
    ∃ c d N₀ : Nat,∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      M.clock (EncodedCNF.encode Φ.val) ≤ c*(bound Φ.val.variables)^d

/-- An actual fixed fair-bit algorithm. Its totalTime charges physical
carrier printing, every random bit, framing, construction and estimation. -/
def RandomizedOutcome (cs : Nat) (bound : Nat → Nat) : Prop :=
  ∃ F : FairBitAlgorithm.Algorithm,GeneralRandom.SparseCorrect F cs ∧
    ∃ c d N₀ : Nat,∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      F.totalTime (EncodedCNF.encode Φ.val) ≤ c*(bound Φ.val.variables)^d

/-- The four cases of source Theorem 9.7, with a common Amp and C.
Accuracy is required only on sufficiently large dyadic square tables.
Schedule supplies actual code with paid polynomial(N+k) computation;
no polynomial bound on k as a function of N is imposed. -/
structure FourCases (Amp C cs : Nat) : Prop where
  deterministicConstruction_deterministicEstimator :
    ∀ (G : Schedule) (E : PermittedDeterministicEstimator) (a : Nat → Real),
      Monotone a → ∀ T₀ : Nat,DeterministicSquareAccuracy E a T₀ →
      (∀ N,1 ≤ G.gap N) → GapCondition a (deterministicBound Amp C G) G →
      DeterministicOutcome cs (deterministicBound Amp C G)
  deterministicConstruction_randomizedEstimator :
    ∀ (G : Schedule) (E : PermittedEstimator) (a : Nat → Real),
      Monotone a → ∀ T₀ : Nat,RandomizedSquareAccuracy E a T₀ →
      (∀ N,1 ≤ G.gap N) → GapCondition a (deterministicBound Amp C G) G →
      RandomizedOutcome cs (deterministicBound Amp C G)
  randomizedConstruction_deterministicEstimator :
    ∀ (G : Schedule) (E : PermittedDeterministicEstimator) (a : Nat → Real),
      Monotone a → ∀ T₀ : Nat,DeterministicSquareAccuracy E a T₀ →
      (∀ N,1 ≤ G.gap N) → GapCondition a (randomizedBound C G) G →
      RandomizedOutcome cs (randomizedBound C G)
  randomizedConstruction_randomizedEstimator :
    ∀ (G : Schedule) (E : PermittedEstimator) (a : Nat → Real),
      Monotone a → ∀ T₀ : Nat,RandomizedSquareAccuracy E a T₀ →
      (∀ N,1 ≤ G.gap N) → GapCondition a (randomizedBound C G) G →
      RandomizedOutcome cs (randomizedBound C G)

/-- Every field is constructed from its checked physical endpoint. The
record is an output proof bundle, never an assumed conclusion certificate. -/
theorem four_cases (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) (cs : Nat) :
    FourCases (amplification D B) (sizeConstant D B) cs := by
  refine ⟨?_,?_,?_,?_⟩
  · intro G E a ha T₀ hE _hpos hgap
    exact deterministic_time_tradeoff_at D B (sizeConstant D B) (le_max_left _ _) cs G E a ha T₀ hE hgap
  · intro G E a ha T₀ hE _hpos hgap
    exact MixedCaller.mixed_algorithmic_implication_at D B (sizeConstant D B) (le_max_left _ _)
      G E a ha T₀ cs hE hgap
  · intro G E a ha T₀ hE hpos hgap
    exact GeneralRandom.deterministic_estimator_time_tradeoff D B (sizeConstant D B) (le_max_right _ _)
      E a ha T₀ hE G hpos hgap cs
  · intro G E a ha T₀ hE hpos hgap
    exact GeneralRandom.randomized_estimator_time_tradeoff D B (sizeConstant D B) (le_max_right _ _)
      E a ha T₀ hE G hpos hgap cs

/-- v43 Theorem 9.7: one fixed amplification and common construction size
constant precede every clause density, estimator and computable gap schedule.
The conclusion gives exact deterministic SAT only when both choices are
deterministic, and an actual bounded-error fair-bit SAT algorithm otherwise. -/
theorem time_tradeoff (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) :
    ∃ Amp C : Nat,2 ≤ Amp ∧ 1 ≤ C ∧ ∀ cs : Nat,FourCases Amp C cs :=
  ⟨amplification D B,sizeConstant D B,amplification_ge D B,sizeConstant_pos D B,four_cases D B⟩

#print axioms four_cases
#print axioms time_tradeoff
end
end CurrentV43.General
