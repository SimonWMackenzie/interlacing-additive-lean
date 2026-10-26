import CurrentAdditive.DeterministicETHComparator
import CurrentAdditive.DeterministicEndpointAssembly
import CurrentAdditive.DeterministicEndpointClassifier
import EthInapproximability.CurrentPaper.ComplexityReductionClosure

/-! The finite fixed-error estimator consumer for the exact generated table.
The physical source-to-table writer and the actual successor remain explicit
inputs; there is no satisfiability test in the constructor. -/

namespace CurrentAdditive.DeterministicFixedDecision

open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicEndpointClassifier
open CurrentAdditive.DeterministicETHEncodedTable
open CurrentAdditive.DeterministicETHComparator
open Paper2.SquarePadding

universe u v

variable {Graph : Type u} {State : Type v}

/-- An all-table deterministic fixed additive estimator on the adopted
canonical matrix codec, with one fixed physical TM2 algorithm. -/
def AccurateFixed (est : List Bool → List Bool) (u : ℝ) : Prop :=
  BitMachine.Polytime est ∧
  ∀ w d, Paper2.AModel.targetD w = some d →
    ∃ z, Paper2.AModel.decodeDyadic (est w) = some z ∧
      |z-(d:ℝ)| ≤ u

/-- The public repetition count for every fixed integer error allowance. -/
theorem fixed_gap_choice (a : ℕ) :
    1 ≤ 2*a+1 ∧ 2*(a:ℝ) < ((2*a+1:ℕ):ℝ) := by
  constructor
  · omega
  · push_cast
    linarith

/-- A single fixed repetition count also handles an arbitrary fixed
nonnegative real additive error, by rounding its doubled value upward. -/
theorem fixed_real_gap_choice (u : ℝ) :
    let k := ⌈2*u⌉₊ + 1
    1 ≤ k ∧ 2*u < (k:ℝ) := by
  dsimp
  constructor
  · omega
  · have hc : 2*u ≤ (⌈2*u⌉₊ : ℝ) := Nat.le_ceil (2*u)
    have hs : (⌈2*u⌉₊ : ℝ) < ((⌈2*u⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self _
    exact lt_of_le_of_lt hc hs

/-- The actual square output, even with duplicate row/column labels, is
classified by the midpoint when the fixed error is below half the gap. -/
theorem fixed_encoded_midpoint
    (C : Construction Graph State) (G : Graph)
    (Yes No : Graph → Prop)
    (N A C₁ C₀ d₀ h k : ℕ)
    (hN : 2 ≤ N) (hA : 2 ≤ A) (hC₀ : 2*C₁+2 ≤ C₀)
    (V : ValidContract C G)
    (U : UniversalContract C G d₀ h)
    (Y : Yes G → YesContract C G d₀ h)
    (H : No G → NoContract C G d₀ h)
    (R : ResourceContract C G N A C₁)
    (P : TablePresentation C N)
    (est : List Bool → List Bool) (u : ℝ)
    (hest : AccurateFixed est u)
    (hgap : 2*u < (k:ℝ)) :
    let F := state C G k
    let M := paddedTable C N P F
    ∃ z : ℝ,
      Paper2.AModel.decodeDyadic (est (squareWord M)) = some z ∧
      (Yes G → z < (budget d₀ h k:ℝ)+(k:ℝ)/2) ∧
      (No G → (budget d₀ h k:ℝ)+(k:ℝ)/2 < z) ∧
      Paper2.CmpOwner.machine.OutputsWithin
        (EncodedComplexity.pair
          (midpointHeader (budget d₀ h k) k) (est (squareWord M)))
        [decide (z < (budget d₀ h k:ℝ)+(k:ℝ)/2)]
        (Paper2.CmpOwner.cmpTime
          (midpointHeader (budget d₀ h k) k).length
          (est (squareWord M)).length) := by
  let F := state C G k
  let M := paddedTable C N P F
  let S := side (P.rows F) (P.cols F)
  have hfinite := padded_conditional_one_exponent C G Yes No
    N A C₁ C₀ d₀ h k hN hA hC₀ V U Y H R P
  change D M ≤ budget d₀ h k + k ∧
    (Yes G → D M ≤ budget d₀ h k) ∧
    (No G → D M = budget d₀ h k + k ∧ C.profile G F) ∧
    N ≤ S ∧ (∃ e, S = 2^e) ∧
    S^2 ≤ N^(C₀*A^k) ∧
    totalStepTime C G k ≤ N^(C₀*A^k) at hfinite
  rcases hfinite with ⟨_, hy, hno, hside, _, _, _⟩
  have hS : 0 < S := by omega
  obtain ⟨z, hz, herr⟩ := hest.2 (squareWord M) (D M)
    (squareWord_targetD M hS)
  have hclass := midpoint_classifies (D M) (budget d₀ h k) k z u
    (Yes G) (No G) hy (fun hn => (hno hn).1) hgap herr
  exact ⟨z, hz, hclass.1, hclass.2,
    comparator_run (budget d₀ h k) k (est (squareWord M)) z hz⟩

#print axioms fixed_encoded_midpoint
#print axioms fixed_gap_choice
#print axioms fixed_real_gap_choice

/-- Closing the all-input encoded SAT domain: the generated-table classifier
is used on canonical valid formulas, while malformed words are rejected. -/
theorem inP_of_canonical_decider
    (decision : List Bool → Bool)
    (hpoly : BitMachine.Polytime (fun w => [decision w]))
    (hcanonical : ∀ f : EncodedCNF.Formula, f.Valid →
      (decision (EncodedCNF.encode f) = true ↔ EncodedCNF.Satisfiable f))
    (hmalformed : ∀ w, EncodedCNF.decode w = none → decision w = false) :
    ComplexityReductionClosure.InP EncodedCNF.Language := by
  refine ⟨decision, hpoly, ?_⟩
  intro w
  cases hdec : EncodedCNF.decode w with
  | none =>
      simp [EncodedCNF.malformed_not_mem hdec, hmalformed w hdec]
  | some f =>
      have hf : f.Valid := EncodedCNF.decode_valid hdec
      have hw : EncodedCNF.encode f = w := EncodedCNF.decode_sound hdec
      rw [← hw, EncodedCNF.encode_mem_iff f hf]
      exact (hcanonical f hf).symm

/-- The fixed-gap consequence at the adopted visible NP-hard source
interface, once the literal source/table/estimator machine has been composed. -/
theorem np_subset_p_of_canonical_decider
    (hard : EncodedComplexity.NPHard EncodedCNF.Language)
    (decision : List Bool → Bool)
    (hpoly : BitMachine.Polytime (fun w => [decision w]))
    (hcanonical : ∀ f : EncodedCNF.Formula, f.Valid →
      (decision (EncodedCNF.encode f) = true ↔ EncodedCNF.Satisfiable f))
    (hmalformed : ∀ w, EncodedCNF.decode w = none → decision w = false) :
    ∀ L, EncodedComplexity.InNP L →
      ComplexityReductionClosure.InP L :=
  ComplexityReductionClosure.npHard_inP_implies_np_subset_p
    hard (inP_of_canonical_decider decision hpoly hcanonical hmalformed)

#print axioms inP_of_canonical_decider
#print axioms np_subset_p_of_canonical_decider

end CurrentAdditive.DeterministicFixedDecision
