import CurrentAdditive.V39FramedNumerical
import CurrentAdditive.DeterministicETHEstimator
import CurrentAdditive.DeterministicEndpointETH

/-!
Selected v39 `models.tex`, `def:table-estimation`, and `det:eth`.
The estimator representation is arbitrary and its only numerical operation
is comparison with a fixed rational midpoint. The input is the literal
canonical square-table word, with the public midpoint numerator prefixed.
Actual current-source construction, resource, and source-reduction facts
remain independent premises; no older graph-specific endpoint is promoted.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39FramedNumericalEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.V39FramedNumerical
open CurrentAdditive.DeterministicETHEncodedTable
open CurrentAdditive.DeterministicETHEstimator (real_double_log_le_clog)
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointNumeric
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicEndpointETH
open Paper2.SquarePadding
open Workspace.Types.CommComplexity

/-- General numerical-output fixed additive accuracy on every actual table.
Physical polynomial time and rational comparison belong to E itself. -/
def AccurateFixed (E : Estimator) (u : ℝ) : Prop :=
  ∀ word d, Paper2.AModel.targetD word = some d →
    |E.value (E.output word)-(d:ℝ)| ≤ u

/-- Comparison correctness only on requested rational midpoints for valid
actual table inputs. This need not cover arbitrary numerical output words or
unrequested rational lengths. -/
def ComparableRequests (E : Estimator) (Requests : List Bool → ℕ → Prop) : Prop :=
  ∀ word d m, Paper2.AModel.targetD word = some d → Requests word m → ComparisonAt E word m

/-- General numerical-output eventual accuracy. The one fixed cutoff is
measured in table entries, not in encoded-word length. -/
def EventuallyAccurate (E : Estimator) (c : ℝ) : Prop :=
  ∃ T₀ : ℕ, ∀ word d, Paper2.AModel.targetD word = some d →
    T₀ ≤ CurrentAdditive.Eventual.entries word →
    |E.value (E.output word)-(d:ℝ)| ≤ c *
      Real.logb 2 (Real.logb 2 (CurrentAdditive.Eventual.entries word:ℝ))

/-- Apply the literal eventual-table domain to the very same encoded square.
No decoder for the numerical output is used. -/
theorem accurate_on_square (E : Estimator) (c : ℝ) (hc : 0 ≤ c)
    (hE : EventuallyAccurate E c)
    {S : ℕ} (F : Fin S → Fin S → Bool) (hS : 0 < S)
    (hlarge : hE.choose ≤ S^2) (hfour : 4 ≤ S^2) :
    |E.value (E.output (squareWord F))-(D F:ℝ)| ≤
      c*(Nat.clog 2 (Nat.clog 2 (S^2)):ℝ) := by
  have he : CurrentAdditive.Eventual.entries (squareWord F) = S^2 := by
    simp [CurrentAdditive.Eventual.entries, squareWord_decodes F hS]
    ring
  have hh := hE.choose_spec (squareWord F) (D F) (squareWord_targetD F hS)
    (by rw [he]; exact hlarge)
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (real_double_log_le_clog (S^2) hfour) hc)

/-- The fixed-error endpoint works for arbitrary numerical output words.
Both promise implications use the same actual encoded table and machine. -/
theorem fixed_square_midpoint (E : Estimator) (u : ℝ)
    (hE : AccurateFixed E u) (_hu : 0 ≤ u)
    {S : ℕ} (F : Fin S → Fin S → Bool) (hS : 0 < S)
    (B k : ℕ) (hgap : 2*u < (k:ℝ))
    (hcompare : ComparisonAt E (squareWord F) (2*B+k)) :
    let input := natField (2*B+k) ++ squareWord F
    (D F ≤ B → E.machine.OutputsWithin input [true]
      (E.clockCoefficient*(input.length+1)^E.clockDegree)) ∧
    (B+k ≤ D F → E.machine.OutputsWithin input [false]
      (E.clockCoefficient*(input.length+1)^E.clockDegree)) := by
  have hh := midpoint_outputs E (squareWord F) (D F) B k u hgap
    (hE (squareWord F) (D F) (squareWord_targetD F hS)) hcompare
  constructor
  · intro hD
    simpa only [hh.1 hD] using machine_outputs E (natField (2*B+k) ++ squareWord F)
  · intro hD
    simpa only [hh.2 hD] using machine_outputs E (natField (2*B+k) ++ squareWord F)

/-- A simple fixed formula cutoff makes the estimator's entry-count cutoff
applicable. It does not require estimator accuracy on any finite exception. -/
theorem entry_threshold_from_variables (T₀ m T : ℕ)
    (hm : max 2 T₀ ≤ m) (hT : m^2 ≤ T) : T₀ ≤ T := by
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have hmT : T₀ ≤ m := (le_max_right _ _).trans hm
  have hmsq : m ≤ m^2 := by nlinarith
  exact hmT.trans (hmsq.trans hT)

universe u v

/-- The deterministic growing-error classifier on the exact padded output of
one semantic construction. The comparator permits the manuscript's general
numerical representation, has one fixed all-input physical clock, and does
not compare estimator outputs with each other. Current-source construction,
YES/NO, resource and table identities are visible separate premises. -/
theorem padded_eth_general_output
    {Graph : Type u} {State : Type v}
    (C : Construction Graph State) (G : Graph) (Yes No : Graph → Prop)
    (m N a b C₁ C₀ d₀ h : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hN : 2 ≤ N) (hNlow : m ≤ N) (hNhigh : N ≤ m^b)
    (hC₀ : 2*C₁+2 ≤ C₀)
    (hlarge : 2^(max (32*(C₀*b)+16) (8*a)) ≤ m)
    (V : ValidContract C G) (U : UniversalContract C G d₀ h)
    (Y : Yes G → YesContract C G d₀ h)
    (H : No G → NoContract C G d₀ h)
    (R : ResourceContract C G N (2^a) C₁) (P : TablePresentation C N)
    (E : Estimator) (hE : EventuallyAccurate E (1/(4*(a:ℝ))))
    (hthreshold : hE.choose ≤ m^2)
    (hcompare :
      let k := ethIterations a m
      let M := paddedTable C N P (state C G k)
      ComparisonAt E (squareWord M) (2*budget d₀ h k+k)) :
    let k := ethIterations a m
    let F := state C G k
    let M := paddedTable C N P F
    let input := natField (2*budget d₀ h k+k) ++ squareWord M
    (Yes G → E.machine.OutputsWithin input [true]
      (E.clockCoefficient*(input.length+1)^E.clockDegree)) ∧
    (No G → E.machine.OutputsWithin input [false]
      (E.clockCoefficient*(input.length+1)^E.clockDegree)) := by
  let k := ethIterations a m
  let F := state C G k
  let S := side (P.rows F) (P.cols F)
  let M := paddedTable C N P F
  let input := natField (2*budget d₀ h k+k) ++ squareWord M
  have he := padded_eth_finite_endpoint C G Yes No m N a b C₁ C₀ d₀ h
    ha hb hN hNlow hNhigh hC₀ hlarge V U Y H R P
  change (0:ℝ) < 1/(4*(a:ℝ)) ∧ 1 ≤ k ∧
    ((2^a)^k)^2 ≤ m ∧ D M ≤ budget d₀ h k+k ∧
    (Yes G → D M ≤ budget d₀ h k) ∧
    (No G → D M = budget d₀ h k+k ∧ C.profile G F) ∧
    N ≤ S ∧ (∃ e, S = 2^e) ∧ m^2 ≤ S^2 ∧
    S^2 ≤ m^(b*C₀*(2^a)^k) ∧
    2*(1/(4*(a:ℝ)))*(Nat.clog 2 (Nat.clog 2 (S^2)):ℝ) < (k:ℝ) ∧
    totalStepTime C G k ≤ N^(C₀*(2^a)^k) at he
  rcases he with ⟨hcstar, _, _, _, hy, hn, hs, _, ht, _, hgap, _⟩
  have hS : 0 < S := by omega
  have hfour : 4 ≤ S^2 := by nlinarith
  let error := (1/(4*(a:ℝ)))*(Nat.clog 2 (Nat.clog 2 (S^2)):ℝ)
  have hacc := accurate_on_square E (1/(4*(a:ℝ))) hcstar.le hE M hS
    (hthreshold.trans ht) hfour
  have hgap' : 2*error < (k:ℝ) := by simpa only [error, mul_assoc] using hgap
  have hmid := midpoint_outputs E (squareWord M) (D M) (budget d₀ h k) k
    error hgap' hacc hcompare
  constructor
  · intro hyes
    simpa only [input, hmid.1 (hy hyes)] using machine_outputs E input
  · intro hno
    have hD : budget d₀ h k+k ≤ D M := (hn hno).1.ge
    simpa only [input, hmid.2 hD] using machine_outputs E input

#print axioms accurate_on_square
#print axioms fixed_square_midpoint
#print axioms entry_threshold_from_variables
#print axioms padded_eth_general_output

end CurrentAdditive.V39FramedNumericalEndpoint
