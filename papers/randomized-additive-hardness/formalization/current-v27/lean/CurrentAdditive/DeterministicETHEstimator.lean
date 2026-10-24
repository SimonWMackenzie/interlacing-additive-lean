import CurrentAdditive.DeterministicETHEncodedTable
import CurrentAdditive.EventualDomain

/-! Literal deterministic eventual-table estimator interface in the
existing TM2/encoded-matrix model, with a checked bridge from real binary
double logarithms to the finite integer ceiling used by det:eth. -/

namespace CurrentAdditive.DeterministicETHEstimator

open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicETHEncodedTable

/-- The manuscript's deterministic polynomial-time estimator: one fixed
physical TM2 machine computes the output word, which must decode to a
dyadic estimate on every sufficiently large canonical matrix input. -/
def EventuallyAccurate (est : List Bool → List Bool) (c : ℝ) : Prop :=
  BitMachine.Polytime est ∧
  ∃ T₀ : ℕ, ∀ w d, Paper2.AModel.targetD w = some d →
    T₀ ≤ CurrentAdditive.Eventual.entries w →
    ∃ z, Paper2.AModel.decodeDyadic (est w) = some z ∧
      |z-(d:ℝ)| ≤ c *
        Real.logb 2 (Real.logb 2 (CurrentAdditive.Eventual.entries w:ℝ))

theorem real_double_log_le_clog (T : ℕ) (hT : 4 ≤ T) :
    Real.logb 2 (Real.logb 2 (T:ℝ)) ≤
      (Nat.clog 2 (Nat.clog 2 T):ℝ) := by
  have hTpos : (1:ℝ) < T := by exact_mod_cast (by omega : 1 < T)
  have hlogpos : (0:ℝ) < Real.logb 2 (T:ℝ) :=
    Real.logb_pos (by norm_num : (1:ℝ) < 2) hTpos
  have hclog : 1 < Nat.clog 2 T :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).2 (by omega)
  have hclogpos : (0:ℝ) < (Nat.clog 2 T:ℝ) := by exact_mod_cast (by omega : 0 < Nat.clog 2 T)
  have hfirst : Real.logb 2 (T:ℝ) ≤ (Nat.clog 2 T:ℝ) := by
    have hc := Real.natCeil_logb_natCast 2 T
    rw [← hc]
    exact Nat.le_ceil _
  have hsecond :=
    (Real.logb_le_logb (by norm_num : (1:ℝ) < 2) hlogpos hclogpos).2 hfirst
  have hthird : Real.logb 2 (Nat.clog 2 T:ℝ) ≤
      (Nat.clog 2 (Nat.clog 2 T):ℝ) := by
    have hc := Real.natCeil_logb_natCast 2 (Nat.clog 2 T)
    rw [← hc]
    exact Nat.le_ceil _
  exact hsecond.trans hthird

/-- Apply the literal eventual error guarantee to the exact encoded square
table. This does not assume that an arbitrary semantic table is magically
available to the estimator; it uses its canonical serialized word. -/
theorem accurate_on_encoded_square
    (est : List Bool → List Bool) (c : ℝ)
    (hc : 0 ≤ c) (hest : EventuallyAccurate est c)
    {S : ℕ} (F : Fin S → Fin S → Bool) (hS : 0 < S)
    (hTlarge : hest.2.choose ≤ S^2) (hTfour : 4 ≤ S^2) :
    ∃ z, Paper2.AModel.decodeDyadic (est (squareWord F)) = some z ∧
      |z-(D F:ℝ)| ≤ c *
        (Nat.clog 2 (Nat.clog 2 (S^2)):ℝ) := by
  have he : CurrentAdditive.Eventual.entries (squareWord F) = S^2 := by
    simp [CurrentAdditive.Eventual.entries, squareWord_decodes F hS]
    ring
  obtain ⟨z, hz, herror⟩ := hest.2.choose_spec (squareWord F) (D F)
    (squareWord_targetD F hS) (by rw [he]; exact hTlarge)
  refine ⟨z, hz, ?_⟩
  rw [he] at herror
  exact herror.trans (mul_le_mul_of_nonneg_left
    (real_double_log_le_clog (S^2) hTfour) hc)

#print axioms real_double_log_le_clog
#print axioms accurate_on_encoded_square

end CurrentAdditive.DeterministicETHEstimator
