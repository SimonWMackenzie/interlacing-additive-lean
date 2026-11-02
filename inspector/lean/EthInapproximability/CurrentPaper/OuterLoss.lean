import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Current replacement paper: the loss along an unsplit route

Source: v8 `A-stage4-details.tex`, the routing-stable transfer and the
paragraph "The outer interlace" in the terminal two-stream proof.

The trajectory consists of actual finite supports. Its one-step cardinal
losses telescope, and the finite dyadic budget is strictly less than the
initial budget. The statements do not construct a protocol route or assert
that its local losses obey this budget: these remain explicit inputs.
-/

namespace EthInapproximability.CurrentPaper.OuterLoss

variable {X : Type*}

/-- A nested finite-support trajectory stays inside its initial support. -/
theorem subset_start (R : ℕ → Finset X) (n : ℕ)
    (hnested : ∀ d < n, R (d + 1) ⊆ R d) : R n ⊆ R 0 := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    exact Finset.Subset.trans (hnested n (by omega))
      (ih (fun d hd => hnested d (by omega)))

/-- The signed cardinal losses telescope to the finite geometric bound.
This arithmetic fact does not require nestedness. -/
theorem card_loss_geometric (R : ℕ → Finset X) (budget : ℝ) (n : ℕ)
    (hstep : ∀ d < n,
      (R d).card - ((R (d + 1)).card : ℝ) ≤ budget * (1 / 2 : ℝ) ^ (d + 1)) :
    (R 0).card - ((R n).card : ℝ) ≤ budget * (1 - (1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprior := ih (fun d hd => hstep d (by omega))
    have hnext := hstep n (by omega)
    have hidentity : budget * (1 - (1 / 2 : ℝ) ^ n) +
        budget * (1 / 2 : ℝ) ^ (n + 1) =
        budget * (1 - (1 / 2 : ℝ) ^ (n + 1)) := by
      rw [pow_succ]
      ring
    linarith

/-- With a positive budget, every finite route loses strictly less than the
whole infinite geometric budget, including the length-zero route. -/
theorem card_loss_lt (R : ℕ → Finset X) (budget : ℝ) (n : ℕ)
    (hbudget : 0 < budget)
    (hstep : ∀ d < n,
      (R d).card - ((R (d + 1)).card : ℝ) ≤ budget * (1 / 2 : ℝ) ^ (d + 1)) :
    (R 0).card - ((R n).card : ℝ) < budget := by
  have htotal := card_loss_geometric R budget n hstep
  have hpositive : 0 < budget * (1 / 2 : ℝ) ^ n :=
    mul_pos hbudget (pow_pos (by norm_num) n)
  nlinarith

/-- Nestedness identifies signed loss with the cardinality difference in
the natural numbers, avoiding accidental truncated-subtraction semantics. -/
theorem nat_card_loss_geometric (R : ℕ → Finset X) (budget : ℝ) (n : ℕ)
    (hnested : ∀ d < n, R (d + 1) ⊆ R d)
    (hstep : ∀ d < n,
      (R d).card - ((R (d + 1)).card : ℝ) ≤ budget * (1 / 2 : ℝ) ^ (d + 1)) :
    (((R 0).card - (R n).card : ℕ) : ℝ) ≤ budget * (1 - (1 / 2 : ℝ) ^ n) := by
  rw [Nat.cast_sub (Finset.card_le_card (subset_start R n hnested))]
  exact card_loss_geometric R budget n hstep

/-- The paper's ambient-pair formulation. An unsplit route discards fewer
than `tau / 2^(d+1)` times the ambient cardinality at step `d`. -/
theorem unsplit_card_loss_lt (R : ℕ → Finset X) (tau : ℝ) (ambient n : ℕ)
    (htau : 0 < tau) (hambient : 0 < ambient)
    (hnested : ∀ d < n, R (d + 1) ⊆ R d)
    (hstep : ∀ d < n,
      (R d).card - ((R (d + 1)).card : ℝ) <
        tau * (1 / 2 : ℝ) ^ (d + 1) * ambient) :
    (((R 0).card - (R n).card : ℕ) : ℝ) < tau * ambient := by
  rw [Nat.cast_sub (Finset.card_le_card (subset_start R n hnested))]
  apply card_loss_lt R (tau * ambient) n
  · exact mul_pos htau (by exact_mod_cast hambient)
  · intro d hd
    calc
      _ ≤ tau * (1 / 2 : ℝ) ^ (d + 1) * ambient := (hstep d hd).le
      _ = _ := by ring

end EthInapproximability.CurrentPaper.OuterLoss
