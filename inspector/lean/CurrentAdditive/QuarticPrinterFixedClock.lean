import CurrentAdditive.QuarticPrefixFit
import CurrentAdditive.QuarticSquareMachine

/-! The v27 physical square printer has a tape-independent declared clock. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

def selectedOutputLength27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  let o := select27 hn edge Δ γ k
  2 * (o.rows.bits.length + o.cols.bits.length + o.budget.bits.length) +
    3 + o.rows * o.cols

theorem selectedOutputLength_eq27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    (outputBits27 hn edge Δ γ k t).length =
      selectedOutputLength27 hn edge Δ γ k := by
  simpa only [selectedOutputLength27] using
    outputBits27_length hn edge Δ γ k t

def squarePrinterClock27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (C E k : ℕ) : ℕ :=
  C * (n + 2) ^ (E * (k + 1)) +
    2 * selectedOutputLength27 hn edge Δ γ k + 2 +
    Paper2.ASquare.Post.squareCP *
      (selectedOutputLength27 hn edge Δ γ k + 1) ^
        Paper2.ASquare.Post.squareEP

theorem squarePrinterClock_eq27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (C E k : ℕ) (t : (select27 hn edge Δ γ k).Tape) :
    C * (n + 2) ^ (E * (k + 1)) +
      2 * (outputBits27 hn edge Δ γ k t).length + 2 +
      Paper2.ASquare.Post.squareCP *
        ((outputBits27 hn edge Δ γ k t).length + 1) ^
          Paper2.ASquare.Post.squareEP =
      squarePrinterClock27 hn edge Δ γ C E k := by
  rw [selectedOutputLength_eq27 hn edge Δ γ k t]
  rfl

#print axioms selectedOutputLength_eq27
#print axioms squarePrinterClock_eq27

end Paper2.CurrentAdditive.QuarticClassEndpoint
