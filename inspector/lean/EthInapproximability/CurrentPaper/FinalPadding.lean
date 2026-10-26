import EthInapproximability.CurrentPaper.WeightedDuplication
import Mathlib.Data.Nat.Log

/-!
# Common square padding and the current approximation allowance

Source: v8 `06-eth.tex`, `eq:paper-padding-invariance`,
`eq:paper-length-clock-allowance`, and `eq:paper-length-clock-gap-fit`.

Padding is an actual input map, with explicit right inverses. The allowance
below is the current floor-log formula, not the older plateau search.
Clock monotonicity/unboundedness and the reduction's gap remain explicit
inputs to these generic consequences. This module proves no machine runtime
or ETH contradiction, and does not assume either as an opaque proposition.
-/

namespace EthInapproximability.CurrentPaper.FinalPadding

open Workspace.Types.CommComplexity
open EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-- Zero-based form of the paper's map: unused labels repeat the first input. -/
def inputMap (d p : ℕ) (hd : 0 < d) (u : Fin (2 ^ p)) : Fin d :=
  if h : u.val < d then ⟨u.val, h⟩ else ⟨0, hd⟩

def inputSection (d p : ℕ) (hfit : d ≤ 2 ^ p) (u : Fin d) : Fin (2 ^ p) :=
  ⟨u.val, lt_of_lt_of_le u.isLt hfit⟩

@[simp] theorem inputMap_section (d p : ℕ) (hd : 0 < d) (hfit : d ≤ 2 ^ p)
    (u : Fin d) : inputMap d p hd (inputSection d p hfit u) = u := by
  simp [inputMap, inputSection, u.isLt]

theorem inputMap_surjective (d p : ℕ) (hd : 0 < d) (hfit : d ≤ 2 ^ p) :
    Function.Surjective (inputMap d p hd) :=
  fun u => ⟨inputSection d p hfit u, inputMap_section d p hd hfit u⟩

def matrix {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) : Fin (2 ^ p) → Fin (2 ^ p) → Bool :=
  fun u v => R (inputMap m p hm u) (inputMap r p hr v)

theorem D_matrix {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) (hrows : m ≤ 2 ^ p) (hcols : r ≤ 2 ^ p) :
    D (matrix R p hm hr) = D R :=
  D_forget_eq R (inputMap m p hm) (inputMap r p hr)
    (inputSection m p hrows) (inputSection r p hcols)
    (inputMap_section m p hm hrows) (inputMap_section r p hr hcols)

/-- The explicit row-major padded truth table, with every output bit present. -/
def table {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) : List Bool :=
  (List.ofFn fun u : Fin (2 ^ p) =>
    List.ofFn fun v : Fin (2 ^ p) => matrix R p hm hr u v).flatten

theorem table_length {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) : (table R p hm hr).length = 2 ^ (2 * p) := by
  simp [table, List.length_flatten, Function.comp_def, List.ofFn_const,
    List.sum_replicate, ← pow_add, two_mul]

theorem table_eq_ofFn {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) :
    table R p hm hr = List.ofFn (fun k : Fin (2 ^ p * 2 ^ p) =>
      matrix R p hm hr (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  unfold table
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have he : (⟨u.val * 2 ^ p + v.val, by
      have := u.isLt
      have := v.isLt
      nlinarith [Nat.zero_le (2 ^ p)]⟩ : Fin (2 ^ p * 2 ^ p)) =
      finProdFinEquiv (u, v) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [he, Equiv.symm_apply_apply]

theorem table_entry {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) (u v : Fin (2 ^ p)) :
    (table R p hm hr)[u.val * 2 ^ p + v.val]? = some (matrix R p hm hr u v) := by
  rw [table_eq_ofFn]
  have hidx : u.val * 2 ^ p + v.val < 2 ^ p * 2 ^ p := by
    have := u.isLt
    have := v.isLt
    nlinarith [Nat.zero_le (2 ^ p)]
  rw [List.getElem?_ofFn, dif_pos hidx]
  have he : (⟨u.val * 2 ^ p + v.val, hidx⟩ : Fin (2 ^ p * 2 ^ p)) =
      finProdFinEquiv (u, v) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [he, Equiv.symm_apply_apply]

def exponent (L : ℕ → ℕ) (n : ℕ) : ℕ := n / (2 * max 1 (L n))

def tableSize (L : ℕ → ℕ) (n : ℕ) : ℕ := 2 ^ (2 * exponent L n)

/-- The floor-log formula in the current paper, including its small-input convention. -/
def allowance (L : ℕ → ℕ) (T : ℕ) : ℕ := L (Nat.log 2 (max T 2)) / 4

theorem twice_exponent_le (L : ℕ → ℕ) (n : ℕ) : 2 * exponent L n ≤ n := by
  have h := Nat.div_mul_le_self n (2 * max 1 (L n))
  have hmul : 2 * exponent L n ≤ exponent L n * (2 * max 1 (L n)) := by
    have hm : 1 ≤ max 1 (L n) := le_max_left _ _
    have hh := Nat.mul_le_mul_left (exponent L n)
      (show 2 ≤ 2 * max 1 (L n) by omega)
    simpa only [Nat.mul_comm (exponent L n) 2] using hh
  exact hmul.trans h

theorem log_tableSize (L : ℕ → ℕ) (n : ℕ) (hp : 0 < exponent L n) :
    Nat.log 2 (max (tableSize L n) 2) = 2 * exponent L n := by
  have htwo : 2 ≤ tableSize L n := by
    change 2 ^ 1 ≤ 2 ^ (2 * exponent L n)
    exact Nat.pow_le_pow_right (by omega) (by omega)
  rw [max_eq_left htwo]
  exact Nat.log_pow (by omega) _

theorem allowance_monotone (L : ℕ → ℕ) (hL : Monotone L) :
    Monotone (allowance L) := by
  intro a b hab
  exact Nat.div_le_div_right (hL (Nat.log_mono_right (max_le_max_right 2 hab)))

theorem allowance_unbounded (L : ℕ → ℕ) (hmono : Monotone L)
    (hL : ∀ K, ∃ n, K ≤ L n) : ∀ K, ∃ T, K ≤ allowance L T := by
  intro K
  obtain ⟨n, hn⟩ := hL (4 * K)
  refine ⟨2 ^ max 1 n, ?_⟩
  have htwo : 2 ≤ 2 ^ max 1 n := by
    change 2 ^ 1 ≤ 2 ^ max 1 n
    exact Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  unfold allowance
  rw [max_eq_left htwo, Nat.log_pow (by omega : 1 < 2)]
  have hle := hmono (le_max_right 1 n)
  omega

theorem gap_fit (L : ℕ → ℕ) (hL : Monotone L) (n : ℕ)
    (hk : 0 < L n) (hp : 0 < exponent L n) :
    2 * allowance L (tableSize L n) < L n := by
  have hc : L (Nat.log 2 (max (tableSize L n) 2)) ≤ L n := by
    rw [log_tableSize L n hp]
    exact hL (twice_exponent_le L n)
  have hd := Nat.div_mul_le_self (L (Nat.log 2 (max (tableSize L n) 2))) 4
  unfold allowance
  omega

/-- A positive clock alone cannot replace the positive-padding guard. -/
theorem zero_exponent_regression :
    let L : ℕ → ℕ := fun n => 4 * (n + 1)
    exponent L 0 = 0 ∧ tableSize L 0 = 1 ∧ allowance L 1 = 2 ∧
      ¬ (2 * allowance L (tableSize L 0) < L 0) := by decide

theorem midpoint_yes (a : ℤ) (cost Y A k : ℕ)
    (hcost : cost ≤ Y) (herror : |a - (cost : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k) : 2 * a < 2 * (Y : ℤ) + (k : ℤ) := by
  have h := (abs_le.mp herror).2
  omega

theorem midpoint_no (a : ℤ) (Y A k : ℕ)
    (herror : |a - ((Y + k : ℕ) : ℤ)| ≤ (A : ℤ))
    (hgap : 2 * A < k) : 2 * (Y : ℤ) + (k : ℤ) < 2 * a := by
  have h := (abs_le.mp herror).1
  omega

end EthInapproximability.CurrentPaper.FinalPadding
