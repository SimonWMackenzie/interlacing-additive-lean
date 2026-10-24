import EthInapproximability.CurrentPaper.PrimeSampler

/-!
# Modular Horner evaluation of the indexed prime family

Source: frozen v8 `B-effectivity-details.tex`, the explicit balanced-family
accessor. This pure recurrence isolates the arithmetic that the physical
division and multiply-add controllers must implement. It is not itself
a runtime claim. Each recursive call removes the lowest base-p digit;
unwinding performs a bounded modular Horner step.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerEntryAlgorithm

open scoped BigOperators

def polynomialSum (p t l j : ℕ) : ℕ :=
  ∑ r ∈ Finset.range t, (l/p^r%p)*j^r

def horner (p j : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t+1, l => (l%p+j*horner p j t (l/p))%p

theorem polynomialSum_succ (p t l j : ℕ) :
    polynomialSum p (t+1) l j = l%p+j*polynomialSum p t (l/p) j := by
  unfold polynomialSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one, mul_one]
  rw [Nat.add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [pow_succ, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm p (p^r)]
  ring

theorem horner_eq (p j t l : ℕ) : horner p j t l = polynomialSum p t l j%p := by
  induction t generalizing l with
  | zero => simp [horner, polynomialSum]
  | succ t ih =>
      rw [horner, ih, polynomialSum_succ]
      simp [Nat.add_mod, Nat.mul_mod]

def entry (p t m l j : ℕ) : ℕ := horner p j t l % m

theorem entry_eq (p t m l j : ℕ) : entry p t m l j = PrimeSampler.entry p t m l j := by
  rw [entry, horner_eq]
  rfl

theorem horner_lt (p j t l : ℕ) (hp : 0 < p) : horner p j t l < p := by
  rw [horner_eq]
  exact Nat.mod_lt _ hp

theorem quotient_le (p l : ℕ) : l/p ≤ l := Nat.div_le_self _ _

theorem local_operand_bound (p j t l : ℕ) (hp : 0 < p) (hj : j < p) :
    l%p+j*horner p j t (l/p) < p*(p+1) := by
  have hd := Nat.mod_lt l hp
  have hh := horner_lt p j t (l/p) hp
  nlinarith

theorem zero_label (p j t : ℕ) : horner p j t 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [horner, ih]

/-- Fixed-width base-p digits in most-significant-first order. -/
def coefficients (p : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | t+1, l => coefficients p t (l/p) ++ [l%p]

theorem coefficients_length (p t l : ℕ) : (coefficients p t l).length=t := by
  induction t generalizing l with
  | zero => rfl
  | succ t ih => simp [coefficients, ih]

theorem coefficients_lt (p t l : ℕ) (hp : 0<p) :
    ∀ a ∈ coefficients p t l, a<p := by
  induction t generalizing l with
  | zero => simp [coefficients]
  | succ t ih =>
      intro a ha
      simp only [coefficients, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha|ha
      · exact ih (l/p) a ha
      · subst a; exact Nat.mod_lt _ hp

def evaluate (p j : ℕ) (as : List ℕ) (initial : ℕ) : ℕ :=
  as.foldl (fun a digit => (j*a+digit)%p) initial

theorem evaluate_coefficients (p j t l : ℕ) :
    evaluate p j (coefficients p t l) 0=horner p j t l := by
  induction t generalizing l with
  | zero => rfl
  | succ t ih =>
      simp only [coefficients, evaluate, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (j*evaluate p j (coefficients p t (l/p)) 0+l%p)%p=_
      rw [ih, horner, Nat.add_comm]

theorem regressions :
    horner 5 2 3 86 = 2 ∧ entry 5 3 2 86 2 = 0 ∧
      horner 5 3 0 17 = 0 ∧ horner 5 3 8 0 = 0 := by decide

end EthInapproximability.CurrentPaper.PrimeSamplerEntryAlgorithm
