import Mathlib

/-!
# Finite programs of uniform choices

Frozen v12, the finite sampling constructions and their bounded-choice
implementation. A program asks only for a uniform element of an explicitly
given nonempty `Fin n`. Its output carrier need not be enumerated or finite.
The expectation and maximum number of requests are computed recursively on
this syntax. These are finite-choice semantics, not a machine-runtime theorem.
-/

namespace Paper2.RecursiveSamplingProgram

open scoped BigOperators

/-- A finite, possibly adaptive tree of requests for uniform finite choices. -/
inductive Program (A : Type*) : Type _ where
  | pure (a : A)
  | draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program A)

namespace Program

variable {A B C : Type*}

/-- Substitute the continuation at each output leaf. -/
def bind (p : Program A) (f : A → Program B) : Program B :=
  match p with
  | .pure a => f a
  | .draw n hn next => .draw n hn (fun i => bind (next i) f)

/-- Apply a deterministic function to the final output. -/
def map (f : A → B) (p : Program A) : Program B :=
  bind p (fun a => .pure (f a))

/-- One request, with no enumeration of a larger output carrier. -/
def uniform (n : ℕ) (hn : 0 < n) : Program (Fin n) :=
  .draw n hn .pure

/-- The expected real payoff under independent uniform choices at each node. -/
noncomputable def expect (p : Program A) (f : A → ℝ) : ℝ :=
  match p with
  | .pure a => f a
  | .draw n _ next => (n : ℝ)⁻¹ * ∑ i, expect (next i) f

/-- Probability of an output event, without a finiteness assumption on `A`. -/
noncomputable def eventProb (p : Program A) (S : Set A) : ℝ :=
  expect p (S.indicator (fun _ => 1))

/-- Maximum number of finite-choice requests along any branch. -/
def maxDraws (p : Program A) : ℕ :=
  match p with
  | .pure _ => 0
  | .draw _ _ next => 1 + Finset.univ.sup (fun i => maxDraws (next i))

def IsBounded (p : Program A) (N : ℕ) : Prop := maxDraws p ≤ N

/-- Largest requested alphabet, with `1` at a finished leaf. -/
def maxAlphabet (p : Program A) : ℕ :=
  match p with
  | .pure _ => 1
  | .draw n _ next => max n (Finset.univ.sup (fun i => maxAlphabet (next i)))

@[simp] theorem bind_pure (a : A) (f : A → Program B) :
    bind (.pure a) f = f a := rfl

@[simp] theorem bind_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program A)
    (f : A → Program B) :
    bind (.draw n hn next) f = .draw n hn (fun i => bind (next i) f) := rfl

@[simp] theorem map_pure (f : A → B) (a : A) :
    map f (.pure a) = .pure (f a) := rfl

@[simp] theorem map_draw (f : A → B) (n : ℕ) (hn : 0 < n)
    (next : Fin n → Program A) :
    map f (.draw n hn next) = .draw n hn (fun i => map f (next i)) := rfl

@[simp] theorem expect_pure (a : A) (f : A → ℝ) :
    expect (.pure a) f = f a := rfl

@[simp] theorem expect_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program A)
    (f : A → ℝ) :
    expect (.draw n hn next) f = (n : ℝ)⁻¹ * ∑ i, expect (next i) f := rfl

@[simp] theorem expect_uniform (n : ℕ) (hn : 0 < n) (f : Fin n → ℝ) :
    expect (uniform n hn) f = (n : ℝ)⁻¹ * ∑ i, f i := rfl

@[simp] theorem maxDraws_pure (a : A) : maxDraws (.pure a) = 0 := rfl

@[simp] theorem maxDraws_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program A) :
    maxDraws (.draw n hn next) = 1 + Finset.univ.sup (fun i => maxDraws (next i)) := rfl

@[simp] theorem maxDraws_uniform (n : ℕ) (hn : 0 < n) :
    maxDraws (uniform n hn) = 1 := by simp [uniform]

theorem expect_bind (p : Program A) (f : A → Program B) (g : B → ℝ) :
    expect (bind p f) g = expect p (fun a => expect (f a) g) := by
  induction p with
  | pure a => rfl
  | draw n hn next ih => simp only [bind_draw, expect_draw, ih]

theorem expect_map (f : A → B) (p : Program A) (g : B → ℝ) :
    expect (map f p) g = expect p (fun a => g (f a)) := by
  simp only [map, expect_bind, expect_pure]

theorem expect_const (p : Program A) (c : ℝ) : expect p (fun _ => c) = c := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
    simp only [expect_draw, ih, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]

theorem expect_nonneg (p : Program A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ expect p f := by
  induction p with
  | pure a => exact hf a
  | draw n hn next ih =>
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun i _ => ih i))

theorem expect_mono (p : Program A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    expect p f ≤ expect p g := by
  induction p with
  | pure a => exact h a
  | draw n hn next ih =>
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ih i))
      (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem expect_add (p : Program A) (f g : A → ℝ) :
    expect p (fun a => f a + g a) = expect p f + expect p g := by
  induction p with
  | pure a => rfl
  | draw n hn next ih => simp only [expect_draw, ih, Finset.sum_add_distrib, mul_add]

theorem expect_mul (p : Program A) (c : ℝ) (f : A → ℝ) :
    expect p (fun a => c * f a) = c * expect p f := by
  induction p with
  | pure a => rfl
  | draw n hn next ih =>
    simp only [expect_draw, ih, ← Finset.mul_sum]
    ring

theorem eventProb_nonneg (p : Program A) (S : Set A) : 0 ≤ eventProb p S := by
  apply expect_nonneg
  exact Set.indicator_nonneg (fun _ _ => zero_le_one)

theorem eventProb_le_one (p : Program A) (S : Set A) : eventProb p S ≤ 1 := by
  rw [← expect_const p 1]
  apply expect_mono
  intro a
  by_cases ha : a ∈ S <;> simp [ha]

@[simp] theorem eventProb_univ (p : Program A) : eventProb p Set.univ = 1 := by
  simp [eventProb, expect_const]

@[simp] theorem eventProb_empty (p : Program A) : eventProb p ∅ = 0 := by
  simp [eventProb, expect_const]

theorem maxDraws_bind_le (p : Program A) (f : A → Program B) (N : ℕ)
    (hf : ∀ a, maxDraws (f a) ≤ N) :
    maxDraws (bind p f) ≤ maxDraws p + N := by
  induction p with
  | pure a => simpa using hf a
  | draw n hn next ih =>
    simp only [bind_draw, maxDraws_draw]
    have hsup : Finset.univ.sup (fun i => maxDraws (bind (next i) f)) ≤
        Finset.univ.sup (fun i => maxDraws (next i)) + N := by
      apply Finset.sup_le
      intro i hi
      exact (ih i).trans (Nat.add_le_add_right
        (Finset.le_sup (f := fun j => maxDraws (next j)) hi) N)
    omega

@[simp] theorem maxDraws_map (f : A → B) (p : Program A) :
    maxDraws (map f p) = maxDraws p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih => simp only [map_draw, maxDraws_draw, ih]

theorem IsBounded.bind {p : Program A} {f : A → Program B} {N M : ℕ}
    (hp : IsBounded p N) (hf : ∀ a, IsBounded (f a) M) :
    IsBounded (bind p f) (N + M) :=
  (maxDraws_bind_le p f M hf).trans (Nat.add_le_add_right hp M)

theorem IsBounded.map {p : Program A} {N : ℕ} (hp : IsBounded p N) (f : A → B) :
    IsBounded (map f p) N := by simpa [IsBounded] using hp

@[simp] theorem maxAlphabet_pure (a : A) : maxAlphabet (.pure a) = 1 := rfl

@[simp] theorem maxAlphabet_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program A) :
    maxAlphabet (.draw n hn next) =
      max n (Finset.univ.sup (fun i => maxAlphabet (next i))) := rfl

theorem maxAlphabet_pos (p : Program A) : 0 < maxAlphabet p := by
  cases p with
  | pure a => exact Nat.zero_lt_one
  | draw n hn next => exact hn.trans_le (Nat.le_max_left _ _)

@[simp] theorem maxAlphabet_uniform (n : ℕ) (hn : 0 < n) :
    maxAlphabet (uniform n hn) = n := by
  simp only [uniform, maxAlphabet_draw, maxAlphabet_pure]
  apply Nat.max_eq_left
  exact Finset.sup_le (fun _ _ => hn)

theorem maxAlphabet_bind_le (p : Program A) (f : A → Program B) (M : ℕ)
    (hf : ∀ a, maxAlphabet (f a) ≤ M) :
    maxAlphabet (bind p f) ≤ max (maxAlphabet p) M := by
  induction p with
  | pure a => exact (hf a).trans (Nat.le_max_right _ _)
  | draw n hn next ih =>
    simp only [bind_draw, maxAlphabet_draw]
    apply max_le
    · exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
    · apply Finset.sup_le
      intro i hi
      apply (ih i).trans
      apply max_le
      · exact (Finset.le_sup (f := fun j => maxAlphabet (next j)) hi).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
      · exact Nat.le_max_right _ _

@[simp] theorem maxAlphabet_map (f : A → B) (p : Program A) :
    maxAlphabet (map f p) = maxAlphabet p := by
  induction p with
  | pure a => rfl
  | draw n hn next ih => simp only [map_draw, maxAlphabet_draw, ih]

end Program

#print axioms Program.expect_bind
#print axioms Program.expect_const
#print axioms Program.eventProb_le_one
#print axioms Program.maxDraws_bind_le

end Paper2.RecursiveSamplingProgram
