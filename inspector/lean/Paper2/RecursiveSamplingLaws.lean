import Paper2.RecursiveSamplingProgram
import Paper2.SourceLawBinding

/-!
# Exact laws of recursive finite-alphabet generators

Frozen source: v12 Appendix D, `app:implementation`, the finite recursive
generators and their independent tuple draws.  A program generates a law
when its expectation agrees for every real-valued payoff.  Products and
tuples below are generated one coordinate at a time; their implementations
do not enumerate the product carrier.  The finite sums appear only in the
proof of their exact distributions.

This module counts ideal elementary draws.  Capped fair-bit execution,
source-specific generators, and machine-time bounds are separate obligations.
-/

namespace Paper2.RecursiveSamplingLaws

open scoped BigOperators
open RecursiveSamplingProgram

variable {A B : Type*} [Fintype A] [Fintype B]

private theorem rationalLaw_ext {μ ν : PositiveRationalLaw A}
    (h : μ.weight = ν.weight) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

theorem uniform_prod [Nonempty A] [Nonempty B] :
    (PositiveRationalLaw.uniform A).prod (PositiveRationalLaw.uniform B) =
      PositiveRationalLaw.uniform (A × B) := by
  apply rationalLaw_ext
  funext a
  simp [PositiveRationalLaw.uniform, PositiveRationalLaw.prod, Fintype.card_prod, mul_comm]

theorem uniform_iid [Nonempty A] (n : ℕ) :
    (PositiveRationalLaw.uniform A).iid n =
      PositiveRationalLaw.uniform (Fin n → A) := by
  apply rationalLaw_ext
  funext a
  simp [PositiveRationalLaw.uniform, PositiveRationalLaw.iid]

/-- Exact finite-law semantics, including all joint events and payoffs. -/
def Generates (p : Program A) (μ : FiniteLaw A) : Prop :=
  ∀ f : A → ℝ, Program.expect p f = ∑ a, μ.weight a * f a

theorem generates_eventProb {p : Program A} {μ : FiniteLaw A}
    (hp : Generates p μ) (E : Set A) :
    Program.eventProb p E = μ.prob (fun a => a ∈ E) := by
  classical
  rw [Program.eventProb, hp]
  simp only [Set.indicator_apply, FiniteLaw.prob, mul_ite, mul_one, mul_zero]

/-- A deterministic map may be checked against its exact finite pushforward. -/
theorem generates_map {p : Program A} {μ : FiniteLaw A}
    (hp : Generates p μ) (f : A → B) (ν : FiniteLaw B)
    (hf : ∀ g : B → ℝ, (∑ a, μ.weight a * g (f a)) = ∑ b, ν.weight b * g b) :
    Generates (Program.map f p) ν := by
  intro g
  rw [Program.expect_map, hp]
  exact hf g

/-- Point-fibre weights suffice to check the preceding pushforward condition. -/
theorem generates_map_of_fibres {p : Program A} {μ : FiniteLaw A}
    (hp : Generates p μ) (f : A → B) (ν : FiniteLaw B)
    (hf : ∀ b, μ.prob (fun a => f a = b) = ν.weight b) :
    Generates (Program.map f p) ν := by
  classical
  apply generates_map hp f ν
  intro g
  calc
    _ = ∑ a, ∑ b, if f a = b then μ.weight a * g b else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b, ∑ a, if f a = b then μ.weight a * g b else 0 := Finset.sum_comm
    _ = ∑ b, μ.prob (fun a => f a = b) * g b := by
      simp only [FiniteLaw.prob, Finset.sum_mul, ite_mul, zero_mul]
    _ = _ := by simp_rw [hf]

theorem generates_equiv {p : Program A} {μ : FiniteLaw A}
    (hp : Generates p μ) (e : A ≃ B) (ν : FiniteLaw B)
    (hw : ∀ a, ν.weight (e a) = μ.weight a) :
    Generates (Program.map e p) ν := by
  apply generates_map hp e ν
  intro g
  exact Fintype.sum_equiv e _ _ (fun a => by rw [hw])

/-- Transport uses the same bijection as the positive rational law. -/
theorem generates_relabel {p : Program A} {μ : PositiveRationalLaw A}
    (hp : Generates p μ.toFiniteLaw) (e : A ≃ B) :
    Generates (Program.map e p) (μ.relabel e).toFiniteLaw := by
  apply generates_equiv hp e
  intro a
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.relabel,
    e.symm_apply_apply]

theorem generates_uniform (n : ℕ) [NeZero n] :
    Generates (Program.uniform n (Nat.pos_of_ne_zero (NeZero.ne n)))
      (PositiveRationalLaw.uniform (Fin n)).toFiniteLaw := by
  intro f
  rw [Program.expect_uniform]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]

theorem generates_uniform_equiv (n : ℕ) [NeZero n] [Nonempty B]
    (e : Fin n ≃ B) :
    Generates
      (Program.map e (Program.uniform n (Nat.pos_of_ne_zero (NeZero.ne n))))
      (PositiveRationalLaw.uniform B).toFiniteLaw := by
  apply generates_equiv (generates_uniform n) e
  intro a
  have hc : Fintype.card B = n := (Fintype.card_congr e).symm.trans (Fintype.card_fin n)
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform, hc,
    Fintype.card_fin]

/-- Independent generation is sequential composition with a fresh second draw. -/
def prod (p : Program A) (q : Program B) : Program (A × B) :=
  Program.bind p (fun a => Program.map (fun b => (a, b)) q)

theorem generates_prod {p : Program A} {q : Program B}
    {μ : FiniteLaw A} {ν : FiniteLaw B}
    (hp : Generates p μ) (hq : Generates q ν) :
    Generates (prod p q) (μ.prod ν) := by
  unfold Generates at hp hq ⊢
  intro f
  simp only [prod, Program.expect_bind, Program.expect_map]
  rw [hp]
  simp_rw [hq]
  simp only [FiniteLaw.prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem generates_rational_prod {p : Program A} {q : Program B}
    {μ : PositiveRationalLaw A} {ν : PositiveRationalLaw B}
    (hp : Generates p μ.toFiniteLaw) (hq : Generates q ν.toFiniteLaw) :
    Generates (prod p q) (μ.prod ν).toFiniteLaw := by
  rw [PositiveRationalLaw.toFiniteLaw_prod]
  exact generates_prod hp hq

/-- Coordinate recursion, with no enumeration of `Fin n → A`. -/
def iid (p : Program A) : (n : ℕ) → Program (Fin n → A)
  | 0 => .pure finZeroElim
  | n + 1 => Program.bind p (fun a => Program.map (Fin.cons a) (iid p n))

theorem generates_iid {p : Program A} {μ : FiniteLaw A}
    (hp : Generates p μ) (n : ℕ) : Generates (iid p n) (μ.iid n) := by
  classical
  unfold Generates at hp ⊢
  induction n with
  | zero =>
      intro f
      simp only [iid, Program.expect_pure, FiniteLaw.iid, Finset.univ_eq_empty,
        Finset.prod_empty, one_mul]
      rw [Fintype.sum_unique]
      congr 1
  | succ n ih =>
      intro f
      simp only [iid, Program.expect_bind, Program.expect_map]
      rw [hp]
      simp_rw [ih]
      simp only [Finset.mul_sum]
      rw [← Fintype.sum_prod_type (f := fun x : A × (Fin n → A) =>
        μ.weight x.1 * ((μ.iid n).weight x.2 * f (Fin.cons x.1 x.2)))]
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => A))
      intro x
      simp only [FiniteLaw.iid, Fin.consEquiv, Equiv.coe_fn_mk,
        Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring

theorem generates_rational_iid {p : Program A} {μ : PositiveRationalLaw A}
    (hp : Generates p μ.toFiniteLaw) (n : ℕ) :
    Generates (iid p n) (μ.iid n).toFiniteLaw := by
  rw [PositiveRationalLaw.toFiniteLaw_iid]
  exact generates_iid hp n

omit [Fintype A] [Fintype B] in
theorem maxDraws_prod_le (p : Program A) (q : Program B) :
    Program.maxDraws (prod p q) ≤ Program.maxDraws p + Program.maxDraws q := by
  apply Program.maxDraws_bind_le
  intro a
  simp only [Program.maxDraws_map, le_refl]

omit [Fintype A] in
theorem maxDraws_iid_le (p : Program A) (n : ℕ) :
    Program.maxDraws (iid p n) ≤ n * Program.maxDraws p := by
  induction n with
  | zero => simp [iid]
  | succ n ih =>
      rw [iid]
      calc
        _ ≤ Program.maxDraws p + n * Program.maxDraws p := by
          apply Program.maxDraws_bind_le
          intro a
          rw [Program.maxDraws_map]
          exact ih
        _ = (n + 1) * Program.maxDraws p := by ring

omit [Fintype A] [Fintype B] in
theorem bounded_prod {p : Program A} {q : Program B} {N M : ℕ}
    (hp : Program.IsBounded p N) (hq : Program.IsBounded q M) :
    Program.IsBounded (prod p q) (N + M) :=
  (maxDraws_prod_le p q).trans (Nat.add_le_add hp hq)

omit [Fintype A] in
theorem bounded_iid {p : Program A} {N : ℕ}
    (hp : Program.IsBounded p N) (n : ℕ) :
    Program.IsBounded (iid p n) (n * N) :=
  (maxDraws_iid_le p n).trans (Nat.mul_le_mul_left n hp)

omit [Fintype A] [Fintype B] in
theorem maxAlphabet_prod_le (p : Program A) (q : Program B) :
    Program.maxAlphabet (prod p q) ≤
      max (Program.maxAlphabet p) (Program.maxAlphabet q) := by
  apply Program.maxAlphabet_bind_le
  intro a
  simp only [Program.maxAlphabet_map, le_refl]

omit [Fintype A] in
theorem maxAlphabet_iid_le (p : Program A) (n : ℕ) :
    Program.maxAlphabet (iid p n) ≤ Program.maxAlphabet p := by
  induction n with
  | zero =>
      simpa only [iid, Program.maxAlphabet_pure] using Program.maxAlphabet_pos p
  | succ n ih =>
      rw [iid]
      calc
        _ ≤ max (Program.maxAlphabet p) (Program.maxAlphabet p) := by
          apply Program.maxAlphabet_bind_le
          intro a
          rw [Program.maxAlphabet_map]
          exact ih
        _ = Program.maxAlphabet p := max_self _

#print axioms generates_map_of_fibres
#print axioms generates_relabel
#print axioms generates_uniform_equiv
#print axioms generates_prod
#print axioms generates_iid
#print axioms maxDraws_iid_le
#print axioms maxAlphabet_iid_le

end Paper2.RecursiveSamplingLaws
