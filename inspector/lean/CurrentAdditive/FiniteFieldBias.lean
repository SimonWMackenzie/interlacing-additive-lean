import Mathlib

/-!
The finite algebraic part of `yao:finite-field-list` and `yao:trace-list` in
the selected v27 manuscript.  This file does not formalize field construction
or the bit-operation bound for printing the labels.
-/

namespace CurrentAdditive

open Polynomial

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

private noncomputable instance fieldDecidableEq : DecidableEq F := Classical.decEq F

/-- The polynomial of a selected, nonempty set of coordinate positions. -/
def parityPolynomial {n : ℕ} (I : Finset (Fin n)) : F[X] :=
  ∑ j ∈ I, X ^ (j : ℕ)

theorem parityPolynomial_coeff {n : ℕ} (I : Finset (Fin n)) (k : Fin n) :
    (parityPolynomial (F := F) I).coeff k = if k ∈ I then 1 else 0 := by
  classical
  rw [parityPolynomial, Polynomial.finsetSum_coeff]
  have hcast (j : Fin n) : (k : ℕ) = (j : ℕ) ↔ k = j := Fin.val_inj
  simp only [Polynomial.coeff_X_pow, hcast]
  rw [Finset.sum_ite_eq]

theorem parityPolynomial_ne_zero {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty) :
    parityPolynomial (F := F) I ≠ 0 := by
  obtain ⟨k, hk⟩ := hI
  intro h
  have hcoeff := congrArg (fun p : F[X] => p.coeff k) h
  simp [parityPolynomial_coeff, hk] at hcoeff

theorem parityPolynomial_natDegree_le {n : ℕ} (hn : 1 ≤ n) (I : Finset (Fin n)) :
    (parityPolynomial (F := F) I).natDegree ≤ n - 1 := by
  classical
  unfold parityPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  calc
    (X ^ (j : ℕ) : F[X]).natDegree ≤ (j : ℕ) := Polynomial.natDegree_X_pow_le _
    _ ≤ n - 1 := by omega

/-- The sign used to measure parity bias. -/
def bitSign (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

theorem bitSign_add_one (b : ZMod 2) : bitSign (b + 1) = -bitSign b := by
  fin_cases b <;> decide

private instance dualFinite : Finite (Module.Dual (ZMod 2) F) :=
  Finite.of_injective (fun φ : Module.Dual (ZMod 2) F => (φ : F → ZMod 2))
    (by intro φ ψ h; ext z; exact congrFun h z)

noncomputable instance dualFintype : Fintype (Module.Dual (ZMod 2) F) :=
  Fintype.ofFinite _

theorem dual_card_eq_field_card :
    Fintype.card (Module.Dual (ZMod 2) F) = Fintype.card F := by
  let b := Module.Free.chooseBasis (ZMod 2) F
  let e := b.dualBasis.equivFun.trans b.equivFun.symm
  exact Fintype.card_congr e.toEquiv

theorem seed_card_eq_square :
    Fintype.card (Module.Dual (ZMod 2) F × F) = (Fintype.card F) ^ 2 := by
  rw [Fintype.card_prod, dual_card_eq_field_card]
  ring

/-- A binary vector labels the corresponding linear functional by the
dot product with field coordinates in the chosen basis. -/
theorem basisFunctional_eq_dot {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (ZMod 2) F) (x : ι → ZMod 2) (z : F) :
    (b.dualBasis.equivFun.symm x) z =
      ∑ i, x i * b.equivFun z i := by
  let φ := b.dualBasis.equivFun.symm x
  calc
    φ z = φ (∑ i, b.repr z i • b i) := by rw [b.sum_repr]
    _ = ∑ i, x i * b.equivFun z i := by
      simp [map_sum, map_smul, b.dualBasis_equivFun, Module.Basis.equivFun_apply,
        φ, mul_comm]

theorem dualSign_sum_zero (z : F) (hz : z ≠ 0) :
    ∑ φ : Module.Dual (ZMod 2) F, bitSign (φ z) = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hz
  apply Finset.sum_involution (s := Finset.univ)
    (g := fun φ (_ : φ ∈ Finset.univ) => φ + ψ)
  · intro φ hφ
    rw [LinearMap.add_apply, hψ, bitSign_add_one]
    omega
  · intro φ hφ hs
    intro heq
    have hzero : ψ = 0 := add_left_cancel (show φ + ψ = φ + 0 by simpa using heq)
    simp [hzero] at hψ
  · intro φ hφ
    simp
  · intro φ hφ
    simpa [add_assoc, ZModModule.add_self ψ]

theorem dualSign_sum (z : F) :
    ∑ φ : Module.Dual (ZMod 2) F, bitSign (φ z) =
      if z = 0 then (Fintype.card (Module.Dual (ZMod 2) F) : ℤ) else 0 := by
  classical
  by_cases hz : z = 0
  · subst z
    simp [bitSign]
  · simp [hz, dualSign_sum_zero z hz]

/-- The parity bit printed at a coordinate subset by a labelled seed. -/
def parityBit {n : ℕ} (I : Finset (Fin n))
    (φ : Module.Dual (ZMod 2) F) (y : F) : ZMod 2 :=
  ∑ j ∈ I, φ (y ^ (j : ℕ))

theorem parityBit_eq_eval {n : ℕ} (I : Finset (Fin n))
    (φ : Module.Dual (ZMod 2) F) (y : F) :
    parityBit I φ y = φ ((parityPolynomial (F := F) I).eval y) := by
  change (∑ j ∈ I, φ (y ^ (j : ℕ))) = φ ((∑ j ∈ I, X ^ (j : ℕ)).eval y)
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_X_pow, map_sum]

theorem basisPowerWord_eq_parityBit {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (ZMod 2) F) {n : ℕ}
    (I : Finset (Fin n)) (x : ι → ZMod 2) (y : F) :
    (∑ j ∈ I, ∑ i, x i * b.equivFun (y ^ (j : ℕ)) i) =
      parityBit I (b.dualBasis.equivFun.symm x) y := by
  simp only [parityBit, basisFunctional_eq_dot]

theorem parityBit_dualSign_sum {n : ℕ} (I : Finset (Fin n)) (y : F) :
    ∑ φ : Module.Dual (ZMod 2) F, bitSign (parityBit I φ y) =
      if (parityPolynomial (F := F) I).eval y = 0 then
        (Fintype.card (Module.Dual (ZMod 2) F) : ℤ) else 0 := by
  simp_rw [parityBit_eq_eval]
  exact dualSign_sum _

/-- The signed bias numerator is exactly the number of polynomial roots,
times the number of binary linear functionals. -/
theorem paritySignedSum_eq {n : ℕ} (I : Finset (Fin n)) :
    (∑ y : F, ∑ φ : Module.Dual (ZMod 2) F, bitSign (parityBit I φ y)) =
      ((Finset.univ.filter fun y : F =>
        (parityPolynomial (F := F) I).eval y = 0).card : ℤ) *
        (Fintype.card (Module.Dual (ZMod 2) F) : ℤ) := by
  classical
  simp_rw [parityBit_dualSign_sum]
  simp [Finset.sum_ite]

theorem parityBadSeeds_le {n : ℕ} (hn : 1 ≤ n)
    (I : Finset (Fin n)) (hI : I.Nonempty) :
    (Finset.univ.filter fun y : F =>
      (parityPolynomial (F := F) I).eval y = 0).card ≤ n - 1 := by
  classical
  let P := parityPolynomial (F := F) I
  have hP : P ≠ 0 := parityPolynomial_ne_zero I hI
  have hsubset : (Finset.univ.filter fun y : F => P.eval y = 0).val ⊆ P.roots := by
    intro y hy
    exact (Polynomial.mem_roots hP).2 (Finset.mem_filter.mp hy).2
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans
    (parityPolynomial_natDegree_le hn I)

/-- The signed mean of parity over every labelled pair `(φ,y)`. -/
def paritySignedAverage {n : ℕ} (I : Finset (Fin n)) : ℚ :=
  ((∑ y : F, ∑ φ : Module.Dual (ZMod 2) F,
      bitSign (parityBit I φ y) : ℤ) : ℚ) /
    ((Fintype.card F : ℚ) *
      (Fintype.card (Module.Dual (ZMod 2) F) : ℚ))

theorem paritySignedAverage_eq {n : ℕ} (I : Finset (Fin n)) :
    paritySignedAverage (F := F) I =
      ((Finset.univ.filter fun y : F =>
        (parityPolynomial (F := F) I).eval y = 0).card : ℚ) /
        (Fintype.card F : ℚ) := by
  unfold paritySignedAverage
  rw [paritySignedSum_eq]
  have hD : (Fintype.card (Module.Dual (ZMod 2) F) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The exact finite-field bias claim: the signed parity mean of every
nonempty coordinate set has absolute value at most `ε`. -/
theorem finiteFieldPowering_epsilonBias {n : ℕ} (hn : 1 ≤ n)
    (ε : ℚ) (hε : 0 < ε)
    (hR : (n : ℚ) / ε ≤ (Fintype.card F : ℚ))
    (I : Finset (Fin n)) (hI : I.Nonempty) :
    |paritySignedAverage (F := F) I| ≤ ε := by
  have hEq := paritySignedAverage_eq (F := F) I
  have hBad := parityBadSeeds_le (F := F) hn I hI
  have hBadQ :
      ((Finset.univ.filter fun y : F =>
        (parityPolynomial (F := F) I).eval y = 0).card : ℚ) ≤
        ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hBad
  have hSub : ((n - 1 : ℕ) : ℚ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have hCard : (0 : ℚ) < Fintype.card F := by positivity
  have hNumer : (0 : ℚ) ≤
      ((Finset.univ.filter fun y : F =>
        (parityPolynomial (F := F) I).eval y = 0).card : ℚ) := by positivity
  rw [hEq, abs_of_nonneg (div_nonneg hNumer hCard.le)]
  apply (div_le_iff₀ hCard).2
  have hN : (n : ℚ) ≤ (Fintype.card F : ℚ) * ε :=
    (div_le_iff₀ hε).1 hR
  nlinarith

#print axioms parityPolynomial_ne_zero
#print axioms dualSign_sum_zero
#print axioms seed_card_eq_square
#print axioms finiteFieldPowering_epsilonBias

end

end CurrentAdditive
