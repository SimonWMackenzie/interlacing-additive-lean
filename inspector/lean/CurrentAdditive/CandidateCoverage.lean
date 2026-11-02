import CurrentAdditive.DivisionTest

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

noncomputable def lowEncoding (e : ℕ) (tail : Fin (2 ^ e)) :
    Polynomial.degreeLT (ZMod 2) e :=
  ⟨polynomial e tail, Polynomial.mem_degreeLT.mpr (polynomial_degree_lt e tail)⟩

theorem lowEncoding_injective (e : ℕ) : Function.Injective (lowEncoding e) := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < e
  · have hp : polynomial e a = polynomial e b := congrArg Subtype.val hab
    have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff j) hp
    change (polynomial e a).coeff j = (polynomial e b).coeff j at hc
    rw [coeff_polynomial, coeff_polynomial] at hc
    simp only [hj, ↓reduceIte] at hc
    cases ha : a.val.testBit j <;> cases hb : b.val.testBit j <;> simp_all
  · have hpow : 2 ^ e ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (b.isLt.trans_le hpow)]

theorem lowEncoding_surjective (e : ℕ) : Function.Surjective (lowEncoding e) := by
  letI : Fintype (Polynomial.degreeLT (ZMod 2) e) :=
    Fintype.ofEquiv (Fin e → ZMod 2) (Polynomial.degreeLTEquiv (ZMod 2) e).toEquiv.symm
  have hcard : Fintype.card (Fin (2 ^ e)) =
      Fintype.card (Polynomial.degreeLT (ZMod 2) e) := by
    rw [Fintype.card_fin, Fintype.card_congr (Polynomial.degreeLTEquiv (ZMod 2) e).toEquiv]
    simp [Fintype.card_fun, ZMod.card]
  let equiv : Fin (2 ^ e) ≃ Polynomial.degreeLT (ZMod 2) e :=
    Fintype.equivOfCardEq hcard
  exact (Finite.injective_iff_surjective_of_equiv equiv).mp (lowEncoding_injective e)

theorem exists_lowEncoding (e : ℕ) (p : Polynomial (ZMod 2))
    (hp : p.degree < e) :
    ∃ tail : Fin (2 ^ e), polynomial e tail = p := by
  obtain ⟨tail, htail⟩ := lowEncoding_surjective e ⟨p, Polynomial.mem_degreeLT.mpr hp⟩
  exact ⟨tail, congrArg Subtype.val htail⟩

#print axioms lowEncoding_surjective
#print axioms exists_lowEncoding

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
