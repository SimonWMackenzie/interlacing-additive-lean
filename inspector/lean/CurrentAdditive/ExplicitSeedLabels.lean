import CurrentAdditive.ExplicitQuotientBasis

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

def xBits (d : ℕ) (x : Fin (2 ^ d)) : Fin d → ZMod 2 :=
  fun i => boolCoeff (x.val.testBit i)

theorem xBits_injective (d : ℕ) : Function.Injective (xBits d) := by
  intro x y hxy
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d
  · have hcoord := congrFun hxy ⟨j, hj⟩
    change boolCoeff (x.val.testBit j) = boolCoeff (y.val.testBit j) at hcoord
    cases hx : x.val.testBit j <;> cases hy : y.val.testBit j <;>
      simp_all [boolCoeff]
  · have hp : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (y.isLt.trans_le hp)]

theorem xBits_surjective (d : ℕ) : Function.Surjective (xBits d) := by
  have hcard : Fintype.card (Fin (2 ^ d)) = Fintype.card (Fin d → ZMod 2) := by
    simp [ZMod.card]
  let equiv : Fin (2 ^ d) ≃ (Fin d → ZMod 2) := Fintype.equivOfCardEq hcard
  exact (Finite.injective_iff_surjective_of_equiv equiv).mp (xBits_injective d)

noncomputable def xDecode (d : ℕ) : Fin (2 ^ d) ≃ (Fin d → ZMod 2) :=
  Equiv.ofBijective (xBits d) ⟨xBits_injective d, xBits_surjective d⟩

#print axioms xBits_injective
#print axioms xDecode

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
