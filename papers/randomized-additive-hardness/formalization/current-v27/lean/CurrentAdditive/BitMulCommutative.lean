import CurrentAdditive.QuotientCodeEquiv

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

/-- Literal fixed-width modular bit multiplication is commutative for a
monic degree-`d` modulus. Irreducibility is unnecessary. -/
theorem bit_mul_comm (d modulus a b : ℕ) (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    (ha : a < 2 ^ d) (hb : b < 2 ^ d) :
    mul d modulus a b = mul d modulus b a := by
  let u : Fin (2 ^ d) :=
    ⟨mul d modulus a b, mul_lt d modulus a b hmodulus htop hb⟩
  let v : Fin (2 ^ d) :=
    ⟨mul d modulus b a, mul_lt d modulus b a hmodulus htop ha⟩
  have hquot :
      AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d u) =
        AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d v) := by
    change AdjoinRoot.mk (polynomial (d + 1) modulus)
        (polynomial d (mul d modulus a b)) =
      AdjoinRoot.mk (polynomial (d + 1) modulus)
        (polynomial d (mul d modulus b a))
    calc
      _ = AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d a) *
          AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d b) :=
        mul_quotient d modulus a b hd hmodulus htop hb
      _ = AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d b) *
          AdjoinRoot.mk (polynomial (d + 1) modulus) (polynomial d a) :=
        mul_comm _ _
      _ = _ := (mul_quotient d modulus b a hd hmodulus htop ha).symm
  have huv : u = v := quotientCode_injective d modulus hmonic hdegree hquot
  exact congrArg Fin.val huv

theorem bit_mul_comm_monicBits (d tail a b : ℕ) (hd : 0 < d)
    (htail : tail < 2 ^ d) (ha : a < 2 ^ d) (hb : b < 2 ^ d) :
    mul d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) a b =
      mul d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) b a := by
  exact bit_mul_comm d _ a b hd
    (monicBits_lt d tail htail)
    (monicBits_topBit d tail htail)
    (monicBits_monic d tail htail)
    (monicBits_degree d tail htail) ha hb

#print axioms bit_mul_comm
#print axioms bit_mul_comm_monicBits

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
