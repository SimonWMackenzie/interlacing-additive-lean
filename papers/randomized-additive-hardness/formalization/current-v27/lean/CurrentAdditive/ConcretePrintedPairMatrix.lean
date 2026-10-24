import CurrentAdditive.PrintedFieldWordChecked
import CurrentAdditive.SmallBiasPrintedPairBridge

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open CurrentAdditive.SmallBias
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

theorem lower_bound_concrete_printed_pair_matrix
    {V E : Type*} [Fintype V]
    (b t d modulus : ℕ) (ht : 4 ≤ t)
    (hd : 0 < d)
    (hmodulus : modulus < 2 ^ (d + 1))
    (htop : modulus.testBit d = true)
    (hmonic : (polynomial (d + 1) modulus).Monic)
    (hdegree : (polynomial (d + 1) modulus).natDegree = d)
    [Fact (Irreducible (polynomial (d + 1) modulus))]
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ))
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)) := by
  letI : Fintype (QuotientField d modulus) :=
    quotientFintype d modulus hmonic hdegree
  letI : CharP (QuotientField d modulus) 2 :=
    quotientCharP d modulus (Fact.out)
  have hbit (x y : Fin (2 ^ d))
      (j : Fin (2 ^ b * (2 ^ t * 2 ^ t + 1))) :
      CurrentAdditive.FiniteFieldConstructor.BitPrinter.bit d modulus
          x.val y.val j.val =
        CurrentAdditive.FiniteFieldAdapter.vectorWord
          (fieldBasis d modulus hmonic hdegree)
          (xDecode d x, quotientCodeEquiv d modulus hmonic hdegree y) j :=
    printed_bit_eq_vectorWord d modulus _ hd hmodulus htop hmonic hdegree x y j
  exact lower_bound_printed_pair_field_matrix b t d modulus ht
    (fieldBasis d modulus hmonic hdegree)
    (quotient_card d modulus hmonic hdegree)
    (xDecode d) (quotientCodeEquiv d modulus hmonic hdegree)
    hR hbit edges index hno

#print axioms lower_bound_concrete_printed_pair_matrix

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
