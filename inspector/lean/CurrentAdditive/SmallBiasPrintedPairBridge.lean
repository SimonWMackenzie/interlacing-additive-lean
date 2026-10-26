import CurrentAdditive.SmallBiasPairLabels
import CurrentAdditive.BitPrinter

/-!
# Pointwise bridge from executable printer bits to the v27 matrix

The only residual premise here is an explicit bit equality for each
physical seed pair and position. The constructor's quotient-field
operation and coordinate lemmas are intended to discharge that equality.
No small-bias or protocol conclusion is supplied as a premise.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The printer's row-major pair label, flattened to `Fin(R²)`. -/
def printerPairLabel (d : ℕ) :
    Fin (2 ^ d) × Fin (2 ^ d) ≃ Fin ((2 ^ d) ^ 2) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_two]))

/-- The literal executable bit array interpreted at a flattened pair
label and a payload coordinate. -/
def printedPairFieldWord (b t d modulus : ℕ) :
    Fin ((2 ^ d) ^ 2) →
      Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1) → Bool :=
  fun ℓ j =>
    let xy := (printerPairLabel d).symm ℓ
    BitPrinter.bit d modulus xy.1.val xy.2.val (finProdFinEquiv j).val

/-- Pointwise quotient semantics identifies the physical bit array with
the small-biased pair-labelled field word. -/
theorem printedPairFieldWord_eq_explicitPairFieldWord
    (b t d modulus : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hbit : ∀ x y j,
      BitPrinter.bit d modulus (x : Fin (2 ^ d)).val
          (y : Fin (2 ^ d)).val (j : Fin (2 ^ b * (2 ^ t * 2 ^ t + 1))).val =
        vectorWord basis (xDecode x, yDecode y) j) :
    printedPairFieldWord b t d modulus =
      explicitPairFieldWord b t d basis xDecode yDecode := by
  funext ℓ j
  let xy := (printerPairLabel d).symm ℓ
  have hseed :
      (explicitPairVectorSeeds d xDecode yDecode).symm ℓ =
        (xDecode xy.1, yDecode xy.2) := by
    simp [explicitPairVectorSeeds, printerPairLabel, xy]
  change BitPrinter.bit d modulus xy.1.val xy.2.val
      (finProdFinEquiv j).val =
      vectorWord basis
        ((explicitPairVectorSeeds d xDecode yDecode).symm ℓ)
        (finProdFinEquiv j)
  rw [hseed]
  exact hbit xy.1 xy.2 (finProdFinEquiv j)

/-- The executable bit function inherits the actual v27 matrix NO gap
from exact pointwise quotient semantics. This is a direct consumer for
the constructor's `hbit` theorem. -/
theorem lower_bound_printed_pair_field_matrix
    {V E : Type*} [Fintype V]
    (b t d modulus : ℕ) (ht : 4 ≤ t)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (hcard : Fintype.card F = 2 ^ d)
    (xDecode : Fin (2 ^ d) ≃ (Fin d → ZMod 2))
    (yDecode : Fin (2 ^ d) ≃ F)
    (hR : ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
      (2 ^ d : ℚ))
    (hbit : ∀ x y j,
      BitPrinter.bit d modulus (x : Fin (2 ^ d)).val
          (y : Fin (2 ^ d)).val (j : Fin (2 ^ b * (2 ^ t * 2 ^ t + 1))).val =
        vectorWord basis (xDecode x, yDecode y) j)
    (edges : E → Fin (2 ^ t * 2 ^ t) ↪ V)
    (index : E ↪ Fin (2 ^ b))
    (hno : ∀ colour : V → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (2 * b + 4 * t + 2) + 2 * t - 6 ≤
      Dalt .alice (matrix (placeEdges edges index)
        (fullSelector (2 ^ (t - 1)) (2 ^ b))
        (printedPairFieldWord b t d modulus)) := by
  rw [printedPairFieldWord_eq_explicitPairFieldWord
    b t d modulus basis xDecode yDecode hbit]
  exact lower_bound_explicit_pair_field_matrix b t d ht basis hcard
    xDecode yDecode hR edges index hno

#print axioms CurrentAdditive.SmallBias.printedPairFieldWord_eq_explicitPairFieldWord
#print axioms CurrentAdditive.SmallBias.lower_bound_printed_pair_field_matrix

end CurrentAdditive.SmallBias
