import CurrentAdditive.ExplicitSeedLabels
import CurrentAdditive.FiniteFieldVectorSeed
import CurrentAdditive.DotSemantics

/-! A generic coordinate bridge for the executable dot word. -/

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldAdapter

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

theorem dot_eq_vectorWord_of_coords (d n : ℕ)
    (basis : Module.Basis (Fin d) (ZMod 2) F)
    (x : Fin (2 ^ d)) (y : F) (z : ℕ) (j : Fin n)
    (hcoord : ∀ i : Fin d,
      basis.equivFun (y ^ (j : ℕ)) i = boolCoeff (z.testBit i)) :
    dot d x z = vectorWord basis (xBits d x, y) j := by
  change dot d x z = word (basis.dualBasis.equivFun.symm (xBits d x), y) j
  have hsum : (∑ i : Fin d,
        boolCoeff (x.val.testBit i) * boolCoeff (z.testBit i)) =
      (∑ i : Fin d, xBits d x i * basis.equivFun (y ^ (j : ℕ)) i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [xBits, hcoord]
  calc
    dot d x z = decide ((∑ i : Fin d,
        boolCoeff (x.val.testBit i) * boolCoeff (z.testBit i)) = 1) :=
      dot_eq_decide d x z
    _ = decide ((∑ i : Fin d,
        xBits d x i * basis.equivFun (y ^ (j : ℕ)) i) = 1) :=
      congrArg (fun v : ZMod 2 => decide (v = 1)) hsum
    _ = word (basis.dualBasis.equivFun.symm (xBits d x), y) j := by
      change decide ((∑ i : Fin d,
          xBits d x i * basis.equivFun (y ^ (j : ℕ)) i) = 1) =
        decide (((basis.dualBasis.equivFun.symm (xBits d x))
          (y ^ (j : ℕ))) = 1)
      have hdot :
          (basis.dualBasis.equivFun.symm (xBits d x)) (y ^ (j : ℕ)) =
            ∑ i : Fin d, xBits d x i * basis.equivFun (y ^ (j : ℕ)) i := by
        let φ := basis.dualBasis.equivFun.symm (xBits d x)
        calc
          φ (y ^ (j : ℕ)) =
              φ (∑ i, basis.repr (y ^ (j : ℕ)) i • basis i) := by
                rw [basis.sum_repr]
          _ = ∑ i : Fin d, xBits d x i *
              basis.equivFun (y ^ (j : ℕ)) i := by
                simp [Module.Basis.equivFun_apply, φ]
      exact congrArg (fun v : ZMod 2 => decide (v = 1)) hdot.symm

#print axioms CurrentAdditive.SmallBias.dot_eq_vectorWord_of_coords

end CurrentAdditive.SmallBias
