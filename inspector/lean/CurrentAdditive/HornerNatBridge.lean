import CurrentAdditive.HornerQuotientSemantics
import CurrentAdditive.ExplicitSeedLabels
import CurrentAdditive.QuotientMulSemantics
import CurrentAdditive.QuotientCodeEquiv

/-!
Connect the old arbitrary-modulus physical Horner controller to the new
Nat-bit quotient representation. This is a private semantic bridge; operand
preparation and the streaming loop still need physical programs.
-/

namespace CurrentAdditive.FiniteFieldMachine.HornerNatBridge

open Polynomial
open EthInapproximability.CurrentPaper
open ExecutableSmallBiasSampler SamplerMachine SamplerMachineProduct
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldMachine.HornerQuotientSemantics

def lowerWord (d code : ℕ) : BinaryWord d :=
  fun i => boolCoeff (code.testBit i)

theorem monicPolynomial_eq (d modulus : ℕ)
    (htop : modulus.testBit d = true) :
    monicPolynomial d (lowerWord d modulus) = polynomial (d + 1) modulus := by
  ext j
  rw [monicPolynomial_coeff, coeff_polynomial]
  by_cases hj : j < d
  · have hj2 : j < d + 1 := by omega
    simp only [monicCoeff, dif_pos hj, if_pos hj2, lowerWord, boolCoeff]
  · by_cases heq : j = d
    · subst j
      simp [monicCoeff, htop]
    · have hj' : d + 1 ≤ j := by omega
      have hn : ¬j < d + 1 := by omega
      simp only [monicCoeff, dif_neg hj, if_neg heq, if_neg hn]

theorem wordPolynomial_eq (d : ℕ) (x : Fin (2 ^ d)) :
    (∑ i : Fin d, Polynomial.monomial i.val (xBits d x i)) =
      polynomial d x.val := by
  unfold polynomial
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt : i < d := Finset.mem_range.mp hi
  simp only [xBits, boolCoeff, dif_pos hlt, Polynomial.C_mul_X_pow_eq_monomial]

theorem evalAt_xBits (d : ℕ) (c : BinaryWord d) (x : Fin (2 ^ d)) :
    evalAt c (xBits d x) =
      AdjoinRoot.mk (monicPolynomial d c) (polynomial d x.val) := by
  rw [← wordPolynomial_eq d x]
  simp only [evalAt, evalWordAt_apply, map_sum]
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

/-- A binary word returned by the existing physical Horner controller is
the same residue as the literal Nat-bit `BitPrinter.mul`, for any monic
degree-`d` candidate. The `Fin` conversion occurs only in the proof of
semantic equality; the machine stores the d bits directly. -/
theorem horner_eq_bitPrinter_mul (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (a b : Fin (2 ^ d)) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ((encodeWord (xBits d b)).reverse.foldl
      (hornerStep c (xBits d a)) (fun _ => 0)) =
        lowerWord d (mul d modulus a.val b.val) := by
  intro modulus c
  let w : BinaryWord d :=
    (encodeWord (xBits d b)).reverse.foldl
      (hornerStep c (xBits d a)) (fun _ => 0)
  let label : Fin (2 ^ d) := (xDecode d).symm w
  have hw : xBits d label = w := (xDecode d).apply_symm_apply w
  have htop := monicBits_topBit d tail htail
  have hmodulus := monicBits_lt d tail htail
  have hmonic := monicBits_monic d tail htail
  have hdegree := monicBits_degree d tail htail
  have hmul := mul_quotient d modulus a.val b.val hd hmodulus htop b.isLt
  have hcode := eval_horner_mul c (xBits d a) (xBits d b)
  change evalAt c w = evalAt c (xBits d a) * evalAt c (xBits d b) at hcode
  rw [← hw, evalAt_xBits d c label,
    evalAt_xBits d c a,
    evalAt_xBits d c b] at hcode
  dsimp only [c] at hcode
  rw [monicPolynomial_eq d modulus htop] at hcode
  have hout : mul d modulus a.val b.val < 2 ^ d :=
    mul_lt d modulus a.val b.val hmodulus htop b.isLt
  have hlabel : label = ⟨mul d modulus a.val b.val, hout⟩ :=
    (quotientCode_injective d modulus hmonic hdegree) (hcode.trans hmul.symm)
  change w = lowerWord d (mul d modulus a.val b.val)
  calc
    w = xBits d label := hw.symm
    _ = xBits d ⟨mul d modulus a.val b.val, hout⟩ := congrArg (xBits d) hlabel
    _ = lowerWord d (mul d modulus a.val b.val) := rfl

/-- Actual physical multiplication run for the first-search candidate format.
The reversed multiplier and empty scratch banks are the explicit entry
condition; the outer streaming controller must prepare them and charge that
preparation. -/
theorem run_bitPrinter_mul (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (a b : Fin (2 ^ d)) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ∃ t ≤ d * (4 * d + 5) + 1,
      SamplerMachineProduct.run t
        (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
          (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
          (encodeWord (xBits d a)) [] [] (encodeWord c)
          (encodeWord (xBits d b)).reverse) =
      SamplerMachineProduct.cfg none SamplerMachineProduct.initial
        (encodeWord (lowerWord d (mul d modulus a.val b.val)))
        (encodeWord (xBits d a)) [] [] (encodeWord c) [] := by
  intro modulus c
  obtain ⟨t, ht, hr⟩ := SamplerMachineProduct.run_horner c SamplerMachineProduct.initial
    (fun _ : Fin d => 0) (xBits d a) (encodeWord (xBits d b)).reverse
  simp only [List.length_reverse, encodeWord_length] at ht
  rw [horner_eq_bitPrinter_mul d tail htail hd a b] at hr
  exact ⟨t, ht, hr⟩

#print axioms monicPolynomial_eq
#print axioms evalAt_xBits
#print axioms horner_eq_bitPrinter_mul
#print axioms run_bitPrinter_mul

end CurrentAdditive.FiniteFieldMachine.HornerNatBridge
