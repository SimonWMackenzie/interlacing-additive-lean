import EthInapproximability.CurrentPaper.SamplerMachineShift
import EthInapproximability.CurrentPaper.SamplerHorner

/-!
# Non-circular factor-product arithmetic for polynomial search

Source: locked v8 `E-exact-details.tex`, monic binary factor enumeration in
`lem:exact-families`. The fixed shift-and-add operation is interpreted in the
quotient by an arbitrary monic polynomial. No irreducibility, chosen polynomial,
or field construction is needed. In width `n+1`, the zero-modulus Horner fold
therefore computes every coefficient of the two trial monic factors.

These are semantic identities, not machine-runtime assertions.
-/

namespace EthInapproximability.CurrentPaper.SamplerPolynomialProduct

open scoped BigOperators Polynomial
open SamplerMachine ExecutableSmallBiasSampler SamplerMachineShift SamplerHorner

abbrev QuotientWord (n : ℕ) (c : BinaryWord n) := AdjoinRoot (monicPolynomial n c)

noncomputable def coefficientEval {n : ℕ} (c : BinaryWord n) :
    BinaryWord n →ₗ[ZMod 2] QuotientWord n c :=
  evalWordAt (AdjoinRoot.root (monicPolynomial n c))

noncomputable def coefficientBasis {n : ℕ} (c : BinaryWord n) :
    Module.Basis (Fin n) (ZMod 2) (QuotientWord n c) :=
  (AdjoinRoot.powerBasis' (monicPolynomial_monic n c)).basis.reindex
    (finCongr (monicPolynomial_degree n c))

theorem coefficientBasis_apply {n : ℕ} (c : BinaryWord n) (i : Fin n) :
    coefficientBasis c i = AdjoinRoot.root (monicPolynomial n c) ^ i.val := by
  simp only [coefficientBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem coefficientEval_injective {n : ℕ} (c : BinaryWord n) :
    Function.Injective (coefficientEval c) := by
  have heq : ((coefficientBasis c).equivFun.symm : BinaryWord n → QuotientWord n c) =
      coefficientEval c := by
    funext u
    rw [Module.Basis.equivFun_symm_apply]
    simp only [coefficientBasis_apply, coefficientEval, evalWordAt,
      Fintype.linearCombination_apply]
  rw [← heq]
  exact (coefficientBasis c).equivFun.symm.injective

theorem root_relation {n : ℕ} (c : BinaryWord n) :
    AdjoinRoot.root (monicPolynomial n c) ^ n + coefficientEval c c = 0 := by
  have h : (AdjoinRoot.mk (monicPolynomial n c)) (monicPolynomial n c) = 0 :=
    AdjoinRoot.mk_self
  change (AdjoinRoot.mk (monicPolynomial n c))
    (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.monomial i.val (c i)) = 0 at h
  rw [map_add, map_pow, AdjoinRoot.mk_X, map_sum] at h
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X] at h
  simpa only [coefficientEval, evalWordAt_apply, AdjoinRoot.algebraMap_eq] using h

theorem coefficientEval_shiftWith {n : ℕ} (c u : BinaryWord n) :
    coefficientEval c (shiftWith c u) =
      AdjoinRoot.root (monicPolynomial n c) * coefficientEval c u := by
  cases n with
  | zero => simp [shiftWith, coefficientEval, evalWordAt_apply]
  | succ k =>
      have hs : shiftWith c u =
          (Fin.cons 0 (fun j : Fin k => u j.castSucc) : BinaryWord (k + 1)) -
            wordScale (u (Fin.last k)) c := rfl
      rw [hs]
      simp only [coefficientEval]
      rw [map_sub, evalWordAt_scale, evalWordAt_rawShift]
      have hroot := root_relation c
      change AdjoinRoot.root (monicPolynomial (k + 1) c) ^ (k + 1) +
        evalWordAt (AdjoinRoot.root (monicPolynomial (k + 1) c)) c = 0 at hroot
      linear_combination -algebraMap (ZMod 2) (QuotientWord (k + 1) c)
        (u (Fin.last k)) * hroot

/-- The controller's high-to-low fold with arbitrary modulus coefficients. -/
def hornerWith {n : ℕ} (c u : BinaryWord n) (bs : List Bool) (a : BinaryWord n) :
    BinaryWord n :=
  bs.foldl (fun a b => wordAdd (shiftWith c a) (wordScale (decodeBit b) u)) a

theorem coefficientEval_hornerStep {n : ℕ} (c u a : BinaryWord n) (b : Bool) :
    coefficientEval c (wordAdd (shiftWith c a) (wordScale (decodeBit b) u)) =
      AdjoinRoot.root (monicPolynomial n c) * coefficientEval c a +
        algebraMap (ZMod 2) (QuotientWord n c) (decodeBit b) * coefficientEval c u := by
  change coefficientEval c (shiftWith c a + wordScale (decodeBit b) u) = _
  rw [map_add, coefficientEval_shiftWith]
  congr 1
  exact evalWordAt_scale _ _ _

theorem coefficientEval_hornerReverse {n : ℕ} (c u : BinaryWord n) (bs : List Bool)
    (a : BinaryWord n) :
    coefficientEval c (hornerWith c u bs.reverse a) =
      AdjoinRoot.root (monicPolynomial n c) ^ bs.length * coefficientEval c a +
        coefficientEval c u * evalBits (AdjoinRoot.root (monicPolynomial n c)) bs := by
  induction bs generalizing a with
  | nil => simp [hornerWith, evalBits]
  | cons b bs ih =>
      rw [List.reverse_cons]
      simp only [hornerWith, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [coefficientEval_hornerStep]
      change AdjoinRoot.root (monicPolynomial n c) *
        coefficientEval c (hornerWith c u bs.reverse a) + _ = _
      rw [ih]
      simp only [List.length_cons, evalBits, List.foldr_cons, pow_succ]
      ring

theorem coefficientEval_hornerProduct {n : ℕ} (c u v : BinaryWord n) :
    coefficientEval c (hornerWith c u (encodeWord v).reverse (fun _ => 0)) =
      coefficientEval c u * coefficientEval c v := by
  rw [coefficientEval_hornerReverse, evalBits_encodeWord]
  change _ * coefficientEval c (0 : BinaryWord n) +
    coefficientEval c u * coefficientEval c v = _
  simp

theorem evalWordAt_coeff {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    (r : K) (p : Polynomial (ZMod 2)) {m : ℕ} (hm : p.natDegree < m) :
    evalWordAt r (fun i : Fin m => p.coeff i.val) = Polynomial.aeval r p := by
  rw [evalWordAt_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range' _ hm]
  exact Fin.sum_univ_eq_sum_range (fun i => algebraMap (ZMod 2) K (p.coeff i) * r ^ i) m

/-- The high-to-low fold computes the coefficient vector of a polynomial
product whenever that product and both inputs fit in the supplied word width. -/
theorem hornerWith_coeffProduct {m : ℕ} (c : BinaryWord m)
    (p q : Polynomial (ZMod 2)) (hp : p.natDegree < m) (hq : q.natDegree < m)
    (hpq : (p * q).natDegree < m) :
    hornerWith c (fun i => p.coeff i.val)
      (encodeWord (fun i : Fin m => q.coeff i.val)).reverse (fun _ => 0) =
        fun i : Fin m => (p * q).coeff i.val := by
  apply coefficientEval_injective c
  rw [coefficientEval_hornerProduct]
  simp only [coefficientEval, evalWordAt_coeff _ p hp, evalWordAt_coeff _ q hq,
    evalWordAt_coeff _ (p * q) hpq, map_mul]

/-- With zero lower modulus coefficients, the operational Horner algorithm
computes the exact factor-product test before any irreducible modulus is chosen. -/
theorem hornerWith_zero_monicProduct {n k : ℕ} (hk : k ≤ n)
    (u : BinaryWord k) (v : BinaryWord (n - k)) :
    hornerWith (fun _ : Fin (n + 1) => 0)
      (fun i : Fin (n + 1) => monicCoeff k u i.val)
      (encodeWord (fun i : Fin (n + 1) => monicCoeff (n - k) v i.val)).reverse
      (fun _ => 0) = fun j : Fin (n + 1) => productCoeff k (n - k) u v j.val := by
  have hp : (monicPolynomial k u).natDegree < n + 1 := by
    rw [monicPolynomial_degree]
    omega
  have hq : (monicPolynomial (n - k) v).natDegree < n + 1 := by
    rw [monicPolynomial_degree]
    omega
  have hpq : (monicPolynomial k u * monicPolynomial (n - k) v).natDegree < n + 1 := by
    rw [(monicPolynomial_monic k u).natDegree_mul (monicPolynomial_monic (n - k) v),
      monicPolynomial_degree, monicPolynomial_degree]
    omega
  simpa only [monicPolynomial_coeff, ← productCoeff_eq] using
    hornerWith_coeffProduct (fun _ : Fin (n + 1) => 0)
      (monicPolynomial k u) (monicPolynomial (n - k) v) hp hq hpq

end EthInapproximability.CurrentPaper.SamplerPolynomialProduct
