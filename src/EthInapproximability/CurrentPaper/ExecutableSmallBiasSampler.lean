import EthInapproximability.CurrentPaper.SmallBiasSampler
import EthInapproximability.CurrentPaper.ProductBalancedness

/-!
# Executable binary polynomial presentations for the trace sampler

Source: locked v8 `E-exact-details.tex`, the finite-field construction in
the proof of `lem:exact-families`. All executable searches below range over
explicit finite coefficient vectors. Semantic field existence and
representation correctness are separate from their resource accounting.
-/

namespace EthInapproximability.CurrentPaper.ExecutableSmallBiasSampler

open scoped Polynomial BigOperators

abbrev BinaryWord (n : ℕ) := Fin n → ZMod 2

/-- The monic degree-`n` binary polynomial with the supplied lower bits. -/
noncomputable def monicPolynomial (n : ℕ) (c : BinaryWord n) : Polynomial (ZMod 2) :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.monomial i.val (c i)

/-- Executable coefficient function, including the leading one. -/
def monicCoeff (n : ℕ) (c : BinaryWord n) (j : ℕ) : ZMod 2 :=
  if hj : j < n then c ⟨j, hj⟩ else if j = n then 1 else 0

/-- Executable binary convolution. -/
def productCoeff (k l : ℕ) (u : BinaryWord k) (v : BinaryWord l) (j : ℕ) : ZMod 2 :=
  ∑ s ∈ Finset.antidiagonal j, monicCoeff k u s.1 * monicCoeff l v s.2

/-- Exhaustive factor-product test over all smaller monic binary factors.
Only finite coefficient convolution and equality are executed. -/
def irreducibleTest (n : ℕ) (c : BinaryWord n) : Bool :=
  decide (∀ k : Fin n, 0 < k.val → ∀ u : BinaryWord k.val,
    ∀ v : BinaryWord (n - k.val),
      ¬ ∀ j : Fin (n + 1), monicCoeff n c j.val =
        productCoeff k.val (n - k.val) u v j.val)

theorem monicPolynomial_coeff (n : ℕ) (c : BinaryWord n) (j : ℕ) :
    (monicPolynomial n c).coeff j = monicCoeff n c j := by
  classical
  simp only [monicPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow, Polynomial.coeff_monomial, monicCoeff]
  by_cases hj : j < n
  · rw [dif_pos hj, if_neg (by omega : ¬ j = n)]
    simp only [zero_add]
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · simp
    · intro b _ hbj
      rw [if_neg]
      intro heq
      exact hbj (Fin.ext heq)
    · simp
  · rw [dif_neg hj]
    have hsum : (∑ i : Fin n, if i.val = j then c i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      have := i.isLt
      omega
    rw [hsum, add_zero]

theorem monicPolynomial_degree (n : ℕ) (c : BinaryWord n) :
    (monicPolynomial n c).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [monicPolynomial_coeff]
    simp [monicCoeff, show ¬ j < n by omega, show ¬ j = n by omega]
  · rw [monicPolynomial_coeff]
    simp [monicCoeff]

theorem monicPolynomial_monic (n : ℕ) (c : BinaryWord n) :
    (monicPolynomial n c).Monic := by
  change (monicPolynomial n c).coeff (monicPolynomial n c).natDegree = 1
  rw [monicPolynomial_degree, monicPolynomial_coeff]
  simp [monicCoeff]

/-- Every monic polynomial occurs in the explicit coefficient enumeration. -/
theorem monicPolynomial_representation {n : ℕ} (p : Polynomial (ZMod 2))
    (hp : p.Monic) (hn : p.natDegree = n) :
    monicPolynomial n (fun i => p.coeff i.val) = p := by
  ext j
  rw [monicPolynomial_coeff]
  by_cases hj : j < n
  · simp [monicCoeff, hj]
  · by_cases heq : j = n
    · subst j
      simp [monicCoeff, ← hn, hp.coeff_natDegree]
    · have hzero : p.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [monicCoeff, hj, heq, hzero]

theorem productCoeff_eq (k l : ℕ) (u : BinaryWord k) (v : BinaryWord l) (j : ℕ) :
    productCoeff k l u v j = (monicPolynomial k u * monicPolynomial l v).coeff j := by
  simp only [productCoeff, Polynomial.coeff_mul, monicPolynomial_coeff]

/-- It suffices to compare the `n+1` possible nonzero coefficients of the
two monic factors. This validates the executable finite product test. -/
theorem factor_eq_iff {n k : ℕ} (hk : k ≤ n)
    (c : BinaryWord n) (u : BinaryWord k) (v : BinaryWord (n - k)) :
    monicPolynomial n c = monicPolynomial k u * monicPolynomial (n - k) v ↔
      ∀ j : Fin (n + 1), monicCoeff n c j.val = productCoeff k (n - k) u v j.val := by
  constructor
  · intro heq j
    rw [← monicPolynomial_coeff, productCoeff_eq, heq]
  · intro hcoeff
    have hdegree : (monicPolynomial k u * monicPolynomial (n - k) v).natDegree = n := by
      rw [(monicPolynomial_monic k u).natDegree_mul (monicPolynomial_monic (n - k) v),
        monicPolynomial_degree, monicPolynomial_degree]
      omega
    ext j
    by_cases hj : j ≤ n
    · simpa only [monicPolynomial_coeff, productCoeff_eq] using hcoeff ⟨j, by omega⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPolynomial_degree]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdegree]; omega)]

/-- The finite convolution test decides semantic polynomial irreducibility.
Its executable definition contains no classical equality or field oracle. -/
theorem irreducibleTest_iff {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    irreducibleTest n c = true ↔ Irreducible (monicPolynomial n c) := by
  rw [irreducibleTest, decide_eq_true_eq,
    (monicPolynomial_monic n c).irreducible_iff_natDegree]
  have hne : monicPolynomial n c ≠ 1 := by
    intro heq
    have hd := congrArg Polynomial.natDegree heq
    rw [monicPolynomial_degree, Polynomial.natDegree_one] at hd
    omega
  refine ⟨?_, ?_⟩
  · intro htest
    refine ⟨hne, ?_⟩
    intro f g hf hg hfg
    by_contra hnot
    push Not at hnot
    have hdeg : f.natDegree + g.natDegree = n := by
      rw [← hf.natDegree_mul hg, hfg, monicPolynomial_degree]
    let k : Fin n := ⟨f.natDegree, by omega⟩
    have hgdeg : g.natDegree = n - k.val := by dsimp [k]; omega
    apply htest k (by dsimp [k]; omega)
      (fun i => f.coeff i.val) (fun i => g.coeff i.val)
    apply (factor_eq_iff (Nat.le_of_lt k.isLt) _ _ _).mp
    rw [monicPolynomial_representation f hf rfl,
      monicPolynomial_representation g hg hgdeg]
    exact hfg.symm
  · rintro ⟨_, hirr⟩ k hk u v hcoeff
    have heq := (factor_eq_iff (Nat.le_of_lt k.isLt) c u v).mpr hcoeff
    have hz := hirr _ _ (monicPolynomial_monic k.val u)
      (monicPolynomial_monic (n - k.val) v) heq.symm
    simp only [monicPolynomial_degree] at hz
    have := k.isLt
    omega

/-- Standard finite-field existence certifies the finite search. It is not
used as the algorithm for choosing a polynomial. -/
theorem exists_monic_irreducible_degree (n : ℕ) (hn : 0 < n) :
    ∃ p : Polynomial (ZMod 2), p.Monic ∧ Irreducible p ∧ p.natDegree = n := by
  obtain ⟨a, ha⟩ :=
    Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 n)
  refine ⟨minpoly (ZMod 2) a, minpoly.monic (IsIntegral.of_finite (ZMod 2) a),
    minpoly.irreducible (IsIntegral.of_finite (ZMod 2) a), ?_⟩
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) a).mp ha,
    GaloisField.finrank 2 hn.ne']

theorem exists_passing_word (n : ℕ) (hn : 0 < n) :
    ∃ c : BinaryWord n, irreducibleTest n c = true := by
  obtain ⟨p, hp, hirr, hd⟩ := exists_monic_irreducible_degree n hn
  refine ⟨fun i => p.coeff i.val, (irreducibleTest_iff hn _).mpr ?_⟩
  rwa [monicPolynomial_representation p hp hd]

/-- Canonical finite enumeration of all binary coefficient vectors. -/
def allWords : (n : ℕ) → List (BinaryWord n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (allWords n).flatMap fun c => [Fin.cons 0 c, Fin.cons 1 c]

theorem mem_allWords {n : ℕ} (c : BinaryWord n) : c ∈ allWords n := by
  induction n with
  | zero =>
      have heq : c = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
      simp [allWords, heq]
  | succ n ih =>
      apply List.mem_flatMap.mpr
      refine ⟨Fin.tail c, ih (Fin.tail c), ?_⟩
      have hbit : c 0 = 0 ∨ c 0 = 1 := by
        have hb := (c 0).val_lt
        have hval : (c 0).val = 0 ∨ (c 0).val = 1 := by omega
        rcases hval with hv | hv
        · left; exact (ZMod.val_injective 2) (by simpa using hv)
        · right; exact (ZMod.val_injective 2) (by simpa using hv)
      rcases hbit with hb | hb <;>
        simp [← hb, Fin.cons_self_tail]

theorem allWords_length (n : ℕ) : (allWords n).length = 2 ^ n := by
  induction n with
  | zero => simp [allWords]
  | succ n ih => simp [allWords, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

theorem allWords_nodup (n : ℕ) : (allWords n).Nodup := by
  classical
  have hall : (allWords n).toFinset = Finset.univ := by
    ext c
    simp [mem_allWords c]
  have hc : (allWords n).toFinset.card = (allWords n).length := by
    rw [hall, allWords_length]
    simp [BinaryWord]
  have hc' : (allWords n : Multiset (BinaryWord n)).toFinset.card =
      (allWords n : Multiset (BinaryWord n)).card := hc
  exact Multiset.coe_nodup.mp (Multiset.toFinset_card_eq_card_iff_nodup.mp hc')

/-- Canonical executable integer labels for all coefficient vectors. -/
def wordLabels (n : ℕ) : Fin (2 ^ n) ≃ BinaryWord n :=
  (finCongr (allWords_length n).symm).trans
    (List.Nodup.getEquivOfForallMemList (allWords n) (allWords_nodup n)
      (fun c => mem_allWords c))

/-- Each pair is labelled separately, including pairs producing the same
sampler output word. -/
def wordPairLabels (n : ℕ) : Fin ((2 ^ n) ^ 2) ≃ BinaryWord n × BinaryWord n :=
  (finCongr (pow_two (2 ^ n))).trans
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (wordLabels n) (wordLabels n)))

/-- Executable base-two grouping, with exactly the same digit convention
as the existing sampler's alphabet equivalence. -/
def blockAlphabetEquiv (a : ℕ) : BinaryWord a ≃ Fin (2 ^ a) :=
  (Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).toEquiv.symm).trans finFunctionFinEquiv

theorem blockAlphabetEquiv_eq (a : ℕ) :
    blockAlphabetEquiv a = SmallBiasSampler.blockAlphabetEquiv a := rfl

/-- The factor test examines at most this many pairs of monic factors,
including the unused degree-zero branch. This is a count of finite test
candidates, not a machine-runtime theorem. -/
theorem factor_candidate_count (n : ℕ) :
    (∑ k : Fin n, 2 ^ k.val * 2 ^ (n - k.val)) = n * 2 ^ n := by
  have heq (k : Fin n) : 2 ^ k.val * 2 ^ (n - k.val) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt k.isLt)]
  simp_rw [heq]
  simp

/-- Exhausting every polynomial candidate and every factor-product
candidate uses at most `n q²` such tests, where `q = 2^n`. Coefficient
convolution and the machine representation are accounted for separately. -/
theorem search_candidate_count (n : ℕ) :
    (allWords n).length * (∑ k : Fin n, 2 ^ k.val * 2 ^ (n - k.val)) =
      n * (2 ^ n) ^ 2 := by
  rw [allWords_length, factor_candidate_count]
  ring

theorem convolution_summand_count (n : ℕ) :
    (∑ j : Fin (n + 1), (Finset.antidiagonal j.val).card) ≤ (n + 1) ^ 2 := by
  calc
    _ ≤ ∑ _j : Fin (n + 1), (n + 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [Finset.Nat.card_antidiagonal]
      exact Nat.succ_le_of_lt j.isLt
    _ = _ := by simp [pow_two]

/-- Polynomial bound on all possible convolution summands in the search.
This counts the nested finite mathematical loops; it does not yet claim
a bit-machine interpreter or runtime bound for their implementation. -/
theorem search_convolution_summand_bound (n : ℕ) :
    (allWords n).length * (∑ k : Fin n, 2 ^ k.val * 2 ^ (n - k.val)) *
        (∑ j : Fin (n + 1), (Finset.antidiagonal j.val).card) ≤ (2 ^ n) ^ 5 := by
  rw [search_candidate_count]
  have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have hn1 : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (2 ^ n) * (2 ^ n) ^ 2 * (2 ^ n) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hn)
        ((convolution_summand_count n).trans (Nat.pow_le_pow_left hn1 2))
    _ = _ := by ring

/-- The executable search returns the first passing coefficient vector.
The zero-degree fallback makes this a total program; positive degrees
are proved to find a passing candidate. -/
def chosenWord (n : ℕ) : BinaryWord n :=
  ((allWords n).find? (irreducibleTest n)).getD (fun _ => 0)

theorem chosenWord_passes {n : ℕ} (hn : 0 < n) :
    irreducibleTest n (chosenWord n) = true := by
  obtain ⟨c, hc⟩ := exists_passing_word n hn
  have hnonempty : (allWords n).find? (irreducibleTest n) ≠ none := by
    intro heq
    have hn := List.find?_eq_none.mp heq c (mem_allWords c)
    exact hn hc
  cases heq : (allWords n).find? (irreducibleTest n) with
  | none => exact False.elim (hnonempty heq)
  | some c =>
      simpa only [chosenWord, heq, Option.getD_some] using List.find?_some heq

noncomputable def chosenPolynomial (n : ℕ) : Polynomial (ZMod 2) :=
  monicPolynomial n (chosenWord n)

theorem chosenPolynomial_monic (n : ℕ) : (chosenPolynomial n).Monic :=
  monicPolynomial_monic n _

theorem chosenPolynomial_degree (n : ℕ) : (chosenPolynomial n).natDegree = n :=
  monicPolynomial_degree n _

theorem chosenPolynomial_irreducible {n : ℕ} (hn : 0 < n) :
    Irreducible (chosenPolynomial n) :=
  (irreducibleTest_iff hn _).mp (chosenWord_passes hn)

noncomputable instance chosenPolynomialIrreducible (n : ℕ) [NeZero n] :
    Fact (Irreducible (chosenPolynomial n)) :=
  ⟨chosenPolynomial_irreducible (Nat.pos_of_ne_zero (NeZero.ne n))⟩

/-- Semantic quotient attached to the polynomial actually selected by the
executable coefficient search. Executable arithmetic is carried by words. -/
abbrev BinaryExtension (n : ℕ) := AdjoinRoot (chosenPolynomial n)

theorem binaryExtension_card (n : ℕ) : Nat.card (BinaryExtension n) = 2 ^ n := by
  rw [Nat.card_congr (AdjoinRoot.powerBasisAux' (chosenPolynomial_monic n)).equivFun.toEquiv,
    Nat.card_fun, Nat.card_zmod, Nat.card_fin, chosenPolynomial_degree]

/-- The selected polynomial presentation is isomorphic to the abstract
binary field used by the already checked sampler. This is a semantic
equivalence, not an algorithm for producing the isomorphism. -/
noncomputable def binaryExtensionEquiv (n : ℕ) [NeZero n] :
    BinaryExtension n ≃ₐ[ZMod 2] GaloisField 2 n :=
  GaloisField.algEquivGaloisField 2 n (binaryExtension_card n)

/-- Algebra isomorphisms preserve each trace-sampler bit, with the same
coordinate exponent and separately relabelled pair of seeds. -/
theorem traceBits_algEquiv {K K' : Type*} [Field K] [Field K']
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) K']
    (e : K ≃ₐ[ZMod 2] K') (L : ℕ) (seed : K × K) (i : Fin L) :
    SmallBiasSampler.traceBits K' L (e seed.1, e seed.2) i =
      SmallBiasSampler.traceBits K L seed i := by
  simp only [SmallBiasSampler.traceBits, ← map_pow, ← map_mul]
  exact Algebra.trace_eq_of_algEquiv e _

/-- The binary trace is the finite sum of Frobenius powers. This is the
semantic specification for the executable coefficient-word evaluator. -/
theorem algebraMap_trace_eq_sum_binary_pow
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    {n : ℕ} (hdim : Module.finrank (ZMod 2) K = n) (x : K) :
    algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K x) =
      ∑ i : Fin n, x ^ (2 ^ i.val) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, Nat.card_zmod, hdim]
  exact (Fin.sum_univ_eq_sum_range (fun i => x ^ (2 ^ i)) n).symm

theorem binaryExtension_trace_eq_sum_binary_pow
    (n : ℕ) [NeZero n] (x : BinaryExtension n) :
    algebraMap (ZMod 2) (BinaryExtension n)
        (Algebra.trace (ZMod 2) (BinaryExtension n) x) =
      ∑ i : Fin n, x ^ (2 ^ i.val) := by
  letI := (chosenPolynomial_monic n).finite_adjoinRoot
  letI : Finite (BinaryExtension n) := Module.finite_of_finite (ZMod 2)
  apply algebraMap_trace_eq_sum_binary_pow
  simpa [chosenPolynomial_degree] using
    Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' (chosenPolynomial_monic n))

/-- Executable coefficientwise addition. -/
def wordAdd {n : ℕ} (u v : BinaryWord n) : BinaryWord n :=
  fun i => u i + v i

/-- Executable multiplication of all coefficients by one bit. -/
def wordScale {n : ℕ} (a : ZMod 2) (u : BinaryWord n) : BinaryWord n :=
  fun i => a * u i

/-- Shift the coefficients by one place and reduce the leading coefficient
using the monic polynomial selected by the executable search. -/
def wordShift : (n : ℕ) → BinaryWord n → BinaryWord n
  | 0, u => u
  | k + 1, u =>
      let shifted : BinaryWord (k + 1) := Fin.cons 0 (fun j : Fin k => u j.castSucc)
      fun i => shifted i - u (Fin.last k) * chosenWord (k + 1) i

/-- Semantic evaluation of a coefficient word at an arbitrary algebra element. -/
noncomputable def evalWordAt {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    {n : ℕ} (r : K) : BinaryWord n →ₗ[ZMod 2] K :=
  Fintype.linearCombination (ZMod 2) (fun i : Fin n => r ^ i.val)

theorem evalWordAt_apply {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    {n : ℕ} (r : K) (u : BinaryWord n) :
    evalWordAt r u = ∑ i : Fin n, algebraMap (ZMod 2) K (u i) * r ^ i.val := by
  simp only [evalWordAt, Fintype.linearCombination_apply, Algebra.smul_def]

@[simp] theorem evalWordAt_add {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    {n : ℕ} (r : K) (u v : BinaryWord n) :
    evalWordAt r (wordAdd u v) = evalWordAt r u + evalWordAt r v :=
  (evalWordAt r).map_add u v

@[simp] theorem evalWordAt_scale {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    {n : ℕ} (r : K) (a : ZMod 2) (u : BinaryWord n) :
    evalWordAt r (wordScale a u) = algebraMap (ZMod 2) K a * evalWordAt r u := by
  change evalWordAt r (a • u) = _
  rw [map_smul, Algebra.smul_def]

/-- Evaluation in the quotient by the selected polynomial. -/
noncomputable def wordEval (n : ℕ) : BinaryWord n →ₗ[ZMod 2] BinaryExtension n :=
  evalWordAt (AdjoinRoot.root (chosenPolynomial n))

theorem chosen_root_relation (n : ℕ) :
    AdjoinRoot.root (chosenPolynomial n) ^ n + wordEval n (chosenWord n) = 0 := by
  have h : (AdjoinRoot.mk (chosenPolynomial n)) (chosenPolynomial n) = 0 :=
    AdjoinRoot.mk_self
  change (AdjoinRoot.mk (chosenPolynomial n))
    (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.monomial i.val (chosenWord n i)) = 0 at h
  rw [map_add, map_pow, AdjoinRoot.mk_X, map_sum] at h
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X] at h
  simpa only [wordEval, evalWordAt_apply, AdjoinRoot.algebraMap_eq] using h

theorem evalWordAt_rawShift {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    {k : ℕ} (r : K) (u : BinaryWord (k + 1)) :
    evalWordAt r (Fin.cons 0 (fun j : Fin k => u j.castSucc)) =
      r * evalWordAt r u - algebraMap (ZMod 2) K (u (Fin.last k)) * r ^ (k + 1) := by
  rw [evalWordAt_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, map_zero, zero_mul, Fin.cons_succ, Fin.val_succ, zero_add]
  rw [evalWordAt_apply, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [mul_add, Finset.mul_sum]
  simp_rw [pow_succ]
  have hsum : (∑ i : Fin k, algebraMap (ZMod 2) K (u i.castSucc) * (r ^ i.val * r)) =
      ∑ i : Fin k, r * (algebraMap (ZMod 2) K (u i.castSucc) * r ^ i.val) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

theorem wordEval_shift (n : ℕ) (u : BinaryWord n) :
    wordEval n (wordShift n u) =
      AdjoinRoot.root (chosenPolynomial n) * wordEval n u := by
  cases n with
  | zero => simp [wordShift, wordEval, evalWordAt_apply]
  | succ k =>
      have hs : wordShift (k + 1) u =
          (Fin.cons 0 (fun j : Fin k => u j.castSucc) : BinaryWord (k + 1)) -
            wordScale (u (Fin.last k)) (chosenWord (k + 1)) := rfl
      rw [hs]
      simp only [wordEval]
      rw [map_sub, evalWordAt_scale, evalWordAt_rawShift]
      have hroot := chosen_root_relation (k + 1)
      change AdjoinRoot.root (chosenPolynomial (k + 1)) ^ (k + 1) +
        evalWordAt (AdjoinRoot.root (chosenPolynomial (k + 1))) (chosenWord (k + 1)) = 0 at hroot
      linear_combination -algebraMap (ZMod 2) (BinaryExtension (k + 1))
        (u (Fin.last k)) * hroot

/-- Executable shift-and-add multiplication of coefficient words. -/
def wordMul (n : ℕ) (u v : BinaryWord n) : BinaryWord n :=
  ∑ i : Fin n, wordScale (v i) ((wordShift n)^[i.val] u)

theorem wordEval_iterateShift (n k : ℕ) (u : BinaryWord n) :
    wordEval n ((wordShift n)^[k] u) =
      AdjoinRoot.root (chosenPolynomial n) ^ k * wordEval n u := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', wordEval_shift, ih, pow_succ]
      ring

theorem wordEval_mul (n : ℕ) (u v : BinaryWord n) :
    wordEval n (wordMul n u v) = wordEval n u * wordEval n v := by
  rw [wordMul, map_sum]
  simp only [wordEval, evalWordAt_scale]
  change (∑ i : Fin n, algebraMap (ZMod 2) (BinaryExtension n) (v i) *
    wordEval n ((wordShift n)^[i.val] u)) = _
  simp_rw [wordEval_iterateShift]
  rw [show evalWordAt (AdjoinRoot.root (chosenPolynomial n)) v =
      ∑ i : Fin n, algebraMap (ZMod 2) (BinaryExtension n) (v i) *
        AdjoinRoot.root (chosenPolynomial n) ^ i.val from evalWordAt_apply _ _,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [wordEval]
  ring

/-- The canonical polynomial basis, indexed by the original word length. -/
noncomputable def wordBasis (n : ℕ) :
    Module.Basis (Fin n) (ZMod 2) (BinaryExtension n) :=
  (AdjoinRoot.powerBasis' (chosenPolynomial_monic n)).basis.reindex
    (finCongr (chosenPolynomial_degree n))

theorem wordBasis_apply (n : ℕ) (i : Fin n) :
    wordBasis n i = AdjoinRoot.root (chosenPolynomial n) ^ i.val := by
  simp only [wordBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- Semantic equivalence induced by the canonical polynomial basis. -/
noncomputable def wordEquiv (n : ℕ) : BinaryWord n ≃ₗ[ZMod 2] BinaryExtension n :=
  (wordBasis n).equivFun.symm

theorem wordEquiv_apply (n : ℕ) (u : BinaryWord n) :
    wordEquiv n u = wordEval n u := by
  rw [wordEquiv, Module.Basis.equivFun_symm_apply]
  simp only [wordBasis_apply, wordEval, evalWordAt, Fintype.linearCombination_apply]

theorem wordEval_bijective (n : ℕ) : Function.Bijective (wordEval n) := by
  have h : (wordEquiv n : BinaryWord n → BinaryExtension n) = wordEval n :=
    funext (wordEquiv_apply n)
  rw [← h]
  exact (wordEquiv n).bijective

/-- The constant coefficient vector, including a total zero-dimensional case. -/
def constantWord (n : ℕ) (a : ZMod 2) : BinaryWord n :=
  fun i => if i.val = 0 then a else 0

theorem wordEval_constant {n : ℕ} (hn : 0 < n) (a : ZMod 2) :
    wordEval n (constantWord n a) = algebraMap (ZMod 2) (BinaryExtension n) a := by
  rw [wordEval, evalWordAt_apply]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · simp [constantWord]
  · intro b _ hb
    have hne : b.val ≠ 0 := by
      intro heq
      exact hb (Fin.ext heq)
    simp [constantWord, hne]
  · simp

/-- Executable repeated multiplication. The deliberately elementary
implementation suffices because polynomial-in-field-size time is allowed. -/
def wordPow (n : ℕ) (u : BinaryWord n) : ℕ → BinaryWord n
  | 0 => constantWord n 1
  | k + 1 => wordMul n (wordPow n u k) u

theorem wordEval_pow {n : ℕ} (hn : 0 < n) (u : BinaryWord n) (k : ℕ) :
    wordEval n (wordPow n u k) = wordEval n u ^ k := by
  induction k with
  | zero => simp [wordPow, wordEval_constant hn]
  | succ k ih => rw [wordPow, wordEval_mul, ih, pow_succ]

/-- Sum of the Frobenius powers in the coefficient presentation. -/
def wordFrobeniusSum (n : ℕ) (u : BinaryWord n) : BinaryWord n :=
  ∑ i : Fin n, wordPow n u (2 ^ i.val)

theorem wordEval_frobeniusSum {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    wordEval n (wordFrobeniusSum n u) =
      ∑ i : Fin n, wordEval n u ^ (2 ^ i.val) := by
  rw [wordFrobeniusSum, map_sum]
  simp only [wordEval_pow hn]

/-- The trace lies in the prime field, so its constant coefficient is its bit. -/
def traceBit (n : ℕ) (u : BinaryWord n) : ZMod 2 :=
  if hn : 0 < n then wordFrobeniusSum n u ⟨0, hn⟩ else 0

theorem traceBit_eq (n : ℕ) [NeZero n] (u : BinaryWord n) :
    traceBit n u = Algebra.trace (ZMod 2) (BinaryExtension n) (wordEval n u) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have heq : wordFrobeniusSum n u =
      constantWord n (Algebra.trace (ZMod 2) (BinaryExtension n) (wordEval n u)) := by
    apply (wordEval_bijective n).injective
    rw [wordEval_constant hn, wordEval_frobeniusSum hn]
    exact (binaryExtension_trace_eq_sum_binary_pow n (wordEval n u)).symm
  rw [traceBit, dif_pos hn, heq]
  simp [constantWord]

/-- Fully executable bit evaluator for a pair of coefficient-vector seeds. -/
def executableTraceBits (n L : ℕ) (seed : BinaryWord n × BinaryWord n)
    (i : Fin L) : ZMod 2 :=
  traceBit n (wordMul n seed.1 (wordPow n seed.2 i.val))

theorem executableTraceBits_eq (n L : ℕ) [NeZero n]
    (seed : BinaryWord n × BinaryWord n) (i : Fin L) :
    executableTraceBits n L seed i =
      SmallBiasSampler.traceBits (BinaryExtension n) L
        (wordEquiv n seed.1, wordEquiv n seed.2) i := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  simp only [executableTraceBits, traceBit_eq, wordEval_mul, wordEval_pow hn,
    SmallBiasSampler.traceBits, wordEquiv_apply]

/-- A binary word whose coefficients are stored as explicit list data. -/
structure WordVector (n : ℕ) where
  coeffs : List (ZMod 2)
  length_eq : coeffs.length = n

namespace WordVector

/-- Materialize every coefficient before returning the list-backed word. -/
def fromWord {n : ℕ} (u : BinaryWord n) : WordVector n :=
  ⟨List.ofFn u, List.length_ofFn⟩

/-- Lookup in the explicit coefficient data; no delayed field arithmetic. -/
def lookup {n : ℕ} (u : WordVector n) : BinaryWord n :=
  fun i => u.coeffs[i.val]'(by rw [u.length_eq]; exact i.isLt)

@[simp] theorem lookup_fromWord {n : ℕ} (u : BinaryWord n) :
    (fromWord u).lookup = u := by
  funext i
  simp [lookup, fromWord]

@[simp] theorem fromWord_lookup {n : ℕ} (u : WordVector n) :
    fromWord u.lookup = u := by
  cases u with
  | mk coeffs hlength =>
      unfold fromWord
      congr 1
      apply List.ext_getElem
      · simp [hlength]
      · intro i hi hj
        simp [lookup]

end WordVector

/-- Multiply two materialized words and materialize every output coefficient. -/
def vectorMul (n : ℕ) (u v : WordVector n) : WordVector n :=
  WordVector.fromWord (wordMul n u.lookup v.lookup)

@[simp] theorem vectorMul_lookup (n : ℕ) (u v : WordVector n) :
    (vectorMul n u v).lookup = wordMul n u.lookup v.lookup :=
  WordVector.lookup_fromWord _

/-- Every multiplication result is stored before the next multiplication.
This prevents exponent-depth expansion through function-valued coordinates. -/
def vectorPow (n : ℕ) (u : WordVector n) : ℕ → WordVector n
  | 0 => WordVector.fromWord (constantWord n 1)
  | k + 1 => vectorMul n (vectorPow n u k) u

@[simp] theorem vectorPow_lookup (n : ℕ) (u : WordVector n) (k : ℕ) :
    (vectorPow n u k).lookup = wordPow n u.lookup k := by
  induction k with
  | zero => simp [vectorPow, wordPow]
  | succ k ih => simp [vectorPow, wordPow, ih]

/-- The powers and the resulting sum are represented by explicit lists. -/
def vectorFrobeniusSum (n : ℕ) (u : WordVector n) : WordVector n :=
  WordVector.fromWord (∑ i : Fin n, (vectorPow n u (2 ^ i.val)).lookup)

@[simp] theorem vectorFrobeniusSum_lookup (n : ℕ) (u : WordVector n) :
    (vectorFrobeniusSum n u).lookup = wordFrobeniusSum n u.lookup := by
  simp [vectorFrobeniusSum, wordFrobeniusSum]

/-- Trace-bit extraction through the materialized powering implementation. -/
def vectorTraceBit (n : ℕ) (u : WordVector n) : ZMod 2 :=
  if hn : 0 < n then (vectorFrobeniusSum n u).lookup ⟨0, hn⟩ else 0

theorem vectorTraceBit_eq (n : ℕ) (u : WordVector n) :
    vectorTraceBit n u = traceBit n u.lookup := by
  simp [vectorTraceBit, traceBit]

theorem vectorTraceBit_eq_trace (n : ℕ) [NeZero n] (u : WordVector n) :
    vectorTraceBit n u =
      Algebra.trace (ZMod 2) (BinaryExtension n) (wordEval n u.lookup) := by
  rw [vectorTraceBit_eq, traceBit_eq]

/-- The semantic relabelling from executable coefficient seeds to the
finite field used in the original balance proof. -/
noncomputable def wordToGaloisField (n : ℕ) [NeZero n] :
    BinaryWord n ≃ GaloisField 2 n :=
  (wordEquiv n).toEquiv.trans (binaryExtensionEquiv n).toEquiv

theorem executableTraceBits_galois (n L : ℕ) [NeZero n]
    (seed : BinaryWord n × BinaryWord n) (i : Fin L) :
    executableTraceBits n L seed i =
      SmallBiasSampler.traceBits (GaloisField 2 n) L
        (wordToGaloisField n seed.1, wordToGaloisField n seed.2) i := by
  rw [executableTraceBits_eq]
  exact (traceBits_algEquiv (binaryExtensionEquiv n) L
    (wordEquiv n seed.1, wordEquiv n seed.2) i).symm

/-- The actual evaluator stores every intermediate power as coefficient
list data. The function-valued evaluator is used only as its specification. -/
def materializedTraceBits (n L : ℕ) (seed : BinaryWord n × BinaryWord n)
    (i : Fin L) : ZMod 2 :=
  let u := WordVector.fromWord seed.1
  let v := WordVector.fromWord seed.2
  vectorTraceBit n (vectorMul n u (vectorPow n v i.val))

theorem materializedTraceBits_eq (n L : ℕ)
    (seed : BinaryWord n × BinaryWord n) (i : Fin L) :
    materializedTraceBits n L seed i = executableTraceBits n L seed i := by
  simp only [materializedTraceBits, vectorTraceBit_eq, vectorMul_lookup,
    vectorPow_lookup, WordVector.lookup_fromWord, executableTraceBits]

/-- Literal executable finite-index trace family, using stored intermediate powers. -/
def indexedTraceBits (L B : ℕ)
    (seed : Fin ((2 ^ SmallBiasSampler.fieldExponent L B) ^ 2)) (i : Fin L) : ZMod 2 :=
  materializedTraceBits (SmallBiasSampler.fieldExponent L B) L
    (wordPairLabels (SmallBiasSampler.fieldExponent L B) seed) i

/-- The executable and abstract indexed families differ only by this
permutation of their original seed labels. It never identifies equal outputs. -/
noncomputable def seedRelabel {L B : ℕ} (h : 1 < L * B) :
    Fin ((2 ^ SmallBiasSampler.fieldExponent L B) ^ 2) ≃
      Fin ((2 ^ SmallBiasSampler.fieldExponent L B) ^ 2) := by
  letI : NeZero (SmallBiasSampler.fieldExponent L B) :=
    ⟨(SmallBiasSampler.fieldExponent_pos h).ne'⟩
  exact ((wordPairLabels (SmallBiasSampler.fieldExponent L B)).trans
    (Equiv.prodCongr (wordToGaloisField _) (wordToGaloisField _))).trans
      (SmallBiasSampler.fieldPairEquiv h).symm

theorem indexedTraceBits_eq {L B : ℕ} (h : 1 < L * B)
    (seed : Fin ((2 ^ SmallBiasSampler.fieldExponent L B) ^ 2)) (i : Fin L) :
    indexedTraceBits L B seed i =
      SmallBiasSampler.indexedTraceBits L B h (seedRelabel h seed) i := by
  letI : NeZero (SmallBiasSampler.fieldExponent L B) :=
    ⟨(SmallBiasSampler.fieldExponent_pos h).ne'⟩
  rw [indexedTraceBits, materializedTraceBits_eq, executableTraceBits_galois]
  simp [SmallBiasSampler.indexedTraceBits, seedRelabel, Prod.map]

/-- Executable grouped sampler, with the original bit-block alphabet
convention and original number of separately labelled columns. -/
def samplerFamily (q a t E : ℕ) :
    Fin (SmallBiasSampler.samplerSize q a t E) → Fin q → Fin (2 ^ a) :=
  fun seed i => blockAlphabetEquiv a (fun r =>
    indexedTraceBits (q * a) (E * (2 ^ a) ^ t) seed (finProdFinEquiv (i, r)))

theorem samplerFamily_eq {q a t E : ℕ}
    (h : 1 < q * a * (E * (2 ^ a) ^ t))
    (seed : Fin (SmallBiasSampler.samplerSize q a t E)) (i : Fin q) :
    samplerFamily q a t E seed i =
      SmallBiasSampler.samplerFamily q a t E h (seedRelabel h seed) i := by
  simp only [samplerFamily, SmallBiasSampler.samplerFamily, SmallBiasSampler.groupBits,
    blockAlphabetEquiv_eq, indexedTraceBits_eq h]

/-- Balance is inherited by proved seed permutation, not supplied as a
sampler oracle. The executable table retains all `q_field²` seed labels. -/
theorem samplerFamily_balanced {q a t E : ℕ}
    (h : 1 < q * a * (E * (2 ^ a) ^ t)) :
    NPCC.IsBalancedFamily t (samplerFamily q a t E) (1 / (E : ℝ)) := by
  have heq : samplerFamily q a t E =
      fun seed i => SmallBiasSampler.samplerFamily q a t E h (seedRelabel h seed) i := by
    funext seed i
    exact samplerFamily_eq h seed i
  rw [heq]
  exact ProductBalancedness.balanced_reindex
    (SmallBiasSampler.samplerFamily_balanced h) (seedRelabel h)

/-- Executable first call site, including all three appended binary coordinates. -/
def exactFirstFamily (a t d : ℕ) :
    ExactConstruction.FirstFamily a (SmallBiasSampler.exactFirstSize a t d) :=
  fun j i => finTwoEquiv
    (samplerFamily (ExactConstruction.prefixLength a + 3) 1 t
      (SmallBiasSampler.exactDenominator d) j i)

/-- Executable second call site, on the full original `2^a`-symbol alphabet. -/
def exactSecondFamily (a t d : ℕ) :
    ExactConstruction.SecondFamily a d (SmallBiasSampler.exactSecondSize a t d) :=
  samplerFamily d a t (SmallBiasSampler.exactDenominator d)

theorem exactFirstFamily_balanced (a t d : ℕ) (hd : 2 ≤ d) :
    NPCC.IsBalancedFamily t (exactFirstFamily a t d) (1 / (d : ℝ) ^ 8) := by
  simpa [exactFirstFamily, SmallBiasSampler.exactDenominator] using
    SmallBiasSampler.balanced_twoPowOne_to_bool (samplerFamily_balanced
      (SmallBiasSampler.exact_sampler_input (q := ExactConstruction.prefixLength a + 3)
        (a := 1) (t := t) (by omega) (by omega) hd))

theorem exactSecondFamily_balanced (a t d : ℕ) (ha : 0 < a) (hd : 2 ≤ d) :
    NPCC.IsBalancedFamily t (exactSecondFamily a t d) (1 / (d : ℝ) ^ 8) := by
  simpa [exactSecondFamily, SmallBiasSampler.exactDenominator] using
    samplerFamily_balanced (SmallBiasSampler.exact_sampler_input (q := d) (a := a)
      (t := t) (by omega) ha hd)

end EthInapproximability.CurrentPaper.ExecutableSmallBiasSampler
