import EthInapproximability.CurrentPaper.SamplerMachineIncrement
import EthInapproximability.CurrentPaper.SamplerPolynomialProduct
import Mathlib.Data.List.Iterate

/-!
# The binary-counter order of the executable sampler search

Source: locked v8 `E-exact-details.tex`, monic-polynomial enumeration in
`lem:exact-families`. The head coefficient changes first in `allWords`, exactly
as in the actual fixed-width increment machine. The identities here identify
the searched list and its first successful element, not merely its set of
elements. They do not claim the full search-controller runtime.
-/

namespace EthInapproximability.CurrentPaper.SamplerEnumeration

open ExecutableSmallBiasSampler SamplerMachine SamplerMachineIncrement SamplerHorner
open scoped BigOperators Polynomial

/-- Decode a fixed-width coefficient word, padding a short input by zero. -/
def decodeWord (n : ℕ) (bits : List Bool) : BinaryWord n :=
  fun i => decodeBit (bits[i.val]?.getD false)

@[simp] theorem decodeWord_encodeWord {n : ℕ} (c : BinaryWord n) :
    decodeWord n (encodeWord c) = c := by
  funext i
  simp [decodeWord, encodeWord]

theorem encodeWord_injective {n : ℕ} :
    Function.Injective (encodeWord : BinaryWord n → List Bool) := by
  intro u v h
  have := congrArg (decodeWord n) h
  simpa using this

@[simp] theorem encodeWord_cons {n : ℕ} (b : ZMod 2) (c : BinaryWord n) :
    encodeWord (Fin.cons b c) = encodeBit b :: encodeWord c := by
  simp [encodeWord, List.ofFn_succ]

@[simp] theorem encodeWord_zero (n : ℕ) :
    encodeWord (fun _ : Fin n => 0) = List.replicate n false := by
  simp [encodeWord, encodeBit]

/-- Two successive increments expose the two possible low coefficients. -/
theorem iterate_double (q : List Bool) (t : ℕ) :
    List.iterate increment (false :: q) (2 * t) =
      (List.iterate increment q t).flatMap (fun w => [false :: w, true :: w]) := by
  induction t generalizing q with
  | zero => simp
  | succ t ih =>
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega]
      simp only [List.iterate, increment, List.flatMap_cons, List.cons_append,
        List.nil_append]
      rw [ih]

/-- The literal candidates generated from the all-zero counter. -/
def counterWords (n : ℕ) : List (List Bool) :=
  List.iterate increment (List.replicate n false) (2 ^ n)

/-- Exact order agreement, including the zero-width singleton. -/
theorem counterWords_eq (n : ℕ) :
    counterWords n = (allWords n).map encodeWord := by
  induction n with
  | zero => simp [counterWords, allWords, encodeWord]
  | succ n ih =>
      change List.iterate increment (false :: List.replicate n false) (2 ^ (n + 1)) = _
      rw [pow_succ, Nat.mul_comm, iterate_double]
      change (counterWords n).flatMap _ = _
      rw [ih]
      simp only [allWords, List.map_flatMap, List.flatMap_map,
        List.map_cons, List.map_nil, encodeWord_cons]
      rfl

theorem counterWords_length (n : ℕ) : (counterWords n).length = 2 ^ n := by
  simp [counterWords]

theorem counterWords_nodup (n : ℕ) : (counterWords n).Nodup := by
  rw [counterWords_eq]
  exact (allWords_nodup n).map encodeWord_injective

theorem increment_iterate_length (n j : ℕ) :
    ((increment^[j]) (List.replicate n false)).length = n := by
  induction j with
  | zero => simp
  | succ j ih => simpa only [Function.iterate_succ_apply', increment_length] using ih

theorem counterWords_contains {n : ℕ} (c : BinaryWord n) :
    encodeWord c ∈ counterWords n := by
  rw [counterWords_eq]
  exact List.mem_map.mpr ⟨c, mem_allWords c, rfl⟩

/-- The controller's list-based first-success search has the original exact
selected modulus, rather than only an isomorphic or permuted field. -/
theorem counterWords_find (n : ℕ) :
    (counterWords n).find? (fun q => irreducibleTest n (decodeWord n q)) =
      ((allWords n).find? (irreducibleTest n)).map encodeWord := by
  rw [counterWords_eq, List.find?_map]
  simp only [Function.comp_def, decodeWord_encodeWord]

def counterChosen (n : ℕ) : List Bool :=
  ((counterWords n).find? (fun q => irreducibleTest n (decodeWord n q))).getD
    (List.replicate n false)

theorem counterChosen_eq (n : ℕ) : counterChosen n = encodeWord (chosenWord n) := by
  rw [counterChosen, counterWords_find]
  unfold chosenWord
  cases (allWords n).find? (irreducibleTest n) <;> simp

/-- Zero-padded coefficients of an arbitrary, not necessarily monic word. -/
def rawCoeff {n : ℕ} (u : BinaryWord n) (j : ℕ) : ZMod 2 :=
  if h : j < n then u ⟨j, h⟩ else 0

noncomputable def coefficientPolynomial {n : ℕ} (u : BinaryWord n) :
    Polynomial (ZMod 2) := ∑ i : Fin n, Polynomial.monomial i.val (u i)

theorem coefficientPolynomial_coeff {n : ℕ} (u : BinaryWord n) (j : ℕ) :
    (coefficientPolynomial u).coeff j = rawCoeff u j := by
  classical
  simp only [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hj : j < n
  · rw [rawCoeff, dif_pos hj, Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
    · simp
    · intro b _ hbj
      rw [if_neg]
      intro heq
      exact hbj (Fin.ext heq)
    · simp
  · rw [rawCoeff, dif_neg hj]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    have := i.isLt
    omega

theorem coefficientPolynomial_degree_lt {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    (coefficientPolynomial u).natDegree < n := by
  have h : (coefficientPolynomial u).natDegree ≤ n - 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coefficientPolynomial_coeff, rawCoeff, dif_neg (by omega)]
  omega

theorem coefficientPolynomial_representation {n : ℕ} (p : Polynomial (ZMod 2))
    (hp : p.natDegree < n) :
    coefficientPolynomial (fun i : Fin n => p.coeff i.val) = p := by
  ext j
  rw [coefficientPolynomial_coeff]
  by_cases hj : j < n
  · simp [rawCoeff, hj]
  · rw [rawCoeff, dif_neg hj]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- A factor must have a nonzero coefficient above its constant term. -/
def Nonconstant {n : ℕ} (u : BinaryWord n) : Prop :=
  ∃ i : Fin n, 0 < i.val ∧ u i ≠ 0

instance {n : ℕ} (u : BinaryWord n) : Decidable (Nonconstant u) := by
  unfold Nonconstant
  infer_instance

theorem encodeBit_eq_true_iff (a : ZMod 2) : encodeBit a = true ↔ a ≠ 0 := by
  change decide (a = 1) = true ↔ a ≠ 0
  rw [decide_eq_true_eq]
  constructor
  · intro h
    simpa only [h] using (one_ne_zero : (1 : ZMod 2) ≠ 0)
  · intro h
    apply ZMod.val_injective 2
    have ha := a.val_lt
    have hz : a.val ≠ 0 := by
      intro hh
      apply h
      exact ZMod.val_injective 2 (by simpa using hh)
    change a.val = 1
    omega

/-- Nonconstant factors are recognized by a Boolean scan after the first bit. -/
theorem nonconstant_iff_tail_any {n : ℕ} (u : BinaryWord n) :
    Nonconstant u ↔ ((encodeWord u).drop 1).any id = true := by
  cases n with
  | zero => simp [Nonconstant, encodeWord]
  | succ n =>
      simp only [encodeWord, List.ofFn_succ, List.drop_succ_cons, List.drop_zero,
        List.any_eq_true, List.mem_ofFn, id_eq]
      constructor
      · rintro ⟨i, hi, hu⟩
        refine ⟨true, ⟨⟨i.val - 1, by omega⟩, ?_⟩, rfl⟩
        have heq : (⟨i.val - 1, by omega⟩ : Fin n).succ = i := by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        rw [heq, encodeBit_eq_true_iff]
        exact hu
      · rintro ⟨b, ⟨i, hu⟩, hb⟩
        exact ⟨i.succ, by simp, (encodeBit_eq_true_iff _).mp (hu.trans hb)⟩

theorem nonconstant_iff_degree_pos {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    Nonconstant u ↔ 0 < (coefficientPolynomial u).natDegree := by
  constructor
  · rintro ⟨i, hi, hui⟩
    have hc : (coefficientPolynomial u).coeff i.val ≠ 0 := by
      simpa [coefficientPolynomial_coeff, rawCoeff, i.isLt] using hui
    exact lt_of_lt_of_le hi (Polynomial.le_natDegree_of_ne_zero hc)
  · intro hp
    have hd := coefficientPolynomial_degree_lt hn u
    refine ⟨⟨(coefficientPolynomial u).natDegree, hd⟩, hp, ?_⟩
    have hc : (coefficientPolynomial u).coeff (coefficientPolynomial u).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
      exact Polynomial.ne_zero_of_natDegree_gt hp
    rw [coefficientPolynomial_coeff, rawCoeff, dif_pos hd] at hc
    exact hc

/-- Finite convolution of two arbitrary fixed-width coefficient words. -/
def rawProductCoeff {n : ℕ} (u v : BinaryWord n) (j : ℕ) : ZMod 2 :=
  ∑ s ∈ Finset.antidiagonal j, rawCoeff u s.1 * rawCoeff v s.2

theorem rawProductCoeff_eq {n : ℕ} (u v : BinaryWord n) (j : ℕ) :
    rawProductCoeff u v j = (coefficientPolynomial u * coefficientPolynomial v).coeff j := by
  simp only [rawProductCoeff, Polynomial.coeff_mul, coefficientPolynomial_coeff]

/-- Width `2*n` contains the entire trial product and the degree-`n` candidate. -/
theorem fixed_factor_eq_iff {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) :
    monicPolynomial n c = coefficientPolynomial u * coefficientPolynomial v ↔
      ∀ j : Fin (2 * n), monicCoeff n c j.val = rawProductCoeff u v j.val := by
  constructor
  · intro h j
    rw [← monicPolynomial_coeff, rawProductCoeff_eq, h]
  · intro h
    ext j
    by_cases hj : j < 2 * n
    · simpa only [monicPolynomial_coeff, rawProductCoeff_eq] using h ⟨j, hj⟩
    · have hd : (coefficientPolynomial u * coefficientPolynomial v).natDegree < 2 * n :=
        lt_of_le_of_lt Polynomial.natDegree_mul_le (by
          have hu := coefficientPolynomial_degree_lt hn u
          have hv := coefficientPolynomial_degree_lt hn v
          omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPolynomial_degree]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- The uniform two-counter test uses two arbitrary `n`-bit factors. It
does not need variable-width factor banks or an irreducibility oracle. -/
def fixedFactorTest (n : ℕ) (c : BinaryWord n) : Bool :=
  decide (∀ u v : BinaryWord n, Nonconstant u → Nonconstant v →
    ¬ ∀ j : Fin (2 * n), monicCoeff n c j.val = rawProductCoeff u v j.val)

theorem fixedFactorTest_eq {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    fixedFactorTest n c = irreducibleTest n c := by
  apply Bool.eq_iff_iff.mpr
  rw [fixedFactorTest, decide_eq_true_eq]
  constructor
  · intro htest
    rw [irreducibleTest, decide_eq_true_eq]
    intro k hk u v heq
    have hk' : k.val < n := k.isLt
    have hl : n - k.val < n := by omega
    let u' : BinaryWord n := fun i => (monicPolynomial k.val u).coeff i.val
    let v' : BinaryWord n := fun i => (monicPolynomial (n - k.val) v).coeff i.val
    have hu' : coefficientPolynomial u' = monicPolynomial k.val u :=
      coefficientPolynomial_representation _ (by rw [monicPolynomial_degree]; exact hk')
    have hv' : coefficientPolynomial v' = monicPolynomial (n - k.val) v :=
      coefficientPolynomial_representation _ (by rw [monicPolynomial_degree]; exact hl)
    apply htest u' v'
    · rw [nonconstant_iff_degree_pos hn, hu', monicPolynomial_degree]
      exact hk
    · rw [nonconstant_iff_degree_pos hn, hv', monicPolynomial_degree]
      omega
    · apply (fixed_factor_eq_iff hn c u' v').mp
      rw [hu', hv']
      exact (factor_eq_iff (Nat.le_of_lt hk') c u v).mpr heq
  · intro htest u v hu hv heq
    have hirr := (irreducibleTest_iff hn c).mp htest
    have hpoly := (fixed_factor_eq_iff hn c u v).mpr heq
    rcases hirr.isUnit_or_isUnit hpoly with hp | hp
    · exact Polynomial.not_isUnit_of_natDegree_pos _
        ((nonconstant_iff_degree_pos hn u).mp hu) hp
    · exact Polynomial.not_isUnit_of_natDegree_pos _
        ((nonconstant_iff_degree_pos hn v).mp hv) hp

/-- The fixed-width multiplication controller can compare all `2*n`
coefficients without knowing any irreducible modulus beforehand. -/
theorem hornerWith_rawProduct {n : ℕ} (hn : 0 < n) (u v : BinaryWord n) :
    SamplerPolynomialProduct.hornerWith (fun _ : Fin (2 * n) => 0)
      (fun i => rawCoeff u i.val)
      (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
      (fun _ => 0) = fun j : Fin (2 * n) => rawProductCoeff u v j.val := by
  have hu := coefficientPolynomial_degree_lt hn u
  have hv := coefficientPolynomial_degree_lt hn v
  have huv : (coefficientPolynomial u * coefficientPolynomial v).natDegree < 2 * n :=
    lt_of_le_of_lt Polynomial.natDegree_mul_le (by omega)
  simpa only [coefficientPolynomial_coeff, ← rawProductCoeff_eq] using
    SamplerPolynomialProduct.hornerWith_coeffProduct (fun _ : Fin (2 * n) => 0)
      (coefficientPolynomial u) (coefficientPolynomial v) (by omega) (by omega) huv

theorem counterWords_all (n : ℕ) (p : BinaryWord n → Bool) :
    (counterWords n).all (fun q => p (decodeWord n q)) = decide (∀ u, p u = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.decide_iff]
  simp only [counterWords_eq, List.all_map, Function.comp_def, decodeWord_encodeWord,
    List.all_eq_true]
  exact ⟨fun h u => h u (mem_allWords u), fun h u _ => h u⟩

/-- Literal nested scans of the two fixed-width factor counters. -/
def fixedListTest (n : ℕ) (c : BinaryWord n) : Bool :=
  (counterWords n).all fun ubits =>
    (counterWords n).all fun vbits =>
      decide (Nonconstant (decodeWord n ubits) → Nonconstant (decodeWord n vbits) →
        ¬ ∀ j : Fin (2 * n), monicCoeff n c j.val =
          rawProductCoeff (decodeWord n ubits) (decodeWord n vbits) j.val)

theorem fixedListTest_eq (n : ℕ) (c : BinaryWord n) :
    fixedListTest n c = fixedFactorTest n c := by
  let P (u v : BinaryWord n) : Prop := Nonconstant u → Nonconstant v →
    ¬ ∀ j : Fin (2 * n), monicCoeff n c j.val = rawProductCoeff u v j.val
  have inner (u : BinaryWord n) :
      (counterWords n).all (fun bits => decide (P u (decodeWord n bits))) =
        decide (∀ v, P u v) := by
    simpa only [decide_eq_true_eq] using
      counterWords_all n (fun v => decide (P u v))
  change (counterWords n).all (fun ubits =>
    (counterWords n).all (fun vbits => decide (P (decodeWord n ubits) (decodeWord n vbits)))) = _
  simp_rw [inner]
  simpa only [decide_eq_true_eq] using
    counterWords_all n (fun u => decide (∀ v, P u v))

theorem counterWords_find_fixed {n : ℕ} (hn : 0 < n) :
    (counterWords n).find? (fun q => fixedListTest n (decodeWord n q)) =
      ((allWords n).find? (irreducibleTest n)).map encodeWord := by
  simp_rw [fixedListTest_eq, fixedFactorTest_eq hn]
  exact counterWords_find n

/-- Exhaustive fixed-width trials have `q^3` candidate/factor triples. This
counts loop iterations only; the finite-control runtime is a separate proof. -/
theorem fixed_trial_count (n : ℕ) :
    (counterWords n).length * (counterWords n).length * (counterWords n).length =
      (2 ^ n) ^ 3 := by
  rw [counterWords_length]
  ring

end EthInapproximability.CurrentPaper.SamplerEnumeration
