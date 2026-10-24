import Mathlib
import NPCC.Relaxed
import EthInapproximability.CurrentPaper.ExactConstruction

/-!
# The finite-field sampler of the exact reduction

Source: v8 `E-exact-details.tex`, `lem:exact-families` and its preceding
small-bias construction. Field-pair seeds remain labelled even when their
output tuples coincide. The second alphabet consists of all `2^a` labels,
before the separate duplicate-row map is applied.

Finite-field trace correctness and finite pattern counts are distinct from
the algorithmic construction of a polynomial presentation of the field and
the running-time proof. No balanced-family existence axiom is imported.
-/

namespace EthInapproximability.CurrentPaper.SmallBiasSampler

open scoped BigOperators Polynomial

/-- The rational additive character of the two-element field. -/
def bitSign (b : ZMod 2) : ℚ := if b = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]
@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

@[simp] theorem abs_bitSign (x : ZMod 2) : |bitSign x| = 1 := by
  unfold bitSign
  split <;> norm_num

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  have ha : a = 0 ∨ a = 1 := by fin_cases a; exact Or.inl rfl; exact Or.inr rfl
  have hb : b = 0 ∨ b = 1 := by fin_cases b; exact Or.inl rfl; exact Or.inr rfl
  have htwo : (1 : ZMod 2) + 1 = 0 := rfl
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [zero_add, add_zero, htwo, bitSign_zero, bitSign_one] <;> norm_num

theorem bitSign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    bitSign (∑ i ∈ s, f i) = ∏ i ∈ s, bitSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, bitSign_add, ih]

def bitCharacter : AddChar (ZMod 2) ℚ where
  toFun := bitSign
  map_zero_eq_one' := bitSign_zero
  map_add_eq_mul' := bitSign_add

section Trace

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]

theorem exists_trace_mul_ne_zero (a : K) (ha : a ≠ 0) :
    ∃ b : K, Algebra.trace (ZMod 2) K (a * b) ≠ 0 := by
  have htr := (traceForm_nondegenerate (ZMod 2) K).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

noncomputable def traceCharacter : AddChar K ℚ :=
  bitCharacter.compAddMonoidHom (Algebra.trace (ZMod 2) K).toAddMonoidHom

omit [Fintype K] in
@[simp] theorem traceCharacter_apply (x : K) :
    traceCharacter x = bitSign (Algebra.trace (ZMod 2) K x) := rfl

theorem traceCharacter_ne_one : (traceCharacter : AddChar K ℚ) ≠ 1 := by
  obtain ⟨b, hb⟩ := exists_trace_mul_ne_zero (1 : K) one_ne_zero
  simp only [one_mul] at hb
  intro heq
  have h := congrArg (fun f : AddChar K ℚ => f b) heq
  norm_num [traceCharacter_apply, bitSign, hb] at h

theorem sum_trace_mul [DecidableEq K] (a : K) :
    (∑ x : K, bitSign (Algebra.trace (ZMod 2) K (a * x))) =
      if a = 0 then (Fintype.card K : ℚ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    exact AddChar.sum_eq_zero_of_ne_one
      ((AddChar.IsPrimitive.of_ne_one traceCharacter_ne_one) ha)

theorem sum_trace_mul_right [DecidableEq K] (a : K) :
    (∑ x : K, bitSign (Algebra.trace (ZMod 2) K (x * a))) =
      if a = 0 then (Fintype.card K : ℚ) else 0 := by
  simpa only [mul_comm] using sum_trace_mul a

end Trace

/-- Fourier expansion of the indicator of a prescribed bit pattern. -/
theorem one_add_sign_mul (x y : ZMod 2) :
    1 + bitSign x * bitSign y = if x = y then (2 : ℚ) else 0 := by
  fin_cases x <;> fin_cases y <;> decide +kernel

theorem fourier_indicator {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c p : ι → ZMod 2) :
    (if ∀ i ∈ S, c i = p i then (2 : ℚ)^S.card else 0) =
      ∑ T ∈ S.powerset,
        bitSign (∑ i ∈ T, c i) * bitSign (∑ i ∈ T, p i) := by
  classical
  have hprod : (∏ i ∈ S, (1 + bitSign (c i) * bitSign (p i))) =
      if ∀ i ∈ S, c i = p i then (2 : ℚ)^S.card else 0 := by
    simp_rw [one_add_sign_mul]
    by_cases h : ∀ i ∈ S, c i = p i
    · rw [if_pos h]
      simp only [Finset.prod_congr rfl (fun i hi => if_pos (h i hi)), Finset.prod_const]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi, hne⟩ := h
      exact Finset.prod_eq_zero hi (if_neg hne)
  rw [← hprod, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.prod_mul_distrib, ← bitSign_sum]

noncomputable def patternMatches {Seed Bit : Type*} [Fintype Seed] [DecidableEq Bit]
    (C : Seed → Bit → ZMod 2) (S : Finset Bit) (p : Bit → ZMod 2) : Finset Seed :=
  Finset.univ.filter fun seed => ∀ i ∈ S, C seed i = p i

theorem pattern_count_identity {Seed Bit : Type*} [Fintype Seed] [DecidableEq Bit]
    (C : Seed → Bit → ZMod 2) (S : Finset Bit) (p : Bit → ZMod 2) :
    (2 : ℚ)^S.card * (patternMatches C S p).card =
      ∑ T ∈ S.powerset,
        (∑ seed, bitSign (∑ i ∈ T, C seed i)) * bitSign (∑ i ∈ T, p i) := by
  classical
  calc
    (2 : ℚ)^S.card * (patternMatches C S p).card =
        ∑ seed, if ∀ i ∈ S, C seed i = p i then (2 : ℚ)^S.card else 0 := by
      simp [patternMatches, ← Finset.sum_filter, mul_comm]
    _ = ∑ seed, ∑ T ∈ S.powerset,
        bitSign (∑ i ∈ T, C seed i) * bitSign (∑ i ∈ T, p i) := by
      apply Finset.sum_congr rfl
      intro seed hseed
      exact fourier_indicator S (C seed) p
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]

theorem smallBias_pattern_count {Seed Bit : Type*} [Fintype Seed] [DecidableEq Bit]
    (C : Seed → Bit → ZMod 2) (S : Finset Bit) (p : Bit → ZMod 2) (δ : ℚ)
    (hbias : ∀ T ∈ S.powerset, T.Nonempty →
      |∑ seed, bitSign (∑ i ∈ T, C seed i)| ≤ δ * Fintype.card Seed) :
    |(2 : ℚ)^S.card * (patternMatches C S p).card - Fintype.card Seed| ≤
      ((2 : ℚ)^S.card - 1) * δ * Fintype.card Seed := by
  classical
  let f : Finset Bit → ℚ := fun T =>
    (∑ seed, bitSign (∑ i ∈ T, C seed i)) * bitSign (∑ i ∈ T, p i)
  have hempty : (∅ : Finset Bit) ∈ S.powerset := by simp
  have hfempty : f ∅ = Fintype.card Seed := by simp [f]
  have hidentity : (2 : ℚ)^S.card * (patternMatches C S p).card - Fintype.card Seed =
      ∑ T ∈ S.powerset.erase ∅, f T := by
    rw [pattern_count_identity]
    rw [← Finset.sum_erase_add _ _ hempty]
    simp only [f, hfempty, add_sub_cancel_right]
  rw [hidentity]
  calc
    |∑ T ∈ S.powerset.erase ∅, f T| ≤
        ∑ T ∈ S.powerset.erase ∅, |f T| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S.powerset.erase ∅, δ * Fintype.card Seed := by
      apply Finset.sum_le_sum
      intro T hT
      rcases Finset.mem_erase.mp hT with ⟨hne, hsub⟩
      simpa [f, abs_mul] using hbias T hsub (Finset.nonempty_iff_ne_empty.mpr hne)
    _ = ((2 : ℚ)^S.card - 1) * δ * Fintype.card Seed := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((S.powerset.erase ∅).card : ℚ) = (2 : ℚ)^S.card - 1 := by
        rw [Finset.card_erase_of_mem hempty, Finset.card_powerset,
          Nat.cast_sub (Nat.one_le_pow S.card 2 (by decide)), Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_one]
      rw [hcard]
      ring

theorem smallBias_pattern_probability {Seed Bit : Type*} [Fintype Seed] [Nonempty Seed]
    [DecidableEq Bit] (C : Seed → Bit → ZMod 2) (S : Finset Bit) (p : Bit → ZMod 2)
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hbias : ∀ T ∈ S.powerset, T.Nonempty →
      |∑ seed, bitSign (∑ i ∈ T, C seed i)| ≤ δ * Fintype.card Seed) :
    |((patternMatches C S p).card : ℚ) / Fintype.card Seed - 1 / (2 : ℚ)^S.card| ≤ δ := by
  have hN : (0 : ℚ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hP : (0 : ℚ) < 2^S.card := by positivity
  have hNP : (0 : ℚ) < 2^S.card * Fintype.card Seed := mul_pos hP hN
  have hidentity : (2 : ℚ)^S.card * Fintype.card Seed *
      (((patternMatches C S p).card : ℚ) / Fintype.card Seed - 1 / (2 : ℚ)^S.card) =
      (2 : ℚ)^S.card * (patternMatches C S p).card - Fintype.card Seed := by
    field_simp
  have h := smallBias_pattern_count C S p δ hbias
  rw [← hidentity, abs_mul, abs_of_pos hNP] at h
  have hδN : 0 ≤ δ * (Fintype.card Seed : ℚ) := mul_nonneg hδ hN.le
  nlinarith

section Polynomial

variable (K : Type*) [Field K]

/-- The polynomial selected by a parity of distinct bit positions. -/
noncomputable def parityPolynomial {L : ℕ} (S : Finset (Fin L)) : K[X] :=
  ∑ i ∈ S, Polynomial.X ^ i.val

theorem parityPolynomial_coeff {L : ℕ} (S : Finset (Fin L)) (i : Fin L) :
    (parityPolynomial K S).coeff i.val = if i ∈ S then 1 else 0 := by
  classical
  simp only [parityPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  have hfin : ∀ j : Fin L, (i.val = j.val) ↔ i = j := fun _ => Fin.val_inj
  simp only [hfin]
  simp

theorem parityPolynomial_ne_zero {L : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty) :
    parityPolynomial K S ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  intro h
  have hc := parityPolynomial_coeff K S i
  rw [h, Polynomial.coeff_zero, if_pos hi] at hc
  exact zero_ne_one hc

theorem parityPolynomial_degree {L : ℕ} (S : Finset (Fin L)) :
    (parityPolynomial K S).natDegree ≤ L - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  simp only [Polynomial.natDegree_X_pow]
  omega

theorem parityPolynomial_eval {L : ℕ} (S : Finset (Fin L)) (y : K) :
    (parityPolynomial K S).eval y = ∑ i ∈ S, y ^ i.val := by
  simp [parityPolynomial, Polynomial.eval_finsetSum]

/-- A nonempty selected parity has at most `L-1` bad field seeds. -/
theorem parityPolynomial_root_count [Fintype K] [DecidableEq K] {L : ℕ}
    (S : Finset (Fin L)) (hS : S.Nonempty) :
    (Finset.univ.filter fun y : K => (parityPolynomial K S).eval y = 0).card ≤ L - 1 := by
  classical
  let P := parityPolynomial K S
  have hp : P ≠ 0 := parityPolynomial_ne_zero K S hS
  have hsub : (Finset.univ.filter fun y : K => P.eval y = 0) ⊆ P.roots.toFinset := by
    intro y hy
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    exact (Finset.mem_filter.mp hy).2
  calc
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ L - 1 := parityPolynomial_degree K S

end Polynomial

section Parity

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]

/-- The literal field-pair formula; exponent zero is included. -/
noncomputable def traceBits (L : ℕ) (seed : K × K) (i : Fin L) : ZMod 2 :=
  Algebra.trace (ZMod 2) K (seed.1 * seed.2 ^ i.val)

omit [Fintype K] [DecidableEq K] in
theorem traceBits_parity {L : ℕ} (S : Finset (Fin L)) (x y : K) :
    (∑ i ∈ S, traceBits K L (x, y) i) =
      Algebra.trace (ZMod 2) K (x * (parityPolynomial K S).eval y) := by
  simp only [traceBits, ← map_sum, parityPolynomial_eval, Finset.mul_sum]

/-- Exact character sum: only roots of the selected nonzero polynomial
contribute. Both components of the original field-pair seed are counted. -/
theorem traceBits_parity_sum {L : ℕ} (S : Finset (Fin L)) :
    (∑ seed : K × K, bitSign (∑ i ∈ S, traceBits K L seed i)) =
      (Fintype.card K : ℚ) *
        ((Finset.univ.filter fun y : K => (parityPolynomial K S).eval y = 0).card : ℚ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [traceBits_parity, sum_trace_mul_right]
  rw [Finset.sum_ite]
  simp
  ring

/-- The unnormalised bias bound for every nonempty parity, proved from the
trace character and the polynomial root count, not a balancedness premise. -/
theorem traceBits_smallBias {L : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty) :
    |∑ seed : K × K, bitSign (∑ i ∈ S, traceBits K L seed i)| ≤
      (L - 1 : ℕ) * (Fintype.card K : ℚ) := by
  rw [traceBits_parity_sum]
  rw [abs_of_nonneg (by positivity)]
  have hr :
      ((Finset.univ.filter fun y : K => (parityPolynomial K S).eval y = 0).card : ℚ)
        ≤ (L - 1 : ℕ) := by exact_mod_cast parityPolynomial_root_count K S hS
  nlinarith [Nat.cast_nonneg (α := ℚ) (Fintype.card K)]

end Parity

/-- Distinct field-pair seeds may produce the same word. Their two labels
must therefore be kept, not deduplicated after evaluation. -/
theorem traceBits_collision (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra (ZMod 2) K] (L : ℕ) :
    ((0 : K), (0 : K)) ≠ (0, 1) ∧
      traceBits K L (0, 0) = traceBits K L (0, 1) := by
  constructor
  · intro h
    exact zero_ne_one (congrArg Prod.snd h)
  · funext i
    simp [traceBits]

/-- The actual public degree choice for reciprocal integer bias `1/B`.
At the paper's call sites `B = d^8 * m^t`. -/
def fieldExponent (L B : ℕ) : ℕ := Nat.clog 2 (L * B)

theorem fieldExponent_pos {L B : ℕ} (h : 1 < L * B) :
    0 < fieldExponent L B := Nat.clog_pos (by omega) h

theorem field_size_window {L B : ℕ} (h : 1 < L * B) :
    L * B ≤ 2 ^ fieldExponent L B ∧ 2 ^ fieldExponent L B < 2 * L * B := by
  refine ⟨Nat.le_pow_clog (by omega) _, ?_⟩
  have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) h
  have hexp : fieldExponent L B - 1 + 1 = fieldExponent L B := by
    have := fieldExponent_pos h
    omega
  calc
    2 ^ fieldExponent L B = 2 ^ (fieldExponent L B - 1) * 2 := by
      rw [← pow_succ, hexp]
    _ < (L * B) * 2 := Nat.mul_lt_mul_of_pos_right hp (by omega)
    _ = 2 * L * B := by ring

theorem seed_size_window {L B : ℕ} (h : 1 < L * B) :
    (2 ^ fieldExponent L B) ^ 2 < 4 * L ^ 2 * B ^ 2 := by
  have hp := (field_size_window h).2
  calc
    _ < (2 * L * B) ^ 2 := Nat.pow_lt_pow_left hp (by omega)
    _ = _ := by ring

section BinaryBlocks

noncomputable section

/-- Binary blocks are interpreted as base-two digits, not quotient labels. -/
def blockAlphabetEquiv (a : ℕ) : (Fin a → ZMod 2) ≃ Fin (2 ^ a) :=
  (Equiv.piCongrRight fun _ => (ZMod.finEquiv 2).toEquiv.symm).trans
    finFunctionFinEquiv

/-- Every pair of field seeds has its own column label, including collisions
of the produced bit string. -/
def pairLabels (K : Type*) [Fintype K] : (K × K) ≃ Fin (Fintype.card K ^ 2) :=
  Fintype.equivFinOfCardEq (by simp [pow_two])

def groupBits {Seed : Type*} {q a : ℕ}
    (C : Seed → Fin (q * a) → ZMod 2) : Seed → Fin q → Fin (2 ^ a) :=
  fun seed i => blockAlphabetEquiv a (fun r => C seed (finProdFinEquiv (i, r)))

def selectedBits {q a : ℕ} (J : Finset (Fin q)) : Finset (Fin (q * a)) :=
  (J ×ˢ (Finset.univ : Finset (Fin a))).map finProdFinEquiv.toEmbedding

@[simp] theorem card_selectedBits {q a : ℕ} (J : Finset (Fin q)) :
    (selectedBits (a := a) J).card = a * J.card := by
  simp [selectedBits, Nat.mul_comm]

def bitPattern {q a : ℕ} (p : Fin q → Fin (2 ^ a)) :
    Fin (q * a) → ZMod 2 :=
  fun k => (blockAlphabetEquiv a).symm (p (finProdFinEquiv.symm k).1)
    (finProdFinEquiv.symm k).2

/-- The regrouping is a genuine equivalence on complete words. -/
def groupBitsEquiv (q a : ℕ) :
    (Fin (q * a) → ZMod 2) ≃ (Fin q → Fin (2 ^ a)) where
  toFun c i := blockAlphabetEquiv a (fun r => c (finProdFinEquiv (i, r)))
  invFun := bitPattern
  left_inv c := by
    funext k
    simp only [bitPattern, Equiv.symm_apply_apply]
    exact congrArg c (finProdFinEquiv.apply_symm_apply k)
  right_inv p := by
    funext i
    simp [bitPattern]

theorem grouped_event_iff {Seed : Type*} {q a : ℕ}
    (C : Seed → Fin (q * a) → ZMod 2) (seed : Seed)
    (J : Finset (Fin q)) (p : Fin q → Fin (2 ^ a)) :
    (∀ i ∈ J, groupBits C seed i = p i) ↔
      ∀ k ∈ selectedBits (a := a) J, C seed k = bitPattern p k := by
  constructor
  · intro h k hk
    obtain ⟨⟨i, r⟩, hir, rfl⟩ := Finset.mem_map.mp hk
    have hi : i ∈ J := (Finset.mem_product.mp hir).1
    have hh := congrArg (fun z => (blockAlphabetEquiv a).symm z r) (h i hi)
    simpa [groupBits, bitPattern] using hh
  · intro h i hi
    apply (blockAlphabetEquiv a).symm.injective
    funext r
    have hk : finProdFinEquiv (i, r) ∈ selectedBits (a := a) J := by
      exact Finset.mem_map.mpr ⟨(i, r), Finset.mem_product.mpr ⟨hi, Finset.mem_univ r⟩, rfl⟩
    simpa [groupBits, bitPattern] using h _ hk

/-- Absolute point-event discrepancy for a binary seed family. -/
def BitPatternDiscrepancy {Seed : Type*} [Fintype Seed] {n : ℕ}
    (C : Seed → Fin n → ZMod 2) (r : ℕ) (δ : ℝ) : Prop :=
  ∀ T : Finset (Fin n), T.card ≤ r → ∀ p : Fin n → ZMod 2,
    |((Finset.univ.filter (fun seed : Seed => ∀ k ∈ T, C seed k = p k)).card : ℝ)
        / (Fintype.card Seed : ℝ) - 1 / (2 : ℝ) ^ T.card| ≤ δ

theorem card_grouped_event {Seed : Type*} [Fintype Seed] {q a L : ℕ}
    (label : Fin L ≃ Seed) (C : Seed → Fin (q * a) → ZMod 2)
    (J : Finset (Fin q)) (p : Fin q → Fin (2 ^ a)) :
    (Finset.univ.filter (fun j : Fin L => ∀ i ∈ J, groupBits C (label j) i = p i)).card =
      (Finset.univ.filter (fun seed : Seed =>
        ∀ k ∈ selectedBits (a := a) J, C seed k = bitPattern p k)).card := by
  classical
  apply Finset.card_equiv label
  intro j
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    grouped_event_iff C (label j) J p

/-- Regrouping binary coordinates gives the manuscript's relative-error
balancedness. The column indices are the seeds, not distinct output values. -/
theorem balanced_of_bit_discrepancy {Seed : Type*} [Fintype Seed] {q a L t : ℕ}
    (label : Fin L ≃ Seed) (C : Seed → Fin (q * a) → ZMod 2)
    {ε δ : ℝ} (hSeed : 0 < Fintype.card Seed) (hε : 0 ≤ ε)
    (hδ : δ ≤ ε / (2 ^ a : ℕ) ^ t)
    (hbits : BitPatternDiscrepancy C (a * t) δ) :
    NPCC.IsBalancedFamily t (fun j i => groupBits C (label j) i) ε := by
  have hL : L = Fintype.card Seed := by simpa using Fintype.card_congr label
  refine ⟨by omega, ?_⟩
  intro J hJ p
  have hcard : (selectedBits (a := a) J).card ≤ a * t := by
    rw [card_selectedBits]
    exact Nat.mul_le_mul_left _ hJ
  have h := hbits (selectedBits J) hcard (bitPattern p)
  rw [card_grouped_event label C J p, hL]
  simp only [Fintype.card_fin]
  rw [card_selectedBits, pow_mul] at h
  have hden : ((2 : ℝ) ^ a) ^ J.card ≤ ((2 : ℝ) ^ a) ^ t :=
    pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hJ
  have hδ' : δ ≤ ε / ((2 : ℝ) ^ a) ^ J.card := by
    apply le_trans hδ
    push_cast
    exact div_le_div_of_nonneg_left hε (by positivity) hden
  push_cast
  exact h.trans hδ'

theorem balanced_pair_family {K : Type*} [Fintype K] {q a t : ℕ}
    (C : (K × K) → Fin (q * a) → ZMod 2) {ε δ : ℝ}
    (hK : 0 < Fintype.card K) (hε : 0 ≤ ε)
    (hδ : δ ≤ ε / (2 ^ a : ℕ) ^ t)
    (hbits : BitPatternDiscrepancy C (a * t) δ) :
    NPCC.IsBalancedFamily t
      (fun j i => groupBits C ((pairLabels K).symm j) i) ε := by
  apply balanced_of_bit_discrepancy (pairLabels K).symm C ?_ hε hδ hbits
  simpa using Nat.mul_pos hK hK

end

end BinaryBlocks

abbrev BinaryField (L B : ℕ) := GaloisField 2 (fieldExponent L B)

noncomputable instance binaryFieldFintype (L B : ℕ) : Fintype (BinaryField L B) :=
  Fintype.ofFinite _

noncomputable instance binaryFieldDecidableEq (L B : ℕ) : DecidableEq (BinaryField L B) :=
  Classical.decEq _

theorem binaryField_card {L B : ℕ} (h : 1 < L * B) :
    Fintype.card (BinaryField L B) = 2 ^ fieldExponent L B := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 (fieldExponent L B) (ne_of_gt (fieldExponent_pos h))

noncomputable def fieldPairEquiv {L B : ℕ} (h : 1 < L * B) :
    Fin ((2 ^ fieldExponent L B) ^ 2) ≃ BinaryField L B × BinaryField L B :=
  Fintype.equivOfCardEq (by simp [binaryField_card h, pow_two])

noncomputable def indexedTraceBits (L B : ℕ) (h : 1 < L * B)
    (seed : Fin ((2 ^ fieldExponent L B) ^ 2)) (i : Fin L) : ZMod 2 :=
  traceBits (BinaryField L B) L (fieldPairEquiv h seed) i

theorem indexedTraceBits_parity_sum {L B : ℕ} (h : 1 < L * B)
    (S : Finset (Fin L)) :
    (∑ seed, bitSign (∑ i ∈ S, indexedTraceBits L B h seed i)) =
      ∑ seed : BinaryField L B × BinaryField L B,
        bitSign (∑ i ∈ S, traceBits (BinaryField L B) L seed i) := by
  exact (fieldPairEquiv h).sum_comp (fun seed : BinaryField L B × BinaryField L B =>
    bitSign (∑ i ∈ S, traceBits (BinaryField L B) L seed i))

theorem indexedTraceBits_smallBias {L B : ℕ} (h : 1 < L * B)
    (S : Finset (Fin L)) (hS : S.Nonempty) :
    |∑ seed, bitSign (∑ i ∈ S, indexedTraceBits L B h seed i)| ≤
      (1 / (B : ℚ)) * Fintype.card (Fin ((2 ^ fieldExponent L B) ^ 2)) := by
  rw [indexedTraceBits_parity_sum h]
  have hB : 0 < B := by nlinarith
  have hL : 0 < L := by nlinarith
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have hsize : (L : ℚ) * B ≤ (2 : ℚ) ^ fieldExponent L B := by
    exact_mod_cast (field_size_window h).1
  have hq : (0 : ℚ) < 2 ^ fieldExponent L B := by positivity
  have hpred : ((L - 1 : ℕ) : ℚ) ≤ L := by exact_mod_cast Nat.sub_le L 1
  calc
    _ ≤ (L - 1 : ℕ) * (Fintype.card (BinaryField L B) : ℚ) :=
      traceBits_smallBias (BinaryField L B) S hS
    _ ≤ (L : ℚ) * (2 : ℚ) ^ fieldExponent L B := by
      rw [binaryField_card h, Nat.cast_pow, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_right hpred hq.le
    _ ≤ (1 / (B : ℚ)) * Fintype.card (Fin ((2 ^ fieldExponent L B) ^ 2)) := by
      simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      apply (mul_le_mul_iff_right₀ hBq).mp
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hsize hq.le]

theorem indexedTraceBits_pattern_probability {L B : ℕ} (h : 1 < L * B)
    (S : Finset (Fin L)) (p : Fin L → ZMod 2) :
    |((patternMatches (indexedTraceBits L B h) S p).card : ℚ) /
        ((2 : ℚ) ^ fieldExponent L B) ^ 2 - 1 / (2 : ℚ) ^ S.card| ≤
      1 / (B : ℚ) := by
  have hN : 0 < (2 ^ fieldExponent L B) ^ 2 := by positivity
  letI : Nonempty (Fin ((2 ^ fieldExponent L B) ^ 2)) := Fin.pos_iff_nonempty.mp hN
  simpa using smallBias_pattern_probability (indexedTraceBits L B h) S p (1 / (B : ℚ))
    (by positivity) (fun T _ hT => indexedTraceBits_smallBias h T hT)


/-- Bit discrepancy over the real field, for the literal indexed trace list. -/
theorem indexedTraceBits_discrepancy {L B : ℕ} (h : 1 < L * B) (r : ℕ) :
    BitPatternDiscrepancy (indexedTraceBits L B h) r (1 / (B : ℝ)) := by
  intro S _ p
  have hp := indexedTraceBits_pattern_probability h S p
  have hp' :
      |((patternMatches (indexedTraceBits L B h) S p).card : ℝ) /
        ((2 : ℝ) ^ fieldExponent L B) ^ 2 - 1 / (2 : ℝ) ^ S.card| ≤
      1 / (B : ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hp
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using hc
  convert hp' using 1
  simp only [patternMatches, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  congr 3
  congr 2
  ext seed
  simp only [Finset.mem_filter]

/-- Number of labelled field-pair seeds for the alphabet `Fin (2^a)`.
The natural denominator `E` gives the relative error `1/E`. -/
def samplerSize (q a t E : ℕ) : ℕ :=
  (2 ^ fieldExponent (q * a) (E * (2 ^ a) ^ t)) ^ 2

/-- The actual block-grouped finite-field sampler. It never identifies two
seed labels merely because their output words agree. -/
noncomputable def samplerFamily (q a t E : ℕ)
    (h : 1 < q * a * (E * (2 ^ a) ^ t)) :
    Fin (samplerSize q a t E) → Fin q → Fin (2 ^ a) :=
  groupBits (indexedTraceBits (q * a) (E * (2 ^ a) ^ t) h)

theorem samplerFamily_balanced {q a t E : ℕ}
    (h : 1 < q * a * (E * (2 ^ a) ^ t)) :
    NPCC.IsBalancedFamily t (samplerFamily q a t E h) (1 / (E : ℝ)) := by
  unfold samplerFamily
  apply balanced_of_bit_discrepancy (δ := 1 / ((E * (2 ^ a) ^ t : ℕ) : ℝ))
    (Equiv.refl _) (indexedTraceBits (q * a) (E * (2 ^ a) ^ t) h)
    (by simp only [Fintype.card_fin]; positivity) (by positivity)
  · push_cast
    simp only [div_div, le_refl]
  · exact indexedTraceBits_discrepancy h _

theorem samplerSize_pos (q a t E : ℕ) : 0 < samplerSize q a t E := by
  unfold samplerSize
  positivity

/-- The literal sampler has fewer than the displayed number of labels;
the bound is mathematical size, not a running-time certificate. -/
theorem samplerSize_lt {q a t E : ℕ}
    (h : 1 < q * a * (E * (2 ^ a) ^ t)) :
    samplerSize q a t E < 4 * (q * a) ^ 2 * E ^ 2 * (2 ^ a) ^ (2 * t) := by
  have hs := seed_size_window h
  simpa [samplerSize, mul_pow, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using hs

theorem balanced_pattern_occurs {Y : Type*} [DecidableEq Y] [Fintype Y]
    {q N t : ℕ} {C : Fin N → Fin q → Y} {ε : ℝ}
    (hC : NPCC.IsBalancedFamily t C ε) (hε : ε < 1)
    (hY : 0 < Fintype.card Y)
    (J : Finset (Fin q)) (hJ : J.card ≤ t) (a : Fin q → Y) :
    ∃ n : Fin N, ∀ i ∈ J, C n i = a i := by
  classical
  let E := Finset.univ.filter (fun n : Fin N => ∀ i ∈ J, C n i = a i)
  have hden : 0 < (Fintype.card Y : ℝ) ^ J.card :=
    pow_pos (by exact_mod_cast hY) _
  have hb := hC.2 J hJ a
  have hE : 0 < E.card := by
    by_contra hn
    have hz : E.card = 0 := Nat.eq_zero_of_not_pos hn
    change |(E.card : ℝ) / (N : ℝ) - 1 / (Fintype.card Y : ℝ) ^ J.card|
      ≤ ε / (Fintype.card Y : ℝ) ^ J.card at hb
    rw [hz] at hb
    norm_num only [Nat.cast_zero, zero_div, zero_sub, abs_neg] at hb
    rw [abs_of_pos (div_pos zero_lt_one hden)] at hb
    have : (1 : ℝ) ≤ ε := (div_le_div_iff_of_pos_right hden).mp hb
    linarith
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hE
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

theorem balanced_labels_ge {m q N t : ℕ} {C : Fin N → Fin q → Fin m} {ε : ℝ}
    (hC : NPCC.IsBalancedFamily t C ε) (hε : ε < 1)
    (hm : 0 < m) (ht : t ≤ q) : m ^ t ≤ N := by
  classical
  let e : Fin t → Fin q := Fin.castLE ht
  let f : Fin N → (Fin t → Fin m) := fun n i => C n (e i)
  have he : Function.Injective e := Fin.castLE_injective ht
  have hf : Function.Surjective f := by
    intro a
    let a' : Fin q → Fin m := fun i => if hi : i.val < t then a ⟨i.val, hi⟩ else ⟨0, hm⟩
    let J : Finset (Fin q) := Finset.univ.image e
    have hJ : J.card ≤ t := by
      dsimp [J]
      rw [Finset.card_image_of_injective _ he]
      simp
    obtain ⟨n, hn⟩ := balanced_pattern_occurs hC hε (by simpa using hm) J hJ a'
    refine ⟨n, funext fun i => ?_⟩
    have hi : e i ∈ J := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have h := hn (e i) hi
    simpa [f, e, a', i.isLt] using h
  have hc := Fintype.card_le_of_surjective f hf
  simpa using hc



/-- Bijective alphabet relabelling preserves every indexed pattern count. -/
theorem balanced_alphabet_equiv {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z] {q L t : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (h : NPCC.IsBalancedFamily t S ε) (e : Y ≃ Z) :
    NPCC.IsBalancedFamily t (fun j i => e (S j i)) ε := by
  refine ⟨h.1, ?_⟩
  intro J hJ a
  have hp := h.2 J hJ (fun i => e.symm (a i))
  have hc : Fintype.card Z = Fintype.card Y := (Fintype.card_congr e).symm
  simpa only [hc, e.apply_eq_iff_eq_symm_apply] using hp

theorem balanced_alphabet_equiv_iff {Y Z : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z] {q L t : ℕ} (S : Fin L → Fin q → Y) (ε : ℝ)
    (e : Y ≃ Z) :
    NPCC.IsBalancedFamily t (fun j i => e (S j i)) ε ↔
      NPCC.IsBalancedFamily t S ε := by
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using balanced_alphabet_equiv h e.symm
  · intro h
    exact balanced_alphabet_equiv h e

/-- The exact first-stage call site reads its two-symbol alphabet as Boolean. -/
theorem balanced_finTwo_to_bool {q L t : ℕ} {S : Fin L → Fin q → Fin 2} {ε : ℝ}
    (h : NPCC.IsBalancedFamily t S ε) :
    NPCC.IsBalancedFamily t (fun j i => finTwoEquiv (S j i)) ε :=
  balanced_alphabet_equiv h finTwoEquiv

/-- The same adapter accepts the literal `2^1` sampler alphabet. -/
theorem balanced_twoPowOne_to_bool {q L t : ℕ}
    {S : Fin L → Fin q → Fin (2 ^ 1)} {ε : ℝ}
    (h : NPCC.IsBalancedFamily t S ε) :
    NPCC.IsBalancedFamily t (fun j i => finTwoEquiv (S j i)) ε :=
  balanced_finTwo_to_bool h


/-- The reciprocal-error denominator at both exact-reduction call sites. -/
def exactDenominator (d : ℕ) : ℕ := d ^ 8

theorem exact_sampler_input {q a d t : ℕ} (hq : 0 < q) (ha : 0 < a)
    (hd : 2 ≤ d) : 1 < q * a * (exactDenominator d * (2 ^ a) ^ t) := by
  have hd8 : 2 ≤ d ^ 8 := by
    have hp := Nat.pow_le_pow_left hd 8
    norm_num at hp
    omega
  have hqa : 1 ≤ q * a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hp : 1 ≤ (2 ^ a) ^ t := Nat.one_le_pow _ _ (by positivity)
  unfold exactDenominator
  have hproduct := Nat.mul_le_mul hqa (Nat.mul_le_mul hd8 hp)
  norm_num at hproduct
  omega

def exactFirstSize (a t d : ℕ) : ℕ :=
  samplerSize (ExactConstruction.prefixLength a + 3) 1 t (exactDenominator d)

def exactSecondSize (a t d : ℕ) : ℕ :=
  samplerSize d a t (exactDenominator d)

/-- The first list has the actual `q₁+3` bits, including all three tails. -/
noncomputable def exactFirstFamily (a t d : ℕ) (hd : 2 ≤ d) :
    ExactConstruction.FirstFamily a (exactFirstSize a t d) :=
  fun j i => finTwoEquiv
    (samplerFamily (ExactConstruction.prefixLength a + 3) 1 t (exactDenominator d)
      (exact_sampler_input (by omega) (by omega) hd) j i)

/-- The second list is balanced on all `w=2^a` labels, before `duplicateLabel`
is applied by `ExactConstruction.secondMatrix`. -/
noncomputable def exactSecondFamily (a t d : ℕ) (ha : 0 < a) (hd : 2 ≤ d) :
    ExactConstruction.SecondFamily a d (exactSecondSize a t d) :=
  samplerFamily d a t (exactDenominator d) (exact_sampler_input (by omega) ha hd)

theorem exactFirstFamily_balanced (a t d : ℕ) (hd : 2 ≤ d) :
    NPCC.IsBalancedFamily t (exactFirstFamily a t d hd) (1 / (d : ℝ) ^ 8) := by
  simpa [exactFirstFamily, exactDenominator] using
    balanced_twoPowOne_to_bool (samplerFamily_balanced
      (exact_sampler_input (q := ExactConstruction.prefixLength a + 3) (a := 1)
        (t := t) (by omega) (by omega) hd))

theorem exactSecondFamily_balanced (a t d : ℕ) (ha : 0 < a) (hd : 2 ≤ d) :
    NPCC.IsBalancedFamily t (exactSecondFamily a t d ha hd) (1 / (d : ℝ) ^ 8) := by
  simpa [exactSecondFamily, exactDenominator] using
    samplerFamily_balanced (exact_sampler_input (q := d) (a := a) (t := t)
      (by omega) ha hd)

theorem exactFirst_width {a : ℕ} (ha : 2 ≤ a) :
    ExactConstruction.prefixLength a + 3 = 2 ^ a + 1 := by
  have := Construction.qOne_add_two a (by omega)
  change Construction.qOne a + 3 = 2 ^ a + 1
  omega

theorem exactFirstSize_lt (a t d : ℕ) (hd : 2 ≤ d) :
    exactFirstSize a t d <
      4 * (ExactConstruction.prefixLength a + 3) ^ 2 * d ^ 16 * 2 ^ (2 * t) := by
  have h := samplerSize_lt (exact_sampler_input
    (q := ExactConstruction.prefixLength a + 3) (a := 1) (t := t) (by omega) (by omega) hd)
  simpa [exactFirstSize, exactDenominator, ← pow_mul] using h

theorem exactSecondSize_lt (a t d : ℕ) (ha : 0 < a) (hd : 2 ≤ d) :
    exactSecondSize a t d < 4 * (d * a) ^ 2 * d ^ 16 * (2 ^ a) ^ (2 * t) := by
  have h := samplerSize_lt (exact_sampler_input (q := d) (a := a) (t := t) (by omega) ha hd)
  simpa [exactSecondSize, exactDenominator, ← pow_mul] using h

/-- Every length-`t` alphabet pattern occurs, hence the list has at least
`m^t` labels. This is a lower bound on the actual sampler just constructed. -/
theorem samplerSize_ge {q a t E : ℕ}
    (h : 1 < q * a * (E * (2 ^ a) ^ t)) (hE : 1 < E) (ht : t ≤ q) :
    (2 ^ a) ^ t ≤ samplerSize q a t E := by
  apply balanced_labels_ge (samplerFamily_balanced h) ?_ (by positivity) ht
  exact (div_lt_one (by exact_mod_cast (show 0 < E by omega))).mpr (by exact_mod_cast hE)

theorem exactDenominator_one_lt {d : ℕ} (hd : 2 ≤ d) : 1 < exactDenominator d := by
  have hp := Nat.pow_le_pow_left hd 8
  norm_num at hp
  change 1 < d ^ 8
  omega

theorem exactFirstSize_ge (a t d : ℕ) (hd : 2 ≤ d)
    (ht : t ≤ ExactConstruction.prefixLength a + 3) :
    2 ^ t ≤ exactFirstSize a t d := by
  simpa [exactFirstSize] using samplerSize_ge
    (exact_sampler_input (q := ExactConstruction.prefixLength a + 3) (a := 1)
      (t := t) (by omega) (by omega) hd) (exactDenominator_one_lt hd) ht

theorem exactSecondSize_ge (a t d : ℕ) (ha : 0 < a) (hd : 2 ≤ d) (ht : t ≤ d) :
    (2 ^ a) ^ t ≤ exactSecondSize a t d := by
  exact samplerSize_ge (exact_sampler_input (q := d) (a := a) (t := t)
    (by omega) ha hd) (exactDenominator_one_lt hd) ht

end EthInapproximability.CurrentPaper.SmallBiasSampler
