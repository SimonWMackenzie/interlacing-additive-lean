import CurrentAdditive.PrintedFieldWordChecked
import CurrentAdditive.SmallBiasStreamingIndex
import CurrentAdditive.FirstPassingTotal
import CurrentAdditive.FieldUnaryUnifiedRun

/-! Source v42 `yao:finite-field-list`, all positive word lengths and bias
exponents. All seed pairs remain distinct labels; finite-field search is
included in the physical construction clock. -/

namespace CurrentAdditive.V42FiniteFieldList

open Paper2 CurrentAdditive.SmallBias CurrentAdditive.FiniteFieldAdapter
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

set_option maxHeartbeats 1500000

/-- The source's exact integer `n 2^r`. -/
def target (n r : ℕ) : ℕ := n * 2 ^ r

/-- The least binary field degree reaching the source's target. -/
def degree (n r : ℕ) : ℕ := Nat.clog 2 (target n r)

def order (n r : ℕ) : ℕ := 2 ^ degree n r

theorem target_gt_one (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    1 < target n r := by
  have hp : 2 ≤ 2 ^ r := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr
  unfold target
  nlinarith

theorem degree_pos (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    0 < degree n r := Nat.clog_pos (by omega) (target_gt_one n r hn hr)

theorem degree_lower (n r : ℕ) : target n r ≤ order n r :=
  Nat.le_pow_clog (by omega) _

theorem degree_least (n r k : ℕ) (hk : target n r ≤ 2 ^ k) : degree n r ≤ k :=
  (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).2 hk

theorem order_lt (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    order n r < 2 * target n r := by
  have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < 2)
    (target_gt_one n r hn hr)
  have hd := degree_pos n r hn hr
  have he : degree n r - 1 + 1 = degree n r := by omega
  have hpow : order n r = 2 * 2 ^ (degree n r - 1) := by
    unfold order
    calc
      _ = 2 ^ (degree n r - 1 + 1) := by rw [he]
      _ = 2 * 2 ^ (degree n r - 1) := by rw [pow_succ]; omega
  rw [hpow]
  exact Nat.mul_lt_mul_of_pos_left hp (by omega)

instance labels_nonempty (n r : ℕ) : Nonempty (Fin ((order n r) ^ 2)) :=
  ⟨⟨0, by unfold order; positivity⟩⟩

/-- Literal executable cell function, with row-major pair labels. -/
def word (d modulus n : ℕ) : Fin ((2 ^ d) ^ 2) → Fin n → Bool :=
  fun ℓ j =>
    let xy := (printerPairLabel d).symm ℓ
    BitPrinter.bit d modulus xy.1.val xy.2.val j.val

/-- The uniformly indexed actual printed bits are small-biased once the
actual searched modulus is certified. The field is constructed here from
the polynomial; no field, basis, or desired bias is a final hypothesis. -/
theorem word_isSmallBiased (d modulus n : ℕ) (hd : 0 < d) (hn : 1 ≤ n)
    (hfirst : TrialSearch.firstPassing d = some modulus)
    (ε : ℚ) (hε : 0 < ε) (hR : (n : ℚ) / ε ≤ (2 : ℚ) ^ d) :
    IsSmallBiased (FiniteLaw.uniform (Fin ((2 ^ d) ^ 2)))
      (word d modulus n) (ε : ℝ) := by
  obtain ⟨tail, htail, hmod⟩ := TrialSearch.firstPassing_is_candidate hfirst
  have hlt : modulus < 2 ^ (d + 1) := by
    rw [hmod]
    exact monicBits_lt d tail htail
  have htop : modulus.testBit d = true := by
    rw [hmod]
    exact monicBits_topBit d tail htail
  have hmonic : (polynomial (d + 1) modulus).Monic := by
    rw [hmod]
    exact monicBits_monic d tail htail
  have hdegree : (polynomial (d + 1) modulus).natDegree = d := by
    rw [hmod]
    exact monicBits_degree d tail htail
  letI : Fact (Irreducible (polynomial (d + 1) modulus)) :=
    ⟨TrialSearch.firstPassing_correct hd hfirst⟩
  letI : Fintype (QuotientField d modulus) := quotientFintype d modulus hmonic hdegree
  letI : CharP (QuotientField d modulus) 2 := quotientCharP d modulus (Fact.out)
  let basis := fieldBasis d modulus hmonic hdegree
  let e := explicitPairVectorSeeds d (xDecode d)
    (quotientCodeEquiv d modulus hmonic hdegree)
  have hcard := quotient_card d modulus hmonic hdegree
  have hv := vectorSeedLaw_isSmallBiased basis hn ε hε
    (by simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using hR)
  have hi := uniformSmallBias_relabel e (vectorWord basis (n := n)) (ε : ℝ) hv
  have heq : word d modulus n =
      fun ℓ j => vectorWord basis (e.symm ℓ) j := by
    funext ℓ j
    let xy := (printerPairLabel d).symm ℓ
    have hs : e.symm ℓ =
        (xDecode d xy.1, quotientCodeEquiv d modulus hmonic hdegree xy.2) := by
      simp [e, explicitPairVectorSeeds, printerPairLabel, xy]
    change BitPrinter.bit d modulus xy.1.val xy.2.val j.val = _
    rw [hs]
    exact printed_bit_eq_vectorWord d modulus n hd hlt htop hmonic hdegree xy.1 xy.2 j
  rw [heq]
  exact hi

theorem source_bias (n r modulus : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hfirst : TrialSearch.firstPassing (degree n r) = some modulus) :
    IsSmallBiased (FiniteLaw.uniform (Fin ((order n r) ^ 2)))
      (word (degree n r) modulus n) ((1 / 2 : ℝ) ^ r) := by
  have hR : (n : ℚ) / (1 / 2 : ℚ) ^ r ≤ (2 : ℚ) ^ degree n r := by
    have h := degree_lower n r
    have he : (n : ℚ) / (1 / 2 : ℚ) ^ r = (target n r : ℚ) := by
      simp [target, div_eq_mul_inv]
    rw [he]
    exact_mod_cast h
  have h := word_isSmallBiased (degree n r) modulus n
    (degree_pos n r hn hr) hn hfirst ((1 / 2 : ℚ) ^ r) (by positivity) hR
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

#print axioms degree_lower
#print axioms degree_least
#print axioms order_lt
#print axioms word_isSmallBiased
#print axioms source_bias

end CurrentAdditive.V42FiniteFieldList

