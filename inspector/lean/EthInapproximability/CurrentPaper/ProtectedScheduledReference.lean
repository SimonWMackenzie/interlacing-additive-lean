import EthInapproximability.CurrentPaper.ProtectedReferenceFamily
import EthInapproximability.CurrentPaper.AmplificationInnerProfiles
import EthInapproximability.CurrentPaper.ConcreteRouting

/-!
# The two reference profiles for the literal accepted construction

Source: locked v8 `A-stage4-details.tex`, `lem:paper-reference-extraction`.
The scalar projection test and the lower-level communication input are
discharged by the actual sampler, duplication counts, and accepted parameter
formulas. No protected communication profile is an input.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedScheduledReference

open scoped Classical
open Construction JointTransfer ProtectedProfiles ProtectedReferenceFamily
open Parameters AmplificationInnerProfiles NPCC
open Workspace.Types.CommComplexity Workspace.Types.Interlace

theorem copyCount_cast {k : ℕ} (hk : 5 ≤ k) :
    (HardSeed.copyCount k : ℝ) = (9 / 16 : ℝ) * 2 ^ k := by
  unfold HardSeed.copyCount
  push_cast
  rw [show k = (k - 5) + 5 by omega, pow_add]
  norm_num
  ring

/-- A `99/100` template proportion is sufficient for both the three-fifths
and three-tenths restrictions, including all integer rounding. -/
theorem selection_gate {r j : ℕ} (hj : j ≤ 1) (hr : 5 ≤ r - j)
    {lam x : ℝ} (hlam : 99 / 100 ≤ lam) (hx : x ≤ 1 / 1000) :
    HardSeed.copyCount (r - j) ≤
      ⌈((2 ^ r : ℕ) : ℝ) *
        (((((3 / 5 : ℝ) / 2 ^ j) + lam - 1) / lam) - x) / (1 - x)⌉₊ := by
  have hpos : 0 < lam := by linarith
  have hx1 : 0 < 1 - x := by linarith
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans ?_ (Nat.le_ceil _)
  rw [copyCount_cast hr]
  push_cast
  have hgap0 : (9 / 16 : ℝ) ≤ (((3 / 5 + lam - 1) / lam) - x) / (1 - x) := by
    apply (le_div_iff₀ hx1).2
    have hhat : (59 / 99 : ℝ) ≤ (3 / 5 + lam - 1) / lam := by
      apply (le_div_iff₀ hpos).2
      linarith
    nlinarith
  have hgap1 : (9 / 32 : ℝ) ≤ (((3 / 10 + lam - 1) / lam) - x) / (1 - x) := by
    apply (le_div_iff₀ hx1).2
    have hhat : (29 / 99 : ℝ) ≤ (3 / 10 + lam - 1) / lam := by
      apply (le_div_iff₀ hpos).2
      linarith
    nlinarith
  interval_cases j
  · simp only [Nat.sub_zero, pow_zero, div_one]
    have h := mul_le_mul_of_nonneg_left hgap0 (by positivity : (0 : ℝ) ≤ 2 ^ r)
    simpa only [mul_div_assoc, mul_comm] using h
  · have hr1 : r = (r - 1) + 1 := by omega
    simp only [pow_one]
    norm_num only [show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num]
    have h := mul_le_mul_of_nonneg_left hgap1 (by positivity : (0 : ℝ) ≤ 2 ^ r)
    rw [hr1, pow_succ] at h
    have hpow : (2 : ℝ) ^ r = 2 ^ (r - 1) * 2 := by
      conv_lhs => rw [hr1, pow_succ]
    rw [hpow]
    convert h using 1 <;> ring

/-- The actual two reference profiles. The graph vectors may be any legal
ones: these bounds use only the genuine reference rows and all original
columns, and hence do not depend on the source graph's YES/NO promise. -/
theorem scheduled_reference_profile (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i)
    (f : Fin i.rows → Fin i.columns → Bool)
    (hf : IsRobustAt f i.incomingDepth) (hcost : D f = i.cost)
    (v : ℕ) (hv : 0 < v) (hvE : v ≤ 2 * i.edges)
    (order : ItemOrder (4 * bins i * v) (4 * bins i * (bins i - 3)))
    (vectors : Fin (4 * bins i * v + 4 * bins i * (bins i - 3)) →
      Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i)
    (j : ℕ) (hj : j ≤ 1) :
    i.cost + firstExponent i + secondExponent i + (binExponent i - j) ≤
      Dfamily (interlaceFun
        (fun r : referenceRows (Y := Fin i.columns) (firstExponent i) (bins i) (secondWidth i) =>
          protectedMatrix f (firstExponent i) (bins i) (secondWidth i)
            (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows))
            (4 * bins i * v) (4 * bins i * (bins i - 3)) (bins_pos i)
            (scheduledFamily i ha) order vectors cap r.val) 1)
        (bracketGE
          (referenceRows (Y := Fin i.columns) (firstExponent i) (bins i) (secondWidth i))
          (ProtectedRows (bins i)
            (PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows))
            (4 * bins i * v) (4 * bins i * (bins i - 3)) (Fin i.rows))
          1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) ((3 / 5 : ℝ) / 2 ^ j)) := by
  letI : NeZero i.rows := ⟨by have := ha.1; omega⟩
  letI : NeZero i.columns := ⟨by have := ha.2.1; omega⟩
  let L := PrimeSampler.size (secondWidth i) (balanceOrder i) (firstWidth i * i.rows)
  let nv := 4 * bins i * v
  let nb := 4 * bins i * (bins i - 3)
  have hs : 0 < bins i := bins_pos i
  have hs4 : 4 ≤ bins i := by
    have h := Nat.le_of_dvd hs (sixtyfour_dvd_bins i)
    omega
  have hL : 0 < L := PrimeSampler.size_pos _ _ _
  have hnv : 0 < nv := by dsimp [nv]; positivity
  have hnb : 0 < nb := by
    dsimp [nb]
    exact Nat.mul_pos (by positivity) (by omega)
  have hTpos : 0 < (templateRows (X := Fin i.rows) (bins i) L nv nb).card := by
    rw [template_rows_card]
    exact Nat.mul_pos (Nat.mul_pos hs hL) (template_labels_pos _ _ _ _ hs hL hnv hnb)
  have hNpos : (0 : ℝ) < Fintype.card (ProtectedRows (bins i) L nv nb (Fin i.rows)) := by
    have h := (Finset.card_le_univ (templateRows (X := Fin i.rows) (bins i) L nv nb))
    exact_mod_cast (lt_of_lt_of_le hTpos h)
  have hlam : (99 / 100 : ℝ) ≤ templateFraction (X := Fin i.rows) (bins i) L nv nb := by
    have h := ConcreteRouting.actual_template_proportion i hc ha v hvE
    rw [ReceivingCapacityTemplate.fullTemplate_card hs] at h
    unfold templateFraction
    apply (le_div_iff₀ hNpos).2
    rw [template_rows_card]
    simpa only [L, nv, nb, mul_assoc] using h
  let x := (2 : ℝ) ^ (binExponent i - j) * (2 : ℝ) ^ (-(tailDepth i : ℝ))
  have hx : x ≤ 1 / 1000 := by
    have hpow : (2 : ℝ) ^ (binExponent i - j) ≤ (bins i : ℝ) := by
      simpa only [bins, Nat.cast_pow, Nat.cast_ofNat] using
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le (binExponent i) j))
    have hh := mul_le_mul_of_nonneg_right hpow
      (by positivity : 0 ≤ (2 : ℝ) ^ (-(tailDepth i : ℝ)))
    exact hh.trans ((ParameterGates.dense_tail_loss i).2.trans (by norm_num))
  have hdom : 5 ≤ binExponent i - j := by
    have := (ParameterGates.hard_seed_exponent_domains i).2.2.2
    omega
  have hg := selection_gate hj hdom hlam hx
  have hhard := scheduled_tail_hardSeed_levels i hc ha f hf hcost j (by omega)
  rw [(scheduled_second_profiles i hc ha f hf hcost).1] at hhard
  apply reference_oneCopy f (firstExponent i) (bins i) (secondWidth i) L nv nb
    hs (secondWidth_pos i) hL hnv hnb (scheduledFamily i ha) order vectors cap
    (HardSeed.copyCount_bounds hdom).1 (show 0 < x by dsimp [x]; positivity)
    (by linarith : x < 1)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _)))
    (by have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); apply (div_le_one (by positivity)).2; linarith)
    (by simpa only [bins, Nat.cast_pow, Nat.cast_ofNat] using hg)
  exact hhard

end EthInapproximability.CurrentPaper.ProtectedScheduledReference
