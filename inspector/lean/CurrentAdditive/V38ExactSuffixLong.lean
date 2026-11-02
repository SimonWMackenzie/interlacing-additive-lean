import CurrentAdditive.V38IndexedTwoHigh
import CurrentAdditive.PrefixSuffixGlue
import CurrentAdditive.DeterministicExactPairEightWise
import CurrentAdditive.ExactPairTail

/-! The `b≥4` exact-source suffix: four-wise Boolean pair tests and the
checked exact fourth-moment tail at the manuscript's `9/(50m)` threshold. -/

namespace V38RareBoost

open Paper2 CurrentAdditive
open CurrentAdditive.SuffixLong
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem exact_suffix_long_eight
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (hb : 4 ≤ b) (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^(b+1)*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ)/(2 : ℝ)^b ≤ source.prob (· ∈ K)) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  classical
  let m : ℕ := 2^(b-1)
  have hm : 8 ≤ m := by
    have hp : (2:ℕ)^3 ≤ 2^(b-1) :=
      pow_le_pow_right₀ (by omega) (by omega)
    norm_num at hp
    exact hp
  have htwo : 2*m = 2^b := by
    have heq : b = b-1+1 := by omega
    calc
      2*m = 2^(b-1+1) := by simp [m, pow_succ, mul_comm]
      _ = 2^b := by rw [← heq]
  have hselected : 2*m ≤ Good.card := by omega
  let e : Fin (2*m) → Fin q := selectGoodPairs Good hselected
  have he : Function.Injective e := selectGoodPairs_injective Good hselected
  have hemem (j : Fin (2*m)) : e j ∈ Good :=
    selectGoodPairs_mem Good hselected j
  have hpow : (2 : ℝ) ≤ (2 : ℝ)^(b+1) := by
    calc
      (2 : ℝ) = (2 : ℝ)^1 := by norm_num
      _ ≤ (2 : ℝ)^(b+1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have hscale2 : 2*x ≤ 1 :=
    (mul_le_mul_of_nonneg_right hpow hx.le).trans hscale
  by_cases hheavy : ∃ i : Fin m,
      (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
        (· ∈ pairImage decode e K i)
  · obtain ⟨i, hi⟩ := hheavy
    apply indexed_two_block_high μ.toFiniteLaw ν.toFiniteLaw F decode
      (fun j => e (pairPosition i j))
      (rowRectangle Good Rows) K d x hd hx hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (hemem (pairPosition i j))]
      exact (mul_le_mul_of_nonneg_right hpow hx.le).trans
        (hrow _ (hemem (pairPosition i j)))
    · simpa only [pairImage, Set.mem_image] using hi
  · have hsmall : ∀ i : Fin m,
        (boolImageLaw (ν.toFiniteLaw.iid q)
          (pairHit decode e K i)).prob (fun z => z = true) < 9/25 := by
      intro i
      have hi : (ν.toFiniteLaw.iid 2).prob
          (· ∈ pairImage decode e K i) < 9/25 := by
        exact lt_of_not_ge (fun h => hheavy ⟨i,h⟩)
      have hp := pairHit_ambient_mass ν.toFiniteLaw decode e he K i
      rw [← hp] at hi
      simpa [boolImageLaw, FiniteLaw.prob_singleton] using hi
    have htail := FourthMoment.exact_pair_tail_of_four_wise source
      (fun i s => pairHit decode e K i (decode s))
      (fun i => boolImageLaw (ν.toFiniteLaw.iid q) (pairHit decode e K i))
      (· ∈ K) hm hsmall
      (by intro s hs i; exact pairHit_of_retained decode e K i s hs)
      (by
        intro s hs E
        exact pairHit_source_four_wise_of_eight source ν.toFiniteLaw decode
          hwise e he K s hs E)
    have hden : (2 : ℝ)^b = 2*(m : ℝ) := by
      exact_mod_cast htwo.symm
    have hthreshold : (9/25 : ℝ)/(2 : ℝ)^b = 9/(50*(m : ℝ)) := by
      rw [hden]
      ring
    linarith [htail.2]

#print axioms V38RareBoost.exact_suffix_long_eight

end V38RareBoost
