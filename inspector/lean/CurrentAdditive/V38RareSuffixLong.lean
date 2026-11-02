import CurrentAdditive.V38RareGoodPair
import CurrentAdditive.V38IndexedTwoHigh
import CurrentAdditive.PrefixSuffixGlue

/-!
The `b ≥ 5` branch of v38 `det:suffix`, on actual retained indexed labels.
The exceptional set is fixed before `K` is chosen. The selected heavy pair
is measured in the original product law, while `K` retains its source labels.
-/

namespace V38RareBoost

open Paper2 CurrentAdditive
open CurrentAdditive.SuffixLong
open CurrentAdditive.SuffixLongSource
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem rare_suffix_long_fixed_E
    (μ : FiniteLaw X) (ν : FiniteLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (hb : 5 ≤ b) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν)
    (Good E : Finset (Fin q))
    (hGood : 2^b + 1 ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (Rows : Fin q → Set X) (Y K : Set S)
    (d : ℕ) (x v τ : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1) * x ≤ μ.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1 / (2 : ℝ)^(b+1) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
        ν decode J ≤ V38Moments.epsilon v τ) :
    d + 1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1))
      (rowRectangle Good Rows) K := by
  let e := sourceGoodSelector hb Good hGood
  have he : Function.Injective e :=
    sourceGoodSelector_injective hb Good hGood
  have hgood (t : Fin (2*2^(b-1))) : e t ∉ E :=
    hOutside _ (sourceGoodSelector_mem hb Good hGood t)
  have hfourNat := (long_suffix_block_arithmetic b hb).2.2
  have hfour : (2 : ℝ)^(b+1) = 4 * (2^(b-1) : ℝ) := by
    exact_mod_cast hfourNat.symm
  have hcond' : 1/(4*((2^(b-1) : ℕ) : ℝ)) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y) := by
    simpa only [hfour, Nat.cast_pow] using hcond
  obtain ⟨i, hi⟩ := FiniteV35.pair_projections_good_source_epsilon
    source ν (long_suffix_block_arithmetic b hb).1 decode hwise
    e he Y K v τ hv hv1 hτ hY hK E hgood
    (by simpa only [V38Moments.epsilon_eq_old,
        FiniteV35Conditioning.paperEpsilon_eq] using hTV) hcond'
  have hpow : (2 : ℝ) ≤ (2 : ℝ)^(b+1) := by
    calc
      (2 : ℝ) = (2 : ℝ)^1 := by norm_num
      _ ≤ (2 : ℝ)^(b+1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have hr (j : Fin 2) : 2*x ≤ μ.prob
      (fun u => (e (pairPosition i j),u) ∈ rowRectangle Good Rows) := by
    have hmem := sourceGoodSelector_mem hb Good hGood (pairPosition i j)
    rw [rowRectangle_fiber Good Rows _ hmem μ]
    exact (mul_le_mul_of_nonneg_right hpow hx.le).trans
      (hrow _ hmem)
  exact indexed_two_block_high μ ν F decode
    (fun j => e (pairPosition i j))
    (rowRectangle Good Rows) K d x hd hx hprofile hr
    (by simpa only [pairImage, Set.mem_image] using hi)

#print axioms rare_suffix_long_fixed_E

end V38RareBoost
