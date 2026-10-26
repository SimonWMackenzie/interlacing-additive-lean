import CurrentAdditive.DeterministicSuffixLong

/-! Private v27 Appendix H `det:suffix`, exact `b≥5` source-parameter
wrapper. The three moment premises remain explicit, matching the checked
`suffix_many_from_moments_1024` theorem. -/

namespace CurrentAdditive.SuffixLongSource

open Paper2
open Workspace.Types.CommComplexity
open CurrentAdditive.SuffixLong

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- The first `2^b` distinct coordinates from a retained good set of at
least `2^b+1` original blocks. This defines the precise `m=2^(b−1)` pairs
used in the long suffix. -/
def sourceGoodSelector {b q : ℕ} (hb : 5 ≤ b)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card) :
    Fin (2 * 2^(b-1)) → Fin q :=
  selectGoodPairs Good (by
    have htwo := (long_suffix_block_arithmetic b hb).2.1
    omega)

theorem sourceGoodSelector_injective {b q : ℕ} (hb : 5 ≤ b)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card) :
    Function.Injective (sourceGoodSelector hb Good hGood) := by
  exact selectGoodPairs_injective Good _

theorem sourceGoodSelector_mem {b q : ℕ} (hb : 5 ≤ b)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (j : Fin (2 * 2^(b-1))) :
    sourceGoodSelector hb Good hGood j ∈ Good :=
  selectGoodPairs_mem Good _ j

/-- The manuscript's original row threshold implies the two-copy row
threshold on every selected pair. -/
private theorem selected_row_two {b q : ℕ} (hb : 5 ≤ b)
    (x : ℝ) (hx : 0 < x)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (μ : PositiveRationalLaw X) (R : Set (Fin q × X))
    (hrow : ∀ j ∈ Good, (2 : ℝ) ^ (b+1) * x ≤
      μ.toFiniteLaw.prob (fun a => (j,a) ∈ R))
    (j : Fin (2 * 2^(b-1))) :
    2*x ≤ μ.toFiniteLaw.prob
      (fun a => (sourceGoodSelector hb Good hGood j,a) ∈ R) := by
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (b+1) := by
    calc
      (2 : ℝ) = (2 : ℝ)^1 := by norm_num
      _ ≤ (2 : ℝ) ^ (b+1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hmul := mul_le_mul_of_nonneg_right hpow hx.le
  exact hmul.trans (hrow _ (sourceGoodSelector_mem hb Good hGood j))

/-- Exact paper `b≥5` suffix wrapper. It consumes actual good blocks,
the paper's row/column thresholds, and the three separately tracked
moment inputs. The conclusion is a protocol lower bound on original
indexed source columns. -/
theorem suffix_long_source
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {b q : ℕ} (hb : 5 ≤ b)
    (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x v ε : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ) ^ (b+1) * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j ∈ Good, (2 : ℝ) ^ (b+1) * x ≤
      μ.toFiniteLaw.prob (fun a => (j,a) ∈ R))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1 / (2 : ℝ) ^ (b+1) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ) ^ (-20 : ℤ) / 1024 * v ^ ((1 : ℝ) / 256))
    (hcross : FourthMoment.PairCrossMoments (ν.toFiniteLaw.iid q)
      (centeredPairAmbient ν.toFiniteLaw decode
        (sourceGoodSelector hb Good hGood) K))
    (hterms : ∀ i j k l : Fin (2^(b-1)),
      FourthMoment.expect
        (conditionedIndexedLaw source Y (hv.trans_le hY))
        (fun s => centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K l (decode s) *
          centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K k (decode s) *
          centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K j (decode s) *
          centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K i (decode s)) ≤
      FourthMoment.expect (ν.toFiniteLaw.iid q)
        (fun c => centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K l c *
          centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K k c *
          centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K j c *
          centeredPairAmbient ν.toFiniteLaw decode
            (sourceGoodSelector hb Good hGood) K i c) + 2 * ε)
    (hHighMoment : sourceMoment source
      (centeredPairSourceSum ν.toFiniteLaw decode
        (sourceGoodSelector hb Good hGood) K) 1024 ≤
      2 * (256 * ((2^(b-1) : ℕ) : ℝ)) ^ (512 : ℕ)) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  have harith := long_suffix_block_arithmetic b hb
  have hm : 16 ≤ 2^(b-1) := harith.1
  have he := sourceGoodSelector_injective hb Good hGood
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ (b+1) := by
    calc
      (2 : ℝ) = (2 : ℝ)^1 := by norm_num
      _ ≤ (2 : ℝ) ^ (b+1) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hscale2 : 2*x ≤ 1 :=
    (mul_le_mul_of_nonneg_right hpow hx.le).trans hscale
  have hcond2 : 1 / (4 * ((2^(b-1) : ℕ) : ℝ)) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y) := by
    have hden : (4 : ℝ) * ((2^(b-1) : ℕ) : ℝ) =
        (2 : ℝ) ^ (b+1) := by
      exact_mod_cast harith.2.2
    rw [hden]
    exact hcond
  exact suffix_many_from_moments_1024 μ ν F source hm decode
    (sourceGoodSelector hb Good hGood) he R Y K d x v ε hd hx hscale2
    hprofile (fun j => selected_row_two hb x hx Good hGood μ R hrow j)
    hv hv1 hY hK hcond2 hε hεcap hcross hterms hHighMoment

#print axioms sourceGoodSelector_injective
#print axioms suffix_long_source

end CurrentAdditive.SuffixLongSource
