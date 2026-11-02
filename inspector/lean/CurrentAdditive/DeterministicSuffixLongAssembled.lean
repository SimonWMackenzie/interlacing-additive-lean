import CurrentAdditive.DeterministicPairHighMoment

/-! Appendix H exact long suffix after the ambient product and source high
moment bridges. The good-marginal conditional quartic comparison is the
remaining explicit premise. -/

namespace CurrentAdditive.SuffixLongSource

open Paper2
open Workspace.Types.CommComplexity
open CurrentAdditive.SuffixLong

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- Literal `b≥5` source branch, with independent-stream and product-law
moments proved from the actual selected original coordinates. -/
theorem suffix_long_of_dwise_and_quartic_tv
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {b q : ℕ} (hb : 5 ≤ b)
    (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
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
            (sourceGoodSelector hb Good hGood) K i c) + 2 * ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  let e := sourceGoodSelector hb Good hGood
  have he : Function.Injective e := sourceGoodSelector_injective hb Good hGood
  exact suffix_long_source μ ν F source hb decode Good hGood R Y K
    d x v ε hd hx hscale hprofile hrow hv hv1 hY hK hcond hε hεcap
    (pairHit_product_cross ν.toFiniteLaw decode e he K)
    hterms
    (pairHit_source_high_moment source ν.toFiniteLaw decode hwise e he K)

#print axioms suffix_long_of_dwise_and_quartic_tv

end CurrentAdditive.SuffixLongSource
