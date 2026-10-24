import CurrentAdditive.DeterministicSuffixLongAssembled
import CurrentAdditive.QuarticTVAdapter

/-! Appendix H's long suffix with all moment and quartic comparison
theorems applied to actual indexed columns and good original coordinates. -/

namespace CurrentAdditive.SuffixLongSource

open Paper2
open Workspace.Types.CommComplexity
open CurrentAdditive.SuffixLong

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- Exact `b≥5` source suffix. The good-marginal estimate is stated as
the paper supplies it: every at-most-eight-coordinate projection outside
the exceptional set is within ε after conditioning. -/
theorem suffix_long_of_good_tv
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {b q : ℕ} (hb : 5 ≤ b)
    (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q))
    (hGood : 2^b + 1 ≤ Good.card)
    (hGoodOutside : ∀ j ∈ Good, j ∉ E)
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
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  let e := sourceGoodSelector hb Good hGood
  have hgood (t : Fin (2 * 2^(b-1))) : e t ∉ E :=
    hGoodOutside _ (sourceGoodSelector_mem hb Good hGood t)
  exact suffix_long_of_dwise_and_quartic_tv μ ν F source hb decode hwise
    Good hGood R Y K d x v ε hd hx hscale hprofile hrow hv hv1 hY hK
    hcond hε hεcap
    (quartic_terms_of_condition_good_projection source ν.toFiniteLaw decode
      e K Y (hv.trans_le hY) E ε hgood hTV)

#print axioms suffix_long_of_good_tv

end CurrentAdditive.SuffixLongSource
