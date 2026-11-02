import Paper2.TwoStreamObstruction
import Paper2.SourceProfilesSchedule
import Paper2.SourceProfilesOuter
import Paper2.TwoStreamMatrix

/-!
# The two-stream obstruction for the literal source interlaces

Frozen v12 Section 5, `res:two-stream`, and Section 4's raw-column law.
The ordinary column is the actual raw source column. The paired and foreign
original carriers remain explicit until a source rectangle supplies them.
-/

namespace Paper2.TwoStreamSource

open SourceMatrix SourceLaws SourceProfileParameters

variable {X Y Rw F E : Type*}
  [Fintype X] [Fintype Y] [Fintype Rw] [Fintype F] [Fintype E]
  [DecidableEq E]

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by
  unfold outerWidth
  positivity⟩

local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

/-- Literal source specialization of the original-input two-stream bound.
The four numerical assumptions are public schedule checks. In particular,
neither exact base communication cost nor a source activity/graph promise is
needed for these two restriction profiles. -/
theorem restriction_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (M : Rw → (RawColumn (width L - 2) (outerWidth L) (width L) Y ⊕ F) → Bool)
    (κF : FiniteLaw F) (κE : FiniteLaw E)
    (bin : Rw → Fin (width L))
    (selector : Rw → Template (width L - 2) (outerWidth L) X)
    (ψ : F → OuterColumn (width L - 2) (outerWidth L) (width L) Y)
    (hordinary : ∀ r c, M r (.inl c) =
      T base (selector r) (c.2 (bin r)))
    (hψ : κF.PushesTo
      (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw ψ)
    (ι : E → Rw)
    (ζ : E → Template (width L - 2) (outerWidth L) X ×
      Template (width L - 2) (outerWidth L) X)
    (hζ : κE.PushesTo
      ((templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prod
        (templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw) ζ)
    (star : Fin (width L)) (P0 : Finset E)
    (R : Set Rw)
    (O : Set (RawColumn (width L - 2) (outerWidth L) (width L) Y))
    (G : Set F)
    (hι : ∀ e ∈ P0, ι e ∈ R)
    (hstar : ∀ e ∈ P0, bin (ι e) = star ∧ selector (ι e) = (ζ e).1)
    (hforeign : ∀ e ∈ P0, ∀ f,
      M (ι e) (.inr f) = T base (ζ e).2 (ψ f))
    (hpair : 2 * width L * x L ≤
      (templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prob
        (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)))
    (hrow : ∀ i ≠ star, 2 * width L * x L ≤
      (templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prob
        (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z))
    (hretain : ∀ P' : Finset E, P' ⊆ P0 →
      SourceSupportStep.mass κE (P0 \ P') < 2 * width L * x L →
      (49 / 64 : ℝ) ≤
        ((templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prod
          (templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw).prob
            (· ∈ ζ '' (P' : Set E)))
    (ε δ : ℝ)
    (hO : 1 - ε ≤
      (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (· ∈ O))
    (hF : δ ≤ κF.prob (· ∈ G)) (hδ : δ ≤ 1)
    (hslack : 2 * outerWidth L * x L + 5 * ε + 2 / outerWidth L ≤ δ) :
    d + exponent L + outerExponent L + exponent L + 1 ≤
      Compression.restrictionD M R
        (TwoStreamInitial.retainedColumns O G) := by
  let q₁ := width L - 2
  let q₂ := outerWidth L
  let s := width L
  let A : Word q₁ s Y → InnerRow q₁ X → Bool := fun γ r => M₁ base r γ
  let μA : PositiveRationalLaw (Word q₁ s Y) := ν.iid (q₁ + s + 1)
  let νA : PositiveRationalLaw (InnerRow q₁ X) :=
    (PositiveRationalLaw.uniform (Fin q₁)).prod μ
  have ha : 2 ≤ exponent L := le_trans (by decide) (exponent_ge L)
  have hb : 2 ≤ outerExponent L := by unfold outerExponent; omega
  have hprofile : RestrictionProfile
      (T (q₁ := q₁) (q₂ := q₂) (s := s) base)
      (templateLaw μ q₁ q₂).toFiniteLaw
      (outerLaw ν q₁ q₂ s).toFiniteLaw
      (x L) ((d + exponent L + outerExponent L : ℕ) : ℤ) :=
    SourceProfilesOuter.outer_profile μ ν base q₁ q₂ s d
      (exponent L) (outerExponent L) hd ha hb (rho L) (x L)
      (SourceProfilesSchedule.inner_guards L hinner)
      (SourceProfilesSchedule.outer_guards L houter hwide) hp
  have hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 8 := by
    linarith only [href]
  have hbound := TwoStreamObstruction.restriction_lower
    μA νA A M
    (d + exponent L) (outerExponent L) (exponent L)
    (by omega) (by rfl) (by rfl) (x L) (x_pos L)
    (SourceProfilesInner.inner_profile μ ν base q₁ s d (exponent L)
      hd ha (rho L) (x L)
      (SourceProfilesSchedule.inner_guards L hinner) hp)
    (by exact hprofile)
    (rawLaw ν q₁ q₂ s).toFiniteLaw κF κE bin selector
    (fun Z => Z.2) ψ
    (by exact hordinary)
    (by exact TwoStreamMatrix.raw_joint_pushes ν q₁ q₂ s)
    (by exact hψ)
    ι ζ
    (by exact hζ)
    star P0 R O G hι hstar
    (by exact hforeign)
    (by exact hpair)
    (by exact hrow)
    (by exact hretain)
    ε δ hO hF hδ hslack hsmall
  simpa only [Nat.add_assoc] using hbound

end Paper2.TwoStreamSource

#print axioms Paper2.TwoStreamSource.restriction_lower
