import Paper2.RationalRowEstimates

/-!
# Exact two-threshold restriction profile of Paper 2 v38

`versions/v38/source/sections/amplifier.tex`, `def:profile`, lines 16--28.
The old `Paper2.RestrictionProfile` has a third `j=2` threshold and is
strictly stronger. This definition has exactly the source's `j=0,1` scope.
-/

namespace Paper2.V38RestrictionProfiles

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- v38 `def:profile`: a universal lower bound on actual restrictions at
column thresholds `3/5` and `3/10`, with no upper-bound requirement. -/
def TwoThresholdProfile (F : X → Y → Bool) (μX : FiniteLaw X)
    (μY : FiniteLaw Y) (θ : ℝ) (H : ℤ) : Prop :=
  ∀ j : Fin 2, RestrictionLowerBound F μX μY θ
    ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) (H - (j.val : ℤ))

/-- The two exact source thresholds, with no third case. -/
theorem twoThresholdProfile_iff (F : X → Y → Bool) (μX : FiniteLaw X)
    (μY : FiniteLaw Y) (θ : ℝ) (H : ℤ) :
    TwoThresholdProfile F μX μY θ H ↔
      RestrictionLowerBound F μX μY θ (3 / 5) H ∧
      RestrictionLowerBound F μX μY θ (3 / 10) (H - 1) := by
  constructor
  · intro h
    constructor
    · simpa [TwoThresholdProfile] using h ⟨0, by omega⟩
    · convert h ⟨1, by omega⟩ using 1; norm_num
  · rintro ⟨h0, h1⟩ j
    fin_cases j
    · simpa [TwoThresholdProfile] using h0
    · convert h1 using 1; norm_num

/-- The original positive rational laws and the actual uniform-copy matrix
have equivalent two-threshold profiles. Every threshold is transported as an
independent lower-bound assertion; no third-threshold assumption enters. -/
theorem matrix_profile_iff (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (h : ℕ+) (θ : ℝ) (H : ℤ) :
    TwoThresholdProfile (RationalSeparation.matrix μ ν F h)
      (FiniteLaw.uniform (RationalSeparation.Rows μ h))
      (FiniteLaw.uniform ν.Copies) θ H ↔
    TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ H := by
  constructor <;> intro hp j
  · exact (RationalRowEstimates.matrix_lowerBound_iff μ ν F h θ
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) (H - (j.val : ℤ))).mp (hp j)
  · exact (RationalRowEstimates.matrix_lowerBound_iff μ ν F h θ
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) (H - (j.val : ℤ))).mpr (hp j)

#print axioms twoThresholdProfile_iff
#print axioms matrix_profile_iff

end Paper2.V38RestrictionProfiles
