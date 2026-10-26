import CurrentAdditive.V39GeneratedSourceProfiles
import CurrentAdditive.V39GeneratedReference

/-! Current generated profiles on the literal finite constructor.  These
matrices use the constructor's original Fin labels and literal row/column
laws.  In particular the reference is the ordinary restriction of `src.B`.
-/

namespace CurrentAdditive.V39GeneratedActualProfiles

open Paper2 Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39GeneratedSourceBridge

variable {nx ny ni : ℕ} {L : ℕ}
  [NeZero (generatedQ₁ L)] [NeZero (generatedQ₂ L)] [NeZero (generatedS L)]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}

/-- First template evaluated from the actual retained gamma list. -/
def A
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (R : Fin nx → Fin ny → Bool) :
    Fin src.gamma.size → (Fin (generatedQ₁ L) × Fin nx) → Bool :=
  fun γ row => SourceMatrix.M₁ R row (src.gamma.decode γ)

/-- Second template evaluated from the same actual inner list. -/
def T
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (R : Fin nx → Fin ny → Bool) :
    Fin src.inner.size → (Fin (generatedQ₂ L) × Fin src.gamma.size) → Bool :=
  fun z j => A src R j.2 (src.inner.decode z j.1)

theorem A_eq
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY) (R : Fin nx → Fin ny → Bool) :
    Sources.A (toSources src) R = A src R := rfl

theorem T_eq
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY) (R : Fin nx → Fin ny → Bool) :
    Sources.T (toSources src) R = T src R := rfl

/-- The exact costs and all three profiles, with the literal constructor
laws and the ordinary entries of its actual two-family matrix. -/
def CostsAndProfiles
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (μI : PositiveRationalLaw (Fin ni)) (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (d : ℕ) : Prop :=
  D (A src R) = d+quarterCeil L ∧
  D (T src R) = d+quarterCeil L+4*L ∧
  V38RestrictionProfiles.TwoThresholdProfile (A src R)
    src.gamma.law.toFiniteLaw
    (product (uniform (generatedQ₁ L)) μX).toFiniteLaw
    ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L : ℕ) : ℤ) ∧
  V38RestrictionProfiles.TwoThresholdProfile (T src R)
    src.inner.law.toFiniteLaw
    (product (uniform (generatedQ₂ L)) src.gamma.law).toFiniteLaw
    ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L+4*L : ℕ) : ℤ) ∧
  V38RestrictionProfiles.TwoThresholdProfile
    (V39GeneratedReference.reference src R activity)
    (product src.outer.law src.gamma.law).toFiniteLaw
    (src.rowLaw (μI := μI)).toFiniteLaw
    ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L+4*L+quarterCeil L : ℕ) : ℤ)

theorem costs_and_profiles_of_tests
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (μI : PositiveRationalLaw (Fin ni)) (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (d : ℕ) (c δv ζ : ℚ) (m : ℕ) (htests : GeneratedTests c L m δv ζ)
    (hd : 2 ≤ d) (hD : D R = d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ)) :
    CostsAndProfiles src μI R activity d := by
  classical
  let ξ₀ : SourceMatrix.Tail (generatedS L) (Fin ny) :=
    fun _ => Classical.choice μY.nonempty
  have h := V39GeneratedSourceProfiles.costs_and_profiles_of_tests
    (toSources src) μI R activity ξ₀ d c δv ζ m htests hd hD hp
  simpa only [CostsAndProfiles,V39GeneratedSourceProfiles.CostsAndProfiles,A_eq,T_eq,
    V39GeneratedReference.reference_eq,V39GeneratedReference.rowLaw_eq,
    product_eq,uniform_eq] using h

/-- Actual finite constructor endpoint at the accepted explicit cutoff.
It assumes only the base matrix cost/profile, exact-list source data, and
the public scalar/graph-size hypotheses; no later profile is assumed. -/
theorem costs_and_profiles_all_large
    (src : SourceData (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (μI : PositiveRationalLaw (Fin ni)) (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (d : ℕ) (γ c : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ/(4*Δ)) (sourceZeta γ/256))/2^16)
    (hL : GeneratedCutoff.cutoffLog Δ c ≤ L) (hn : 0 < n)
    (hnN : n ≤ generatedN L) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ Δ*n)
    (hd : 2 ≤ d) (hD : D R = d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ)) :
    CostsAndProfiles src μI R activity d := by
  exact costs_and_profiles_of_tests src μI R activity d
    c (sourceDeltaV γ Δ n m) (sourceZeta γ) m
    (GeneratedCutoff.all_large_sources γ c Δ hγ hΔ hc hcmax
      L n m hL hn hnN hlow hdegree) hd hD hp

/-- The same endpoint for the three literal calls to a single exact source
operation. The physical implementation of that operation is separate. -/
theorem constructed_costs_and_profiles_all_large
    (code : CodeD 8192) (μX : PositiveRationalLaw (Fin nx))
    (μY : PositiveRationalLaw (Fin ny)) (μI : PositiveRationalLaw (Fin ni))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (d : ℕ) (γ c : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ/(4*Δ)) (sourceZeta γ/256))/2^16)
    (hL : GeneratedCutoff.cutoffLog Δ c ≤ L) (hn : 0 < n)
    (hnN : n ≤ generatedN L) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ Δ*n)
    (hd : 2 ≤ d) (hD : D R = d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ)) :
    CostsAndProfiles
      (sourceData (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
        (s := generatedS L) code μX μY) μI R activity d := by
  exact costs_and_profiles_all_large _ μI R activity d γ c Δ n m
    hγ hΔ hc hcmax hL hn hnN hlow hdegree hd hD hp

#print axioms A
#print axioms T
#print axioms A_eq
#print axioms T_eq
#print axioms CostsAndProfiles
#print axioms costs_and_profiles_of_tests
#print axioms costs_and_profiles_all_large
#print axioms constructed_costs_and_profiles_all_large

end CurrentAdditive.V39GeneratedActualProfiles
