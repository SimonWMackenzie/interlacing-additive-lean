import CurrentAdditive.V38FixedDefectInduction
import CurrentAdditive.V38UniformFive

/-!
The selected v39 source, Appendix A `cl:defect-induction` (lines 197--317),
with exactly the two profile thresholds of `def:profile`. The v38 proof
text is identical. Small-block lower bounds are proved dependencies here;
none is an additional premise of the endpoints below.
-/

namespace Paper2.V38DefectInduction

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

section Uniform

variable [Nonempty X] [Nonempty Y]

/-- The complete fixed-4/3 induction on the actual retained uniform matrix.
The current profile has only its two source thresholds. -/
theorem defect_induction (F : X → Y → Bool) (C p a e : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (he : e ≤ 1) (ha : 2 * e ≤ a)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hnear : C ≤ ClassicalRows.restrictionCost F 1 θ (1 - δ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C : ℤ) - 1))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : NPCC.IsEquipartitionedGE R Finset.univ
      ⌈(Fintype.card X : ℝ) * (2 : ℝ) ^ a * θ⌉₊)
    (hdef : ProjectionDefect.defect (ProjectionDefect.columnDensity p K) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ +
        (e : ℝ) * (4 / 3)) :
    C + a - e ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  apply defect_induction_from_bases F C p a e θ δ hC hθ hθ1 hδ hδ1
    he ha hp hscale hnear
  · intro R₂ K₂ hmem
    apply V38UniformSmallBlockAdapter.two_block_C_of_profile F C θ
      hC hθ hprofile R₂ K₂
    norm_num at hmem ⊢
    exact hmem
  · intro R₃ K₃ hmem
    apply V38UniformSmallBlockAdapter.three_block_C_of_profile F C θ
      hC hθ hprofile R₃ K₃
    norm_num at hmem ⊢
    exact hmem
  · exact V38UniformSmallBlockAdapter.five_block_C_of_profile F C θ
      hC hθ hprofile
  · exact hK
  · exact hR
  · exact hdef

end Uniform

open RationalSeparation in
/-- The exact current-source theorem under positive rational input laws.
The retained tuples can be arbitrarily correlated; their mass is measured
under the original iid law. The conclusion concerns the same retained
Boolean matrix, by exact rational-copy communication-cost equality. -/
theorem rational_defect_induction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (C p a e : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (he : e ≤ 1) (ha : 2 * e ≤ a)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw
      θ (1 - δ) (C : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw θ ((C : ℤ) - 1))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun x => (i, x) ∈ R))
    (hdef : ProjectionDefect.defect ((ν.toFiniteLaw.iid p).prob (· ∈ K)) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ + (e : ℝ) * (4 / 3)) :
    C + a - e ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  let M := RationalSeparation.matrix μ ν F 1
  have hnear' : RestrictionLowerBound M
      (FiniteLaw.uniform (RationalSeparation.Rows μ 1))
      (FiniteLaw.uniform ν.Copies)
      θ (1 - δ) (C : ℤ) :=
    (RationalRowEstimates.matrix_lowerBound_iff μ ν F 1 θ (1 - δ) (C : ℤ)).mpr hnear
  have hfamily : C ≤ ClassicalRows.restrictionCost M 1 θ (1 - δ) := by
    have hh := ClassicalSeparation.oneCopy_family_lowerBound M θ (1 - δ) (C : ℤ)
      (by linarith) (by linarith) hnear'
    exact_mod_cast hh
  have hrows := RationalRowEstimates.lifted_selected_rows μ 1 p Finset.univ R
    ((2 : ℝ) ^ a * θ) (fun i _ => hR i)
  have hrows' : NPCC.IsEquipartitionedGE
      (RationalSeparation.liftSet (RationalSeparation.blockForget μ 1 p) R)
      Finset.univ
      ⌈(Fintype.card (RationalSeparation.Rows μ 1) : ℝ) * (2 : ℝ) ^ a * θ⌉₊ := by
    simpa only [mul_assoc] using hrows
  have hout := defect_induction M C p a e θ δ hC hθ hθ1 hδ hδ1 he ha
    hp hscale hfamily
    ((V38RestrictionProfiles.matrix_profile_iff μ ν F 1 θ ((C : ℤ) - 1)).mpr
      hprofile)
    (RationalSeparation.liftSet (RationalSeparation.blockForget μ 1 p) R)
    (RationalSeparation.liftSet (ν.forgetTuple p) K)
    (Paper2.DefectInduction.lifted_columns_nonempty ν p K hK) hrows'
    (by simpa only [Paper2.DefectInduction.lifted_columnDensity] using hdef)
  exact (RationalRowEstimates.lifted_D_eq μ ν F 1 p R K) ▸ hout

/-- The set-based version has the same pointwise retained matrix and laws;
it merely converts finite sets to the `restrictionD` interface. -/
theorem rational_defect_restriction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (C p a e : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (he : e ≤ 1) (ha : 2 * e ≤ a)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw
      θ (1 - δ) (C : ℤ))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw θ ((C : ℤ) - 1))
    (U : Set (Fin p × X)) (V : Set (Fin p → Y)) (hV : V.Nonempty)
    (hU : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun x => (i, x) ∈ U))
    (hdef : ProjectionDefect.defect ((ν.toFiniteLaw.iid p).prob (· ∈ V)) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ + (e : ℝ) * (4 / 3)) :
    C + a - e ≤ Compression.restrictionD (fullInterlace F p) U V := by
  classical
  have hK : V.toFinset.Nonempty := by
    obtain ⟨z, hz⟩ := hV
    exact ⟨z, by simpa using hz⟩
  have hout := rational_defect_induction μ ν F C p a e θ δ hC hθ hθ1
    hδ hδ1 he ha hp hscale hnear hprofile U.toFinset V.toFinset hK
    (by simpa using hU) (by simpa using hdef)
  change C + a - e ≤ Compression.restrictionD (fullInterlace F p)
    (U.toFinset : Set _) (V.toFinset : Set _) at hout
  simpa using hout

#print axioms defect_induction
#print axioms rational_defect_induction
#print axioms rational_defect_restriction

end Paper2.V38DefectInduction
