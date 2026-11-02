import Paper2.SourcePopulation
import Paper2.SourceProfiles
import Paper2.ReferenceInitial
import Paper2.SourceProjection
import Paper2.RestorationCoverParameters

/-!
# The three-rung reference profile of the first restoration interlace

Frozen v12, Section 5, lines 488--507. The selected reference rows are
actual unrestricted rows of the retained first interlace; product columns
remain an arbitrary correlated retained event.
-/

namespace Paper2.RestorationReferenceProfile

open Workspace.Types.CommComplexity
open SourceMatrix SourceLaws SourceLawBinding SourceProfileParameters
open scoped BigOperators

noncomputable def referenceBeta (j : ℕ) : ℝ :=
  (beta j - (1 - 127 / 128)) / (127 / 128 : ℝ)

/-- The actual `g=127/128` population margin, with no qualifying-coordinate
count supplied by the caller. -/
theorem reference_population (n j : ℕ) (hn : 8 ≤ n) (hj : j ≤ 2)
    (x : ℝ) (hx : 0 ≤ x)
    (hsmall : (2 : ℝ) ^ n * x ≤ 1 / 10000) :
    (2 : ℝ) ^ n * (referenceBeta j - (2 : ℝ) ^ (n - j) * x) >
      (StrongSeed.copies (n - j) : ℝ) *
        (1 - (2 : ℝ) ^ (n - j) * x) := by
  obtain ⟨he, hu64, hu, hfour⟩ := rung_bounds n j hn hj
  have hb := beta_mul_width n j (by omega)
  have hp := copies_cast (n - j) he
  have htu : 0 ≤ (2 : ℝ) ^ (n - j) * x := mul_nonneg (by positivity) hx
  have hc : 0 ≤ (StrongSeed.copies (n - j) : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ (2 : ℝ) ^ (n - j) by positivity)
  rw [hp]
  unfold referenceBeta
  norm_num only [show (1 : ℝ) - 127 / 128 = 1 / 128 by norm_num,
    div_div_eq_mul_div, div_mul_eq_mul_div]
  nlinarith [mul_nonneg hc htu]

/-- Per-coordinate tagged mass is bounded by reference mass plus all
protected mass, using the literal original mixture law. -/
theorem tagged_le_reference {Y : Type*} [Fintype Y]
    (ν : PositiveRationalLaw Y)
    {q₁ q₂ s : ℕ} [NeZero q₂]
    (E : TaggedColumn q₁ q₂ s Y → Prop) :
    (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob E ≤
      (127 / 128 : ℝ) * (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun Z => E (.unrestricted Z)) + (1 - 127 / 128 : ℝ) := by
  rw [tagged_prob]
  have hf := (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun f => E (.fixedTail f))
  have hd := (outerLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun f => E (.diagonal f))
  nlinarith

/-- The original retained first-interlace row set contains this finite
reference-row submatrix. No surviving row is invented. -/
noncomputable def referenceRows {Y : Type*} [Fintype Y]
    {q₁ q₂ s w : ℕ}
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y)) :
    Finset (Fin w × RawColumn q₁ q₂ s Y) := by
  classical
  exact Finset.univ.filter (fun a => (a.1, .unrestricted a.2) ∈ R)

@[simp] theorem mem_referenceRows {Y : Type*} [Fintype Y]
    {q₁ q₂ s w : ℕ}
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (a : Fin w × RawColumn q₁ q₂ s Y) :
    a ∈ referenceRows R ↔ (a.1, .unrestricted a.2) ∈ R := by
  classical
  simp [referenceRows]

/-- The lower row-mass bound on the actual tagged event forces the
paper's average normalized reference mass. -/
theorem reference_row_sum {Y : Type*} [Fintype Y]
    {q₁ q₂ s w : ℕ} [NeZero q₂]
    (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y)) (β : ℝ)
    (hR : β ≤ (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R)) :
    (w : ℝ) * ((β - (1 - 127 / 128)) / (127 / 128 : ℝ)) ≤
      ∑ i : Fin w, (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun Z => (i, Z) ∈ referenceRows R) := by
  have hrow : (w : ℝ) * β ≤
      ∑ i : Fin w, (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun t => (i, t) ∈ R) := by
    rw [ReferenceInitial.firstRowLaw_prob ν hw (fun i t => (i,t) ∈ R)] at hR
    have hwR : (0 : ℝ) < w := by exact_mod_cast hw
    have h := (le_div_iff₀ hwR).mp hR
    nlinarith
  have hsum : (∑ i : Fin w, (taggedLaw ν q₁ q₂ s).toFiniteLaw.prob
      (fun t => (i,t) ∈ R)) ≤
      (127 / 128 : ℝ) * (∑ i : Fin w,
        (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
          (fun Z => (i,Z) ∈ referenceRows R)) +
        (w : ℝ) * (1 - 127 / 128 : ℝ) := by
    calc
      _ ≤ ∑ i : Fin w, ((127 / 128 : ℝ) *
          (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
            (fun Z => (i,Z) ∈ referenceRows R) +
          (1 - 127 / 128 : ℝ)) := by
            apply Finset.sum_le_sum
            intro i _
            simpa [referenceRows] using tagged_le_reference ν (fun t => (i,t) ∈ R)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  nlinarith [hrow, hsum]

/-- One actual rung of the transposed first interlace. The qualifying
coordinate injection is constructed from row mass by `SourcePopulation`;
the retained product columns may have arbitrary correlations. -/
theorem reference_rung
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (hs : 4 ≤ s)
    (H r : ℕ) (hH : 3 ≤ H) (hr : 8 ≤ r) (hw : w = 2 ^ r)
    (x θ : ℝ) (hx : 0 < x)
    (hsmall : (w : ℝ) * x ≤ 1 / 10000)
    (j : Fin 3)
    (hcolumn : (2 : ℝ) ^ (-((2 : ℝ) ^ (r - j.val) / 1024)) ≤ θ)
    (hprofile : RestrictionProfile
      (fun Z row => N base activity ξ₀ (.unrestricted Z) row)
      (rawLaw ν q₁ q₂ s).toFiniteLaw
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw x (H : ℤ))
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (K : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (hR : beta j.val ≤ (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob
      (· ∈ R))
    (hK : θ ≤ ((matrixColumnLaw μ q₁ q₂ s hs).iid w).toFiniteLaw.prob
      (· ∈ K)) :
    H + (r - j.val) ≤ Compression.restrictionD
      (fullInterlace (fun Z row => N base activity ξ₀ Z row) w) R K := by
  classical
  let rawF : RawColumn q₁ q₂ s Y →
      RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Bool :=
    fun Z row => N base activity ξ₀ (.unrestricted Z) row
  let taggedF : TaggedColumn q₁ q₂ s Y →
      RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Bool :=
    N base activity ξ₀
  let RR := referenceRows R
  let KK : Finset (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)) :=
    Finset.univ.filter (· ∈ K)
  have hwpos : 0 < w := by rw [hw]; positivity
  have hj : j.val ≤ 2 := by omega
  have ha : 4 ≤ r - j.val := (rung_bounds r j.val hr hj).1
  have hscale : (2 : ℝ) ^ (r - j.val) * x < 1 := by
    apply rung_scale_lt_one r j.val x hx.le
    have hsmall' : (w : ℝ) * x ≤ 1 / 1000 := by linarith
    simpa only [hw, Nat.cast_pow, Nat.cast_ofNat] using hsmall'
  have hrows : (w : ℝ) * referenceBeta j.val ≤
      ∑ i : Fin w, (rawLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun Z => (i,Z) ∈ RR) := by
    simpa only [RR, referenceBeta] using reference_row_sum ν hwpos R (beta j.val) hR
  have hbudget : (StrongSeed.copies (r - j.val) : ℝ) *
      (1 - (2 : ℝ) ^ (r - j.val) * x) ≤
      (w : ℝ) * (referenceBeta j.val - (2 : ℝ) ^ (r - j.val) * x) := by
    have h := reference_population r j.val hr hj x hx.le
      (by simpa only [hw, Nat.cast_pow, Nat.cast_ofNat] using hsmall)
    have hwr : (w : ℝ) = (2 : ℝ) ^ r := by exact_mod_cast hw
    rw [← hwr] at h
    exact h.le
  have hcolumns : (2 : ℝ) ^ (-((2 : ℝ) ^ (r - j.val) / 1024)) ≤
      ((matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.iid w).prob (· ∈ KK) := by
    have hk : θ ≤ ((matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.iid w).prob
        (· ∈ KK) := by
      simpa [KK, PositiveRationalLaw.toFiniteLaw_iid] using hK
    exact hcolumn.trans hk
  have hstrong := SourcePopulation.retained_interlace_bound
    (rawLaw ν q₁ q₂ s) (matrixColumnLaw μ q₁ q₂ s hs)
    rawF H (r - j.val) hH ha x (referenceBeta j.val) hx
    hscale hprofile w RR KK hrows hbudget hcolumns
  have hmaps : Compression.restrictionD (fullInterlace rawF w)
      (RR : Set _) (KK : Set _) ≤
      Compression.restrictionD (fullInterlace taggedF w) R K := by
    apply SourceProjection.restrictionD_map_le
      (fullInterlace taggedF w)
      (fun a : Fin w × RawColumn q₁ q₂ s Y =>
        (a.1, .unrestricted a.2)) id R K (RR : Set _) (KK : Set _)
    · intro a ha
      exact (mem_referenceRows R a).mp ha
    · intro y hy
      simpa [KK] using hy
  have hstrong' : H + (r - j.val) ≤
      Compression.restrictionD (fullInterlace rawF w) (RR : Set _) (KK : Set _) := by
    exact hstrong
  exact hstrong'.trans hmaps

/-- The actual first interlace, transposed, has all three weaker reference
rungs. The input profile is precisely that of the unrestricted source
population; selected-row counts and the conclusion are derived. -/
theorem reference_profile
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (hs : 4 ≤ s)
    (H r : ℕ) (hH : 3 ≤ H) (hr : 8 ≤ r) (hw : w = 2 ^ r)
    (x θ : ℝ) (hx : 0 < x)
    (hsmall : (w : ℝ) * x ≤ 1 / 10000)
    (hcolumn : ∀ j : Fin 3,
      (2 : ℝ) ^ (-((2 : ℝ) ^ (r - j.val) / 1024)) ≤ θ)
    (hprofile : RestrictionProfile
      (fun Z row => N base activity ξ₀ (.unrestricted Z) row)
      (rawLaw ν q₁ q₂ s).toFiniteLaw
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw x (H : ℤ)) :
    RestrictionProfile
      (fun K R => fullInterlace (N base activity ξ₀) w R K)
      ((matrixColumnLaw μ q₁ q₂ s hs).iid w).toFiniteLaw
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity))
      θ ((H + r : ℕ) : ℤ) := by
  intro j K R hK hR
  have hh := reference_rung μ ν base activity ξ₀ hs H r hH hr hw
    x θ hx hsmall j (hcolumn j) hprofile R K hR hK
  have ht := SourceProjection.restrictionD_transpose
    (fullInterlace (N base activity ξ₀) w) R K
  rw [ht]
  change H + (r - j.val) ≤
    Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R K at hh
  omega

/-- The public `w/4 ≥ t_*` check pays the strong-seed column threshold
at each of the three rung widths `κ=w/2^j`. -/
theorem column_threshold (Q w r : ℕ) (hQ : 0 < Q)
    (hr : 8 ≤ r) (hw : w = 2 ^ r)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (j : Fin 3) :
    (2 : ℝ) ^ (-((2 : ℝ) ^ (r - j.val) / 1024)) ≤
      RestorationCoverParameters.theta Q := by
  have hj : j.val ≤ 2 := by omega
  have hfour := (rung_bounds r j.val hr hj).2.2.2
  have hwr : (w : ℝ) = (2 : ℝ) ^ r := by exact_mod_cast hw
  have hstarR : 4 * (RestorationCoverParameters.tStar Q : ℝ) ≤ w := by
    exact_mod_cast hstar
  have hmin : 1024 * (RestorationCoverParameters.b Q + 1) ≤
      RestorationCoverParameters.tStar Q :=
    SourcePadding.le_powTwoCeil _
  have hminR : (1024 : ℝ) * (RestorationCoverParameters.b Q + 1) ≤
      RestorationCoverParameters.tStar Q := by exact_mod_cast hmin
  have hκ : (RestorationCoverParameters.b Q + 1 : ℝ) ≤
      (2 : ℝ) ^ (r - j.val) / 1024 := by
    rw [hwr] at hstarR
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)).mpr
    linarith
  calc
    _ ≤ (2 : ℝ) ^ (-(RestorationCoverParameters.b Q + 1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (1 / 2 : ℝ) ^ (RestorationCoverParameters.b Q + 1) := by
      rw [Real.rpow_neg (by norm_num)]
      have he : (RestorationCoverParameters.b Q : ℝ) + 1 =
          ((RestorationCoverParameters.b Q + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_natCast]
      rw [one_div, inv_pow]
    _ ≤ RestorationCoverParameters.theta Q :=
      (RestorationCoverParameters.half_power_lt_theta hQ).le

end Paper2.RestorationReferenceProfile

#print axioms Paper2.RestorationReferenceProfile.reference_population
#print axioms Paper2.RestorationReferenceProfile.tagged_le_reference
#print axioms Paper2.RestorationReferenceProfile.reference_row_sum
#print axioms Paper2.RestorationReferenceProfile.reference_rung
#print axioms Paper2.RestorationReferenceProfile.reference_profile
#print axioms Paper2.RestorationReferenceProfile.column_threshold
