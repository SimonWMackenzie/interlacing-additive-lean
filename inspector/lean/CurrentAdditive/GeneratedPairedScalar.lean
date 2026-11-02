import CurrentAdditive.GeneratedPairedAliceTerminal
import Paper2.ReferenceProjectionMass

/-! One tagged-coordinate stopping bound for the actual paired source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceProjection
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Each tagged coordinate of the *unconditioned complete pair* has the
original inner-coordinate law. -/
theorem pair_tagged_coordinate_pushes (hD : 1 ≤ D)
    (b : Bool × Fin q₂) :
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).PushesTo
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      (fun z => taggedDecode src z b) := by
  intro E
  let e : Fin 1 → Bool × Fin q₂ := fun _ => b
  have he : Function.Injective e := by
    intro i j _
    fin_cases i
    fin_cases j
    rfl
  have hw := dwise_comp_injective D
    (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw)
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    (taggedDecode src) (pair_tagged_exact src) e he
  have h := hw (Finset.univ : Finset (Fin 1)) (by simpa using hD)
    (fun v => E (v ⟨0, Finset.mem_univ _⟩))
  have hprod : (FiniteLaw.pi (fun _ : (Finset.univ : Finset (Fin 1)) =>
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)).prob
      (fun v => E (v ⟨0, Finset.mem_univ _⟩)) =
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.iid 1).prob
        (fun v => E (v 0)) := by
    have hr := FiniteLaw.pi_prob_restrict
      (fun _ : Fin 1 =>
        ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      (fun i : (Finset.univ : Finset (Fin 1)) => i.val)
      Subtype.val_injective
      (fun v => E (v ⟨0, Finset.mem_univ _⟩))
    simpa only [FiniteLaw.iid] using hr.symm
  rw [hprod] at h
  simpa only [ReferenceProjectionMass.iid_one_coordinate_prob, e] using h

/-- A retained joint pair set of mass at least 49/64 supplies the
three-fifths column image required by the base profile at any one tagged
block.  The supported original γ labels are kept pointwise. -/
theorem paired_coordinate_cost
    (R₀ : X → Y → Bool) (H : ℕ) (x : ℝ)
    (hD : 1 ≤ D)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (b : Bool × Fin q₂)
    (K : Set (src.inner.Label × src.inner.Label))
    (W : Set src.gamma.Label)
    (C : Set ((Bool × Fin q₂) × src.gamma.Label))
    (hC : ∀ γ ∈ W, (b, γ) ∈ C)
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (hW : x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ W)) :
    H ≤ Compression.restrictionD
      (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))) K C := by
  classical
  let p : (src.inner.Label × src.inner.Label) → Fin q₁ × X :=
    fun z => taggedDecode src z b
  let M : (src.inner.Label × src.inner.Label) →
      ((Bool × Fin q₂) × src.gamma.Label) → Bool :=
    fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2))
  let F : src.gamma.Label → (src.inner.Label × src.inner.Label) → Bool :=
    fun γ z => M z (b, γ)
  have himage : (3/5 : ℝ) ≤
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob
        (· ∈ p '' K) := by
    have hmass := FiniteLaw.prob_le_image _ _ _
      (pair_tagged_coordinate_pushes src hD b) K
    linarith
  have hfirst := (restrictionProfile_three_levels _ _ _ _ _).mp hprofile |>.1
  have hbase : H ≤ Compression.restrictionD (A src R₀) W (p '' K) := by
    exact_mod_cast hfirst W (p '' K) hW himage
  have hproj : Compression.restrictionD (A src R₀) W (p '' K) ≤
      Compression.restrictionD F W K := by
    apply restrictionD_projected_le F (A src R₀) id p W K W
      (by intro _ h; exact h)
    intro γ _ z _
    rfl
  have htrans : Compression.restrictionD F W K =
      Compression.restrictionD (fun z γ => F γ z) K W :=
    (restrictionD_transpose F W K).symm
  have hmap : Compression.restrictionD (fun z γ => F γ z) K W ≤
      Compression.restrictionD M K C := by
    simpa only [F] using restrictionD_map_le M
      (fun z : src.inner.Label × src.inner.Label => z)
      (fun γ : src.gamma.Label => (b, γ))
      K C K W
      (by intro z hz; exact hz) hC
  exact hbase.trans (hproj.trans (htrans.le.trans hmap))

#print axioms pair_tagged_coordinate_pushes
#print axioms paired_coordinate_cost

end CurrentAdditive.DeterministicIndexedMatrix.Sources
