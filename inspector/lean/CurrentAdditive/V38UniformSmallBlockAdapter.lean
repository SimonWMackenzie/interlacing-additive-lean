import CurrentAdditive.V38TwoHigh

namespace Paper2.V38UniformSmallBlockAdapter

open Workspace.Types.CommComplexity Workspace.Types.Interlace

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem iid_uniform_eq_uniform (p : ℕ) :
    (FiniteLaw.uniform Y).iid p = FiniteLaw.uniform (Fin p → Y) := by
  apply FiniteLaw.eq_of_weight_eq
  funext z
  simp only [FiniteLaw.iid, FiniteLaw.uniform, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Nat.cast_pow, inv_pow]

theorem bracket_to_uniform_mass (p : ℕ) (x y : ℝ)
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y))
    (hmem : (R, K) ∈ NPCC.bracketGE X Y p x y) :
    (∀ i : Fin p, x ≤ (FiniteLaw.uniform X).prob (fun z => (i, z) ∈ R)) ∧
      y ≤ ((FiniteLaw.uniform Y).iid p).prob (· ∈ K) := by
  classical
  obtain ⟨hrows, hcols⟩ := hmem
  constructor
  · intro i
    let S : Finset X := (R.filter fun z => z.1 = i).image Prod.snd
    have hcard : S.card = (R.filter fun z => z.1 = i).card := by
      apply Finset.card_image_iff.mpr
      intro z hz w hw hzw
      have hzi : z.1 = i := (Finset.mem_filter.mp hz).2
      have hwi : w.1 = i := (Finset.mem_filter.mp hw).2
      exact Prod.ext (hzi.trans hwi.symm) hzw
    have hrow : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ S.card := by
      simpa only [hcard] using hrows i (Finset.mem_univ i)
    have hprob := (FiniteLaw.le_uniform_prob_iff S x).mpr hrow
    have hevent : ∀ z : X, z ∈ S ↔ (i, z) ∈ R := by
      intro z
      change z ∈ (R.filter fun w => w.1 = i).image Prod.snd ↔ (i, z) ∈ R
      constructor
      · intro hz
        obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz
        have hwi : w.1 = i := (Finset.mem_filter.mp hw).2
        have heq : w = (i, z) := Prod.ext hwi hwz
        simpa only [heq] using (Finset.mem_filter.mp hw).1
      · intro hz
        apply Finset.mem_image.mpr
        exact ⟨(i, z), Finset.mem_filter.mpr ⟨hz, rfl⟩, rfl⟩
    simpa only [hevent] using hprob
  · rw [iid_uniform_eq_uniform]
    apply (FiniteLaw.le_uniform_prob_iff K y).mpr
    simpa [Fintype.card_fun] using hcols

theorem finite_restrictionD_eq (p : ℕ) (F : X → Y → Bool)
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) :
    Compression.restrictionD (fullInterlace F p) (R : Set _) (K : Set _) =
      D (NPCC.subgame (fullInterlace F p) R K) := rfl

/-- The exact v38 two-block high-density theorem as a per-member finite
bound suitable for the defect induction. -/
theorem two_block_high_uniform (F : X → Y → Bool)
    (θ : ℝ) (H : ℕ) (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ (H : ℤ))
    (R : Finset (Fin 2 × X)) (K : Finset (Fin 2 → Y))
    (hmem : (R, K) ∈ NPCC.bracketGE X Y 2 (2 * θ) (9 / 25 : ℝ)) :
    H + 1 ≤ D (NPCC.subgame (fullInterlace F 2) R K) := by
  obtain ⟨hrow, hcol⟩ := bracket_to_uniform_mass 2 (2 * θ)
    (9 / 25 : ℝ) R K hmem
  have h := Paper2.V38SmallBlocks.two_block_high F
    (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ H hH hθ hp
    (R : Set _) (K : Set _) (by simpa using hrow) hcol
  rwa [finite_restrictionD_eq] at h

/-- The v38 profile at `C-1` supplies precisely the main induction's
two-block high-density bound, with no third profile rung. -/
theorem two_block_C_of_profile (F : X → Y → Bool)
    (C : ℕ) (θ : ℝ) (hC : 3 ≤ C) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C : ℤ) - 1))
    (R : Finset (Fin 2 × X)) (K : Finset (Fin 2 → Y))
    (hmem : (R, K) ∈ NPCC.bracketGE X Y 2 (2 * θ) (9 / 25 : ℝ)) :
    C ≤ D (NPCC.subgame (fullInterlace F 2) R K) := by
  have hp' : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C - 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ C), Nat.cast_one] using hp
  have h := two_block_high_uniform F θ (C - 1) (by omega) hθ hp' R K hmem
  omega

#print axioms two_block_high_uniform
#print axioms two_block_C_of_profile

end Paper2.V38UniformSmallBlockAdapter
