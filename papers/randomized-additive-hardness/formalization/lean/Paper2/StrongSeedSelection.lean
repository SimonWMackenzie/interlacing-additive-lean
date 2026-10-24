import Paper2.StrongSeed
import Paper2.SourceProjection

/-!
# Strong seeds inside selected interlace blocks

Frozen v12 Section 4, `eq:product-projection` and `src:profiles`, applying
Appendix A, `cl:strong-seed` to the selected blocks.
The selected columns are the literal joint image of the original retained
tuples. A single original retained tuple represents each projected column
for every row, so no independence of the retained event is assumed.
-/

namespace Paper2.StrongSeedSelection

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y] {k q : ℕ}

def tupleProjection (e : Fin k → Fin q) (z : Fin q → Y) : Fin k → Y :=
  fun j => z (e j)

/-- Rows in the selected blocks, with their original row labels. -/
noncomputable def selectRows (e : Fin k → Fin q) (R : Finset (Fin q × X)) :
    Finset (Fin k × X) := by
  classical
  exact Finset.univ.filter (fun r => (e r.1, r.2) ∈ R)

@[simp] theorem mem_selectRows (e : Fin k → Fin q) (R : Finset (Fin q × X))
    (r : Fin k × X) : r ∈ selectRows e R ↔ (e r.1, r.2) ∈ R := by
  classical
  simp [selectRows]

/-- The joint projection, not a product of individual coordinate images. -/
noncomputable def projectColumns (e : Fin k → Fin q) (K : Finset (Fin q → Y)) :
    Finset (Fin k → Y) := by
  classical
  exact K.image (tupleProjection e)

omit [Fintype Y] in
@[simp] theorem mem_projectColumns (e : Fin k → Fin q) (K : Finset (Fin q → Y))
    (z : Fin k → Y) :
    z ∈ projectColumns e K ↔ ∃ w ∈ K, tupleProjection e w = z := by
  classical
  exact Finset.mem_image

/-- Ambient product laws give the projected event its correct marginal. -/
theorem projection_mass (ν : FiniteLaw Y) (e : Fin k → Fin q)
    (he : Function.Injective e) (K : Finset (Fin q → Y)) :
    (ν.iid q).prob (· ∈ K) ≤ (ν.iid k).prob (· ∈ projectColumns e K) := by
  have h := SourceProjection.iid_projection_mass ν e he (K : Set (Fin q → Y))
  simpa only [mem_projectColumns, Set.mem_image, Finset.mem_coe, tupleProjection]
    using h

noncomputable def retainedProjection (e : Fin k → Fin q)
    (K : Finset (Fin q → Y)) : K → projectColumns e K :=
  fun w => ⟨tupleProjection e w.val, (mem_projectColumns e K _).mpr
    ⟨w.val, w.property, rfl⟩⟩

omit [Fintype Y] in
theorem retainedProjection_surjective (e : Fin k → Fin q)
    (K : Finset (Fin q → Y)) : Function.Surjective (retainedProjection e K) := by
  rintro ⟨z, hz⟩
  obtain ⟨w, hw, heq⟩ := (mem_projectColumns e K z).mp hz
  exact ⟨⟨w, hw⟩, Subtype.ext heq⟩

/-- One actual retained tuple, reused for every selected row. -/
noncomputable def representative (e : Fin k → Fin q) (K : Finset (Fin q → Y)) :
    projectColumns e K → K :=
  Function.surjInv (retainedProjection_surjective e K)

omit [Fintype Y] in
theorem representative_projects (e : Fin k → Fin q) (K : Finset (Fin q → Y))
    (z : projectColumns e K) :
    tupleProjection e (representative e K z).val = z.val :=
  congrArg Subtype.val (Function.surjInv_eq (retainedProjection_surjective e K) z)

omit [Fintype Y] in
theorem representative_survives (e : Fin k → Fin q) (K : Finset (Fin q → Y))
    (z : projectColumns e K) : (representative e K z).val ∈ K :=
  (representative e K z).property

omit [Fintype X] [Fintype Y] in
theorem projected_entry (F : X → Y → Bool) (e : Fin k → Fin q)
    (r : Fin k × X) (w : Fin q → Y) :
    fullInterlace F q (e r.1, r.2) w =
      fullInterlace F k r (tupleProjection e w) := rfl

omit [Fintype Y] in
/-- The selected retained matrix is obtained by local input maps from the
same original retained matrix. The column representative is row-independent. -/
theorem projected_D_le (F : X → Y → Bool) (e : Fin k → Fin q)
    (R : Finset (Fin q × X)) (K : Finset (Fin q → Y)) :
    D (NPCC.subgame (fullInterlace F k) (selectRows e R) (projectColumns e K)) ≤
      D (NPCC.subgame (fullInterlace F q) R K) := by
  classical
  let rows : selectRows e R → R := fun r =>
    ⟨(e r.val.1, r.val.2), (mem_selectRows e R r.val).mp r.property⟩
  let cols : projectColumns e K → K := representative e K
  have heq : NPCC.subgame (fullInterlace F k) (selectRows e R) (projectColumns e K) =
      fun r z => NPCC.subgame (fullInterlace F q) R K (rows r) (cols z) := by
    funext r z
    change fullInterlace F k r.val z.val =
      fullInterlace F q (e r.val.1, r.val.2) (representative e K z).val
    rw [projected_entry, representative_projects]
  rw [heq]
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (NPCC.subgame (fullInterlace F q) R K) rows cols

/-- A strong seed on any sufficiently populated selected blocks lower-bounds
the original retained interlace, even when its columns are correlated. -/
theorem selected_member (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (q : ℕ) (e : Fin (StrongSeed.copies a) → Fin q) (he : Function.Injective e)
    (R : Finset (Fin q × X)) (K : Finset (Fin q → Y))
    (hR : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun x => (e i, x) ∈ R))
    (hK : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid q).prob (· ∈ K)) :
    H + a ≤ D (NPCC.subgame (fullInterlace F q) R K) := by
  have hs := StrongSeed.rational_member μ ν F H a hH ha θ hθ hscale hprofile
    (selectRows e R) (projectColumns e K)
    (by simpa only [mem_selectRows] using hR)
    (hK.trans (projection_mass ν.toFiniteLaw e he K))
  exact hs.trans (projected_D_le F e R K)

end Paper2.StrongSeedSelection
