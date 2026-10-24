import Paper2.PairedSelectorMatrixCore

/-!
# Actual retained projections of the paired-selector matrix

Frozen v12 Section 5, `res:paired`. Each selected tagged block is an
original block, and every projected selector tuple has one retained whole
selector pair representing it. No product completion of retained events
is permitted. The final inequality returns to selector-row orientation.
-/

namespace Paper2.PairedSelectorMatrix

open Workspace.Types.CommComplexity SourceProjection

variable {W J : Type*} [Fintype W] [Fintype J] {q n : ℕ}

/-- The interlace on selected tagged blocks is realized inside the same
retained paired matrix, using joint images of whole selector pairs. -/
theorem selected_interlace_D_le (R : W → J → Bool) (e : Fin n → Block q)
    (A : Set (Selector q J)) (S : Set (Fin n × W)) (C : Set (Column q W))
    (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C) :
    Compression.restrictionD (fullInterlace R n) S (projection e '' A) ≤
      Compression.restrictionD (matrix R) A C := by
  have hh := restrictionD_projected_le (fun c z => matrix R z c)
    (fullInterlace R n) (fun a : Fin n × W => (e a.1, a.2))
    (projection e) C A S hS (fun _ _ _ _ => rfl)
  exact hh.trans_eq (restrictionD_transpose (matrix R) A C)

/-- A single actual tagged block exposes the original base matrix against
the coordinate image of retained whole selector pairs. -/
theorem coordinate_D_le (R : W → J → Bool) (b : Block q)
    (A : Set (Selector q J)) (S : Set W) (C : Set (Column q W))
    (hS : ∀ w ∈ S, (b, w) ∈ C) :
    Compression.restrictionD R S ((fun z => coordinate z b) '' A) ≤
      Compression.restrictionD (matrix R) A C := by
  have hh := restrictionD_projected_le (fun c z => matrix R z c)
    R (fun w => (b, w)) (fun z => coordinate z b) C A S hS
    (fun _ _ _ _ => rfl)
  exact hh.trans_eq (restrictionD_transpose (matrix R) A C)

end Paper2.PairedSelectorMatrix

#print axioms Paper2.PairedSelectorMatrix.selected_interlace_D_le
#print axioms Paper2.PairedSelectorMatrix.coordinate_D_le
