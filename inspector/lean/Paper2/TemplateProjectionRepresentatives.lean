import Paper2.TemplateProjectionFibres

/-!
# Actual retained representatives for dense-alphabet projection

Frozen v12 T41, final paragraph. Every projected column is represented by an
original retained word, and different projected columns have different
representatives. The entry identity is pointwise; no fresh or independently
resampled column is substituted for an original word.
-/

namespace Paper2.TemplateProjection

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]

/-- Choose an original surviving word for each actual projected pattern. -/
noncomputable def representative (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι)
    (y : projectionSet P T J) : {w // w ∈ P} :=
  ⟨((mem_projectionSet P T J y.val).mp y.property).choose,
    ((mem_projectionSet P T J y.val).mp y.property).choose_spec.1⟩

theorem representative_mem (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι)
    (y : projectionSet P T J) : (representative P T J y).val ∈ P :=
  (representative P T J y).property

@[simp] theorem representative_coordinate (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι)
    (y : projectionSet P T J) (j : J) :
    (representative P T J y).val j.val = (y.val j).val :=
  ((mem_projectionSet P T J y.val).mp y.property).choose_spec.2 j

theorem representative_injective (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι) :
    Function.Injective (representative P T J) := by
  intro y z h
  apply Subtype.ext
  funext j
  apply Subtype.ext
  have hc := congrArg (fun w : {w // w ∈ P} => w.val j.val) h
  simpa only [representative_coordinate] using hc

/-- Literal matrix-entry equality after restricting rows to selected
coordinates and columns to original surviving representatives. -/
theorem representative_entry {X O : Type*} (F : X → Z → O)
    (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι)
    (x : X) (j : J) (y : projectionSet P T J) :
    F x ((representative P T J y).val j.val) = F x ((y.val j).val) := by
  rw [representative_coordinate]

/-- Forgetting the subtype labels gives precisely the usual image
intersection `pi_J(P) intersect T^J`. -/
theorem projectionSet_image (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι) :
    (projectionSet P T J).image (fun y j => (y j).val) =
      (P.image (fun (w : ι → Z) (j : J) => w j.val)).filter (fun y => ∀ j, y j ∈ T) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨w, hw, heq⟩ := (mem_projectionSet P T J z).mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨w, hw, funext heq⟩, ?_⟩
    intro j
    exact (z j).property
  · intro hy
    obtain ⟨hyP, hyT⟩ := Finset.mem_filter.mp hy
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hyP
    let z : J → T := fun j => ⟨y j, hyT j⟩
    apply Finset.mem_image.mpr
    refine ⟨z, (mem_projectionSet P T J z).mpr ⟨w, hw, ?_⟩, rfl⟩
    intro j
    exact congrFun heq j

end Paper2.TemplateProjection

#print axioms Paper2.TemplateProjection.representative_coordinate
#print axioms Paper2.TemplateProjection.representative_injective
#print axioms Paper2.TemplateProjection.representative_entry
#print axioms Paper2.TemplateProjection.projectionSet_image
