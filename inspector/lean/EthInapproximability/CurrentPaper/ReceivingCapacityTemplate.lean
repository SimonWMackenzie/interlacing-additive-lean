import EthInapproximability.CurrentPaper.ProductExtraction
import EthInapproximability.CurrentPaper.JointTransfer

/-!
# Template extraction on the actual protected columns

Source: v8 `A-stage4-details.tex`, `lem:paper-uniform-protected-packet`,
the first paragraph of its proof.  Starting with actual joint surviving
columns, this file selects half the coordinates and fixes one physical
template bin per coordinate.  The retained set comes with a section into
the original joint column set, so no independent marginal completions enter.

The scalar lower bound on the physical template proportion remains explicit.
The communication lower bound and donor selection are separate consumers.
-/

noncomputable section
open scoped Classical

namespace EthInapproximability.CurrentPaper.ReceivingCapacityTemplate

open Finset Construction JointTransfer ProductExtraction

universe uX
variable {X : Type uX} [Fintype X]

/-- All physical columns lying in any ordinary template bin. -/
def fullTemplate (s L nv nb : ℕ) : Finset (ProtectedRows s L nv nb X) :=
  Finset.univ.biUnion (templateBin s L nv nb)

/-- A total physical bin classifier.  The default is used only off template. -/
def physicalBin {s L nv nb : ℕ} (hs : 0 < s)
    (y : ProtectedRows s L nv nb X) : Fin s :=
  match rawRow y with
  | .inl r => r.1
  | .inr _ => firstBin s hs

@[simp] theorem physicalBin_template {s L nv nb : ℕ} (hs : 0 < s)
    (p : Fin s) (z : Fin L) (k : TemplateLabels s L nv nb X) :
    physicalBin hs (templateEmbedding s L nv nb p (z, k)) = p := by
  simp [physicalBin]

theorem physicalBin_of_mem_templateBin {s L nv nb : ℕ} (hs : 0 < s)
    {p : Fin s} {y : ProtectedRows s L nv nb X}
    (hy : y ∈ templateBin s L nv nb p) : physicalBin hs y = p := by
  obtain ⟨⟨z, k⟩, _, rfl⟩ := Finset.mem_image.mp hy
  exact physicalBin_template hs p z k

/-- The classifier fibres in the full template are the actual physical bins. -/
theorem fullTemplate_filter_bin {s L nv nb : ℕ} (hs : 0 < s) (p : Fin s) :
    (fullTemplate (X := X) s L nv nb).filter (fun y => physicalBin hs y = p) =
      templateBin s L nv nb p := by
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hp⟩
    obtain ⟨p', _, hy'⟩ := Finset.mem_biUnion.mp hy
    have hpp : p' = p := (physicalBin_of_mem_templateBin hs hy').symm.trans hp
    simpa only [hpp] using hy'
  · intro hy
    exact ⟨Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hy⟩,
      physicalBin_of_mem_templateBin hs hy⟩

theorem fullTemplate_bin_card {s L nv nb : ℕ} (hs : 0 < s) (p : Fin s) :
    ((fullTemplate (X := X) s L nv nb).filter
      (fun y => physicalBin hs y = p)).card =
      L * Fintype.card (TemplateLabels s L nv nb X) := by
  rw [fullTemplate_filter_bin hs p, template_bin_card]

/-- The actual template population is exactly the sum of its equal bins. -/
theorem fullTemplate_card {s L nv nb : ℕ} (hs : 0 < s) :
    (fullTemplate (X := X) s L nv nb).card =
      s * (L * Fintype.card (TemplateLabels s L nv nb X)) := by
  exact ParameterizedNP.EarlyClosureBlockSelection.templateCard_eq_bins
    (physicalBin hs) (fullTemplate s L nv nb) (fullTemplate_bin_card hs)

/-- A subset of a joint template projection has a single completion section
into the original surviving columns, including all selected coordinates. -/
theorem completion_of_template_subset {C : Type*} [DecidableEq C] {u : ℕ}
    (S : Finset (Fin u → C)) (J : Finset (Fin u)) (template : Finset C)
    (T : Finset (↥J → C)) (hT : T ⊆ templateProjection J S template) :
    ∃ sigma : ↥T → ↥S, ∀ g : ↥T, ∀ i : ↥J,
      (sigma g).1 i.1 = g.1 i := by
  let sigma : ↥T → ↥S := fun g =>
    let f := projectionSection J (S.filter (fun f => ∀ i ∈ J, f i ∈ template))
      ⟨g.1, hT g.2⟩
    ⟨f.1, (Finset.mem_filter.mp f.2).1⟩
  exact ⟨sigma, fun g i => projectionSection_apply J
    (S.filter (fun f => ∀ i ∈ J, f i ∈ template)) ⟨g.1, hT g.2⟩ i⟩

/-- Extract half of the coordinates from the actual physical surviving set.
The resulting tuples lie jointly in the selected physical bins and admit
one common completion into `S`.  Density is measured in the physical bins,
before forgetting any duplication labels. -/
theorem physical_template_half_bin_extraction {s L nv nb u : ℕ}
    (hs : 0 < s) (S : Finset (Fin u → ProtectedRows s L nv nb X))
    {rho lam : ℝ} (hu : 4 ∣ u) (hu0 : 0 < u)
    (hC : 0 < Fintype.card (ProtectedRows s L nv nb X)) (hrho : 0 < rho)
    (hS : rho * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^ u ≤
      (S.card : ℝ))
    (hTemplate : lam * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ≤
      ((fullTemplate (X := X) s L nv nb).card : ℝ))
    (hgap : 1 - lam ≤ rho / 8) :
    ∃ (J : Finset (Fin u)) (p : ↥J → Fin s)
      (T : Finset (↥J → ProtectedRows s L nv nb X)),
      J.card = u / 2 ∧
      (rho / 2 ^ (u + 1)) *
          (L * Fintype.card (TemplateLabels s L nv nb X) : ℝ) ^ (u / 2) ≤
        (T.card : ℝ) ∧
      (∀ g ∈ T, ∀ i, g i ∈ templateBin s L nv nb (p i)) ∧
      ∃ sigma : ↥T → ↥S, ∀ g : ↥T, ∀ i : ↥J,
        (sigma g).1 i.1 = g.1 i := by
  obtain ⟨J, p, hJ, hdens, hmem⟩ := template_half_bin_extraction
    S (fullTemplate s L nv nb) (physicalBin hs) hs
    (fullTemplate_bin_card hs) hu hu0 hC hrho hS hTemplate hgap
  let T := binPiece (templateProjection J S (fullTemplate s L nv nb)) (physicalBin hs) p
  have hT : T ⊆ templateProjection J S (fullTemplate s L nv nb) :=
    Finset.filter_subset _ _
  refine ⟨J, p, T, hJ, ?_, ?_,
    completion_of_template_subset S J (fullTemplate s L nv nb) T hT⟩
  · simpa only [Nat.cast_mul] using hdens
  · intro g hg i
    have hm := hmem g hg i
    have : g i ∈ (fullTemplate s L nv nb).filter
        (fun y => physicalBin hs y = p i) := Finset.mem_filter.mpr hm
    rwa [fullTemplate_filter_bin hs (p i)] at this

/- The numbered version is the interface used by the physical packet lower
bound.  The total completion map has an irrelevant default outside `T`. -/
theorem physical_template_half_bin_extraction_fin {s L nv nb u : ℕ}
    (hs : 0 < s) (S : Finset (Fin u → ProtectedRows s L nv nb X))
    {rho lam : ℝ} (hu : 4 ∣ u) (hu0 : 0 < u)
    (hC : 0 < Fintype.card (ProtectedRows s L nv nb X)) (hrho : 0 < rho)
    (hS : rho * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ^ u ≤
      (S.card : ℝ))
    (hTemplate : lam * (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ≤
      ((fullTemplate (X := X) s L nv nb).card : ℝ))
    (hgap : 1 - lam ≤ rho / 8) :
    ∃ (coords : Fin (u / 2) → Fin u) (p : Fin (u / 2) → Fin s)
      (T : Finset (Fin (u / 2) → ProtectedRows s L nv nb X))
      (sigma : (Fin (u / 2) → ProtectedRows s L nv nb X) →
        Fin u → ProtectedRows s L nv nb X),
      Function.Injective coords ∧
      (rho / 2 ^ (u + 1)) *
          (L * Fintype.card (TemplateLabels s L nv nb X) : ℝ) ^ (u / 2) ≤
        (T.card : ℝ) ∧
      (∀ g ∈ T, ∀ i, g i ∈ templateBin s L nv nb (p i)) ∧
      ∀ g ∈ T, sigma g ∈ S ∧ ∀ i, sigma g (coords i) = g i := by
  obtain ⟨J, p, T, hJ, hdens, hbins, sigma, hcomp⟩ :=
    physical_template_half_bin_extraction hs S hu hu0 hC hrho hS hTemplate hgap
  let e : Fin (u / 2) ≃ ↥J :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hJ)).symm
  let coords : Fin (u / 2) → Fin u := fun i => (e i).1
  let reindex : (↥J → ProtectedRows s L nv nb X) →
      (Fin (u / 2) → ProtectedRows s L nv nb X) := fun g i => g (e i)
  have hreindex : Function.Injective reindex := by
    intro g g' h
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun h i
  let T' := T.image reindex
  let project : (Fin u → ProtectedRows s L nv nb X) →
      (Fin (u / 2) → ProtectedRows s L nv nb X) := fun g i => g (coords i)
  have hTimage : T' ⊆ S.image project := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    refine Finset.mem_image.mpr ⟨(sigma ⟨f, hf⟩).1, (sigma ⟨f, hf⟩).2, ?_⟩
    funext i
    exact hcomp ⟨f, hf⟩ (e i)
  letI : Nonempty (ProtectedRows s L nv nb X) := Fintype.card_pos_iff.mp hC
  let sectionMap := ParameterizedNP.TerminalStateRealization.imageSection
    (inferInstance : Nonempty (Fin u → ProtectedRows s L nv nb X)) S project
  refine ⟨coords, (fun i => p (e i)), T', sectionMap, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact e.injective (Subtype.ext h)
  · simpa only [T', Finset.card_image_of_injective _ hreindex] using hdens
  · intro g hg i
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
    exact hbins f hf (e i)
  · intro g hg
    have hmem := hTimage hg
    exact ⟨ParameterizedNP.TerminalStateRealization.imageSection_mem hmem,
      fun i => congrFun
        (ParameterizedNP.TerminalStateRealization.imageSection_apply hmem) i⟩

end EthInapproximability.CurrentPaper.ReceivingCapacityTemplate
