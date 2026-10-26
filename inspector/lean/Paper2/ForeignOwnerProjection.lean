import Paper2.SourceProjectionRetention
import Paper2.TwoStreamSource

/-!
# Original-column pair projections for a foreign owner

Frozen v12 Section 5, `res:foreign`, lines 388--446. The paired carrier is
the product of actual selector templates. Original correlated product
columns supply its retained image and chosen representatives; they do not
become its ambient law.
-/

namespace Paper2.ForeignOwnerProjection

open SourceMatrix SourceLaws SourceLawBinding

variable {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
  {q₁ q₂ s w : ℕ} [NeZero q₁]

abbrev K (V X : Type*) (q₁ q₂ s : ℕ) :=
  RawRow q₁ q₂ s X (SourceConstruction.Items s V)

/-- The actual pair labels exposed by a possibly correlated set of original
columns. Both bin tests concern the same original tuple. -/
def pairImage (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p r : Fin s) :
    Set (Template q₁ q₂ X × Template q₁ q₂ X) :=
  fun z => ∃ y ∈ U, y i = .inl (p, z.1) ∧ y j = .inl (r, z.2)

/-- A pair label in the image has one *original* surviving completion. -/
noncomputable def pairRepresentative
    (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p r : Fin s)
    (z : pairImage U i j p r) : Fin w → K V X q₁ q₂ s :=
  Classical.choose z.property

theorem pairRepresentative_survives
    (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p r : Fin s)
    (z : pairImage U i j p r) :
    pairRepresentative U i j p r z ∈ U :=
  (Classical.choose_spec z.property).1

theorem pairRepresentative_coordinates
    (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p r : Fin s)
    (z : pairImage U i j p r) :
    (pairRepresentative U i j p r z) i = .inl (p, z.val.1) ∧
      (pairRepresentative U i j p r z) j = .inl (r, z.val.2) :=
  (Classical.choose_spec z.property).2

theorem pairRepresentative_injective
    (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p r : Fin s) :
    Function.Injective (pairRepresentative U i j p r) := by
  intro z z' h
  apply Subtype.ext
  have hi := (pairRepresentative_coordinates U i j p r z).1
  have hj := (pairRepresentative_coordinates U i j p r z).2
  have hi' := (pairRepresentative_coordinates U i j p r z').1
  have hj' := (pairRepresentative_coordinates U i j p r z').2
  rw [h] at hi hj
  apply Prod.ext
  · exact (Prod.mk.inj (Sum.inl.inj (hi.symm.trans hi'))).2
  · exact (Prod.mk.inj (Sum.inl.inj (hj.symm.trans hj'))).2

/-- The same chosen original completion gives all three source entry
identities. In the fixed-tail case the foreign copy reads its own fixed
bin `r`, not the owner's distinguished bin `p`. -/
theorem pairRepresentative_entries {Y : Type*} [NeZero s]
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p r : Fin s)
    (z : pairImage U i j p r) :
    (∀ Z : RawColumn q₁ q₂ s Y,
      N base activity ξ₀ (.unrestricted Z)
        ((pairRepresentative U i j p r z) i) = T base z.val.1 (Z.2 p)) ∧
    (∀ f : Fin s → OuterColumn q₁ q₂ s Y,
      N base activity ξ₀ (.fixedTail f)
        ((pairRepresentative U i j p r z) j) = T base z.val.2 (f r)) ∧
    (∀ f : OuterColumn q₁ q₂ s Y,
      N base activity ξ₀ (.diagonal f)
        ((pairRepresentative U i j p r z) j) = T base z.val.2 f) := by
  rcases pairRepresentative_coordinates U i j p r z with ⟨hi,hj⟩
  constructor
  · intro Z
    rw [hi]
    rfl
  constructor
  · intro f
    rw [hj]
    rfl
  · intro f
    rw [hj]
    rfl

/-- The ambient pair law is the product-template law, with identity map.
The loss is measured on pair labels, not on selected completions. -/
theorem pair_retention [DecidableEq X]
    (σ : FiniteLaw (Template q₁ q₂ X))
    (P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X))
    (a τ : ℝ)
    (hinitial : a ≤ (σ.prod σ).prob (· ∈ (P0 : Set _)))
    (hmargin : 49 / 64 + τ < a) :
    ∀ P' : Finset (Template q₁ q₂ X × Template q₁ q₂ X),
      P' ⊆ P0 → SourceSupportStep.mass (σ.prod σ) (P0 \ P') < τ →
      (49 / 64 : ℝ) ≤ (σ.prod σ).prob (· ∈ (P' : Set _)) := by
  classical
  intro P' hsub hloss
  have hsplit : SourceSupportStep.mass (σ.prod σ) (P0 \ P') +
      SourceSupportStep.mass (σ.prod σ) P' =
      SourceSupportStep.mass (σ.prod σ) P0 := by
    unfold SourceSupportStep.mass FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ P'
    · have hp := hsub hz
      simp [hz, hp]
    · by_cases hp : z ∈ P0 <;> simp [hz, hp]
  change _ + (σ.prod σ).prob (· ∈ (P' : Set _)) =
    (σ.prod σ).prob (· ∈ (P0 : Set _)) at hsplit
  linarith

/-- The actual graph-source law has the advertised atom weight in each
fixed template bin; this is not a law imposed on the retained set. -/
theorem template_atom_weight (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (p : Fin s) (z : Template q₁ q₂ X) :
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.weight (.inl (p,z)) =
      (255 / 256 : ℝ) * (s : ℝ)⁻¹ *
        (templateLaw μ q₁ q₂).toFiniteLaw.weight z := by
  classical
  have h := column_template_bin_law (V := V) μ hs p (fun t => t = z)
  simp [FiniteLaw.prob, SourceLawBinding.templateBinEvent,
    Fintype.sum_sum_type, Fintype.sum_prod_type] at h
  have hsum :
      (∑ a : Fin s, ∑ b : Template q₁ q₂ X,
        @ite ℝ (a = p ∧ b = z) (Classical.propDecidable _)
          ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.weight (.inl (a,b)))
          0) =
      (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.weight (.inl (p,z)) := by
    classical
    calc
      _ = ∑ a : Fin s, if a = p then
          (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.weight (.inl (a,z))
          else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a = p <;> simp [ha]
      _ = _ := by simp
  calc
    _ = (∑ a : Fin s, ∑ b : Template q₁ q₂ X,
          @ite ℝ (a = p ∧ b = z) (Classical.propDecidable _)
            ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.weight (.inl (a,b)))
            0) := hsum.symm
    _ = (255 / 256 : ℝ) * (s : ℝ)⁻¹ *
        (∑ b : Template q₁ q₂ X,
          @ite ℝ (b = z) (Classical.propDecidable _)
            ((templateLaw μ q₁ q₂).toFiniteLaw.weight b) 0) := h
    _ = _ := by
      congr 1
      have hs :
          (∑ b : Template q₁ q₂ X,
            @ite ℝ (b = z) (Classical.propDecidable _)
              ((templateLaw μ q₁ q₂).toFiniteLaw.weight b) 0) =
          @ite ℝ (z = z) (Classical.propDecidable _)
            ((templateLaw μ q₁ q₂).toFiniteLaw.weight z) 0 := by
        apply Finset.sum_eq_single z
        · intro b _ hb
          simp [hb]
        · simp
      simpa using hs

/-- The part of a two-coordinate event lying in two template bins is
measured in the original product law, then decomposed into its exact
uniform-bin/product-template components. -/
theorem template_pair_prob (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (B : Set (K V X q₁ q₂ s × K V X q₁ q₂ s)) :
    let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
    let σ := (templateLaw μ q₁ q₂).toFiniteLaw
    (χ.prod χ).prob (fun k =>
      match k with
      | (.inl _, .inl _) => k ∈ B
      | _ => False) =
      ((255 / 256 : ℝ) * (s : ℝ)⁻¹) ^ 2 *
        ∑ p : Fin s, ∑ r : Fin s,
          (σ.prod σ).prob (fun z => ((.inl (p,z.1), .inl (r,z.2)) :
            K V X q₁ q₂ s × K V X q₁ q₂ s) ∈ B) := by
  classical
  dsimp
  simp only [FiniteLaw.prob, FiniteLaw.prod, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp only [template_atom_weight (V := V) μ hs]
  simp [Finset.mul_sum, pow_two]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro z' _
  split_ifs <;> ring

private theorem prob_inter_lower {A : Type*} [Fintype A]
    (κ : FiniteLaw A) (E T : A → Prop) :
    κ.prob E + κ.prob T - 1 ≤ κ.prob (fun a => E a ∧ T a) := by
  classical
  have h : κ.prob E ≤ κ.prob (fun a => E a ∧ T a) +
      κ.prob (fun a => ¬ T a) := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    by_cases he : E a <;> by_cases ht : T a <;> simp [he, ht, κ.nonneg a]
  rw [SourceProjectionRetention.probability_complement] at h
  linarith

private theorem prod_prob_both {A : Type*} [Fintype A]
    (κ : FiniteLaw A) (T : A → Prop) :
    (κ.prod κ).prob (fun x => T x.1 ∧ T x.2) = (κ.prob T)^2 := by
  classical
  have hprod := FiniteLaw.prod_prob κ κ (fun a b => T a ∧ T b)
  have h (a : A) : κ.prob (fun b => T a ∧ T b) =
      if T a then κ.prob T else 0 := by
    by_cases ha : T a <;> simp [ha]
  calc
    _ = ∑ a, κ.weight a * κ.prob (fun b => T a ∧ T b) := hprod
    _ = ∑ a, κ.weight a * (if T a then κ.prob T else 0) := by simp_rw [h]
    _ = (κ.prob T) * (κ.prob T) := by
      calc
        _ = ∑ a, (if T a then κ.weight a else 0) * κ.prob T := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : T a <;> simp [ha]
        _ = (∑ a, if T a then κ.weight a else 0) * κ.prob T := by
          rw [Finset.sum_mul]
        _ = _ := rfl
    _ = _ := by ring

/-- The literal two-template event has probability `λ²` in the original
two-coordinate law, including all non-template source labels. -/
theorem both_template_prob (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
    (χ.prod χ).prob (fun k =>
      (∃ p z, k.1 = .inl (p,z)) ∧ (∃ r z, k.2 = .inl (r,z))) =
      (255 / 256 : ℝ) ^ 2 := by
  classical
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  let T : K V X q₁ q₂ s → Prop := fun k =>
    ∃ p z, k = .inl (p,z)
  have hmass : χ.prob T = 255 / 256 := by
    have h := (column_family_masses (V := V) (q₁ := q₁)
      (q₂ := q₂) (s := s) μ hs).1
    convert h using 1
    apply congrArg
    funext k
    cases k with
    | inl z => rcases z with ⟨p,t⟩; simp [T, columnFamilyIndex]
    | inr z =>
        rcases z with ⟨⟨g, v | a⟩, x⟩ <;>
          simp [T, columnFamilyIndex]
  change (χ.prod χ).prob (fun k => T k.1 ∧ T k.2) = _
  rw [prod_prob_both, hmass]

/-- A good original two-coordinate projection has a fixed pair of template
bins whose *actual selector-pair image* has the claimed mass. -/
theorem exists_dense_pair_bins (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (B : Set (K V X q₁ q₂ s × K V X q₁ q₂ s))
    (hgood : (99 / 100 : ℝ) ≤
      ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prod
        (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).prob
          (· ∈ B)) :
    ∃ p r : Fin s,
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
          (255 / 256 : ℝ)^2 ≤
        ((templateLaw μ q₁ q₂).toFiniteLaw.prod
          (templateLaw μ q₁ q₂).toFiniteLaw).prob
            (fun z => ((.inl (p,z.1), .inl (r,z.2)) :
              K V X q₁ q₂ s × K V X q₁ q₂ s) ∈ B) := by
  classical
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  let σ := (templateLaw μ q₁ q₂).toFiniteLaw
  let a : ℝ := ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
    (255 / 256 : ℝ)^2
  let f (p r : Fin s) : ℝ := (σ.prod σ).prob
    (fun z => ((.inl (p,z.1), .inl (r,z.2)) :
      K V X q₁ q₂ s × K V X q₁ q₂ s) ∈ B)
  have htemplate := both_template_prob (V := V)
    (q₁ := q₁) (q₂ := q₂) (s := s) μ hs
  have hinter := prob_inter_lower (χ.prod χ) (· ∈ B)
    (fun k => (∃ p z, k.1 = .inl (p,z)) ∧
      (∃ r z, k.2 = .inl (r,z)))
  have hdecomp := template_pair_prob (V := V) μ hs B
  have hsum : (99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1 ≤
      ((255 / 256 : ℝ) * (s : ℝ)⁻¹)^2 *
        ∑ p : Fin s, ∑ r : Fin s, f p r := by
    have hh : (χ.prod χ).prob (fun k => k ∈ B ∧
        ((∃ p z, k.1 = .inl (p,z)) ∧
          (∃ r z, k.2 = .inl (r,z)))) =
        (χ.prod χ).prob (fun k =>
          match k with
          | (.inl _, .inl _) => k ∈ B
          | _ => False) := by
      congr 1
      funext k
      rcases k with ⟨u,v⟩
      cases u with
      | inl u =>
          cases v with
          | inl v =>
              rcases u with ⟨p,z⟩
              rcases v with ⟨r,t⟩
              simp
          | inr v => simp
      | inr u => cases v <;> simp
    dsimp [χ] at hgood htemplate hinter hdecomp
    rw [hh] at hinter
    simpa only [f] using le_trans (by linarith [hgood, htemplate])
      (le_of_eq hdecomp)
  by_contra hn
  have hall (p r : Fin s) : f p r < a := by
    exact lt_of_not_ge (fun hp => hn ⟨p,r,hp⟩)
  let p0 : Fin s := ⟨0, by omega⟩
  have hinner (p : Fin s) : (∑ r : Fin s, f p r) < ∑ _r : Fin s, a := by
    apply Finset.sum_lt_sum
    · intro r _; exact (hall p r).le
    · exact ⟨p0, Finset.mem_univ _, hall p p0⟩
  have houter : (∑ p : Fin s, ∑ r : Fin s, f p r) <
      ∑ _p : Fin s, ∑ _r : Fin s, a := by
    apply Finset.sum_lt_sum
    · intro p _; exact (hinner p).le
    · exact ⟨p0, Finset.mem_univ _, hinner p0⟩
  have hconst : (∑ _p : Fin s, ∑ _r : Fin s, a) =
      (s : ℝ) * ((s : ℝ) * a) := by
    simp [Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at houter
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hcpos : (0 : ℝ) < ((255 / 256 : ℝ) * (s : ℝ)⁻¹)^2 := by positivity
  have heq : ((255 / 256 : ℝ) * (s : ℝ)⁻¹)^2 *
      ((s : ℝ) * ((s : ℝ) * a)) = (255 / 256 : ℝ)^2 * a := by
    field_simp
  have houter' := mul_lt_mul_of_pos_left houter hcpos
  rw [heq] at houter'
  have ha : (255 / 256 : ℝ)^2 * a =
      (99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1 := by
    dsimp [a]
    field_simp
  nlinarith [hsum, houter', ha]

/-- A good pair projection of the original retained tuple set yields fixed
bins, an actual finite selector-pair image, and the quantified deletion
retention required by the two-stream endpoint. The image is not replaced
by a product of its singleton projections. -/
theorem original_pair_package [DecidableEq X]
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (i j : Fin w) (U : Set (Fin w → K V X q₁ q₂ s))
    (hgood : (99 / 100 : ℝ) ≤
      ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prod
        (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).prob
          (· ∈ (fun y => (y i, y j)) '' U))
    (τ : ℝ)
    (hmargin : (49 / 64 : ℝ) + τ <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2) :
    ∃ p r : Fin s,
      ∃ P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X),
      (∀ z, z ∈ P0 ↔ z ∈ pairImage U i j p r) ∧
      (((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
          (255 / 256 : ℝ)^2 ≤
        ((templateLaw μ q₁ q₂).toFiniteLaw.prod
          (templateLaw μ q₁ q₂).toFiniteLaw).prob (· ∈ (P0 : Set _))) ∧
      (∀ P' : Finset (Template q₁ q₂ X × Template q₁ q₂ X),
        P' ⊆ P0 →
        SourceSupportStep.mass
          ((templateLaw μ q₁ q₂).toFiniteLaw.prod
            (templateLaw μ q₁ q₂).toFiniteLaw) (P0 \ P') < τ →
        (49 / 64 : ℝ) ≤
          ((templateLaw μ q₁ q₂).toFiniteLaw.prod
            (templateLaw μ q₁ q₂).toFiniteLaw).prob (· ∈ (P' : Set _))) := by
  classical
  let B : Set (K V X q₁ q₂ s × K V X q₁ q₂ s) :=
    (fun y => (y i, y j)) '' U
  obtain ⟨p, r, hpr⟩ := exists_dense_pair_bins (V := V) μ hs B hgood
  let P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X) :=
    Finset.univ.filter (fun z => z ∈ pairImage U i j p r)
  have hmem (z : Template q₁ q₂ X × Template q₁ q₂ X) :
      z ∈ P0 ↔ ((.inl (p,z.1), .inl (r,z.2)) :
        K V X q₁ q₂ s × K V X q₁ q₂ s) ∈ B := by
    simp only [P0, Finset.mem_filter, Finset.mem_univ, true_and,
      B, Set.mem_image]
    change (∃ y ∈ U, y i = .inl (p,z.1) ∧ y j = .inl (r,z.2)) ↔
      ∃ y ∈ U, (y i,y j) = (.inl (p,z.1),.inl (r,z.2))
    constructor
    · rintro ⟨y, hy, hi, hj⟩
      exact ⟨y, hy, Prod.ext hi hj⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨y, hy, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  refine ⟨p, r, P0, ?_, ?_, ?_⟩
  · intro z
    simp [P0]
  · convert hpr using 1
    congr 1
    funext z
    exact propext (hmem z)
  · exact pair_retention (templateLaw μ q₁ q₂).toFiniteLaw P0
      _ τ (by
        convert hpr using 1
        congr 1
        funext z
        exact propext (hmem z)) hmargin

end Paper2.ForeignOwnerProjection

#print axioms Paper2.ForeignOwnerProjection.pairRepresentative_coordinates
#print axioms Paper2.ForeignOwnerProjection.pairRepresentative_entries
#print axioms Paper2.ForeignOwnerProjection.pair_retention
#print axioms Paper2.ForeignOwnerProjection.template_pair_prob
#print axioms Paper2.ForeignOwnerProjection.exists_dense_pair_bins
#print axioms Paper2.ForeignOwnerProjection.original_pair_package
