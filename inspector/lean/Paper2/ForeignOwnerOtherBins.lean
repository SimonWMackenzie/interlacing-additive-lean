import Paper2.ForeignOwnerProjection
import Paper2.ReferenceProjectionMass

/-!
# Other template bins at a foreign owner

Frozen v12 `res:foreign`, lines 410--439.  The retained tuple event is
unchanged and possibly correlated.  All probabilities below use the fixed
ambient template law, never a law conditioned on chosen completions.
-/

namespace Paper2.ForeignOwnerOtherBins

open SourceMatrix SourceLaws SourceLawBinding ForeignOwnerProjection

variable {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
  {q₁ q₂ s w : ℕ} [NeZero q₁]

/-- Selector labels exposed by surviving original tuples in one fixed
template bin at the owner's coordinate. -/
def binImage (U : Set (Fin w → K V X q₁ q₂ s))
    (i : Fin w) (p : Fin s) : Set (Template q₁ q₂ X) :=
  fun z => ∃ y ∈ U, y i = .inl (p, z)

/-- A good singleton image forces every fixed bin, not merely an average
bin, to retain the advertised selector mass. -/
theorem every_bin_mass (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w) (η : ℝ)
    (hgood : 1 - η ≤
      ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).prob
        (· ∈ (fun y : Fin w → K V X q₁ q₂ s => y i) '' U))
    (p : Fin s) :
    1 - η * (s : ℝ) / (255 / 256 : ℝ) ≤
      (templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ binImage U i p) := by
  let E : K V X q₁ q₂ s → Prop :=
    fun k => k ∈ (fun y : Fin w → K V X q₁ q₂ s => y i) '' U
  have h := SourceProjectionRetention.template_bin_retained
    (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) μ hs E η hgood p
  simpa only [E, binImage, Set.mem_setOf_eq, Set.mem_image] using h

/-- The cover's literal singleton projection, rather than a separately
supplied retained law, provides the preceding image hypothesis. -/
theorem every_bin_mass_of_projection (μ : PositiveRationalLaw X)
    (hs : 4 ≤ s) (U : Set (Fin w → K V X q₁ q₂ s))
    (i : Fin w) (η : ℝ)
    (hgood : 1 - η ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw)
      (· ∈ U) {i}) (p : Fin s) :
    1 - η * (s : ℝ) / (255 / 256 : ℝ) ≤
      (templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ binImage U i p) := by
  apply every_bin_mass μ hs U i η _ p
  exact ReferenceProjectionMass.singleton_image_mass_ge
    (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw U i
    (1 - η) hgood

/-- The public numerical margin converts the proved fixed-bin mass to
the two-stream row floor; no per-bin floor is assumed. -/
theorem every_bin_above_threshold (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w)
    (η τ₀ : ℝ)
    (hgood : 1 - η ≤
      ((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).prob
        (· ∈ (fun y : Fin w → K V X q₁ q₂ s => y i) '' U))
    (hmargin : τ₀ < 1 - η * (s : ℝ) / (255 / 256 : ℝ))
    (p : Fin s) :
    τ₀ < (templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ binImage U i p) :=
  lt_of_lt_of_le hmargin (every_bin_mass μ hs U i η hgood p)

theorem every_bin_above_threshold_of_projection
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w)
    (η τ₀ : ℝ)
    (hgood : 1 - η ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw)
      (· ∈ U) {i})
    (hmargin : τ₀ < 1 - η * (s : ℝ) / (255 / 256 : ℝ))
    (p : Fin s) :
    τ₀ < (templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ binImage U i p) :=
  lt_of_lt_of_le hmargin (every_bin_mass_of_projection μ hs U i η hgood p)

/-- A selector label in a fixed bin has an actual surviving completion. -/
noncomputable def binRepresentative
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w) (p : Fin s)
    (z : binImage U i p) : Fin w → K V X q₁ q₂ s :=
  Classical.choose z.property

theorem binRepresentative_survives
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w) (p : Fin s)
    (z : binImage U i p) : binRepresentative U i p z ∈ U :=
  (Classical.choose_spec z.property).1

theorem binRepresentative_coordinate
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w) (p : Fin s)
    (z : binImage U i p) :
    (binRepresentative U i p z) i = .inl (p, z.val) :=
  (Classical.choose_spec z.property).2

theorem binRepresentative_injective
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w) (p : Fin s) :
    Function.Injective (binRepresentative U i p) := by
  intro z z' h
  apply Subtype.ext
  have hz := binRepresentative_coordinate U i p z
  have hz' := binRepresentative_coordinate U i p z'
  rw [h] at hz
  exact (Prod.mk.inj (Sum.inl.inj (hz.symm.trans hz'))).2

/-- Different bin-selector labels cannot choose the same original tuple. -/
theorem binRepresentative_distinct
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w)
    (p p' : Fin s) (z : binImage U i p) (z' : binImage U i p')
    (hlabel : p ≠ p' ∨ z.val ≠ z'.val) :
    binRepresentative U i p z ≠ binRepresentative U i p' z' := by
  intro heq
  have hz := binRepresentative_coordinate U i p z
  have hz' := binRepresentative_coordinate U i p' z'
  rw [heq] at hz
  have hpair := Prod.mk.inj (Sum.inl.inj (hz.symm.trans hz'))
  rcases hlabel with hp | hz
  · exact hp hpair.1
  · exact hz hpair.2

/-- Other-bin completions are disjoint from the distinguished pair-bin
representatives by the original coordinate `i`, regardless of how the
remaining coordinates of either completion were chosen. -/
theorem other_disjoint_pairRepresentative
    (U : Set (Fin w → K V X q₁ q₂ s))
    (i j : Fin w) (p pᵢ pⱼ : Fin s) (hp : p ≠ pᵢ)
    (z : binImage U i p) (e : pairImage U i j pᵢ pⱼ) :
    binRepresentative U i p z ≠ pairRepresentative U i j pᵢ pⱼ e := by
  intro heq
  have hz := binRepresentative_coordinate U i p z
  have he := (pairRepresentative_coordinates U i j pᵢ pⱼ e).1
  rw [heq] at hz
  exact hp (Prod.mk.inj (Sum.inl.inj (hz.symm.trans he))).1

/-- On every chosen other-bin original completion, the unrestricted
source entry reads precisely that selector and that original bin. -/
theorem binRepresentative_unrestricted_entry {Y : Type*} [NeZero s]
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (U : Set (Fin w → K V X q₁ q₂ s)) (i : Fin w) (p : Fin s)
    (z : binImage U i p) (Z : RawColumn q₁ q₂ s Y) :
    N base activity ξ₀ (.unrestricted Z) ((binRepresentative U i p z) i) =
      T base z.val (Z.2 p) := by
  rw [binRepresentative_coordinate]
  rfl

end Paper2.ForeignOwnerOtherBins

#print axioms Paper2.ForeignOwnerOtherBins.every_bin_mass
#print axioms Paper2.ForeignOwnerOtherBins.every_bin_mass_of_projection
#print axioms Paper2.ForeignOwnerOtherBins.every_bin_above_threshold
#print axioms Paper2.ForeignOwnerOtherBins.every_bin_above_threshold_of_projection
#print axioms Paper2.ForeignOwnerOtherBins.binRepresentative_injective
#print axioms Paper2.ForeignOwnerOtherBins.other_disjoint_pairRepresentative
#print axioms Paper2.ForeignOwnerOtherBins.binRepresentative_unrestricted_entry
