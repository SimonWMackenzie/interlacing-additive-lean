import Paper2.ForeignOwnerOtherBins
import Paper2.TwoStreamSource
import Paper2.RestorationSourceMargins

/-!
# The foreign-owner rectangle on original interlace labels

Frozen v12 `res:foreign`, lines 401--446.  A row of the transposed
two-stream rectangle is an original retained tuple with a template at the
owner coordinate.  Its ambient laws remain the literal source laws.
-/

namespace Paper2.ForeignOwnerRectangle

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLaws SourceLawBinding
open ForeignOwnerProjection ForeignOwnerOtherBins SourceProfileParameters

variable {V X Y : Type*} [Fintype V] [Nonempty V] [Fintype X] [Fintype Y]
  {q₁ q₂ s w : ℕ} [NeZero q₁]

/-- An original tuple, not a newly sampled selector, whose owner
coordinate is a template symbol. -/
abbrev TemplateTuple (i : Fin w) :=
  {y : Fin w → K V X q₁ q₂ s // ∃ p : Fin s, ∃ z : Template q₁ q₂ X,
    y i = .inl (p,z)}

noncomputable instance templateTupleFintype (i : Fin w) :
    Fintype (TemplateTuple (V := V) (X := X) (q₁ := q₁)
      (q₂ := q₂) (s := s) i) := by
  classical
  infer_instance

noncomputable def bin (i : Fin w) (r : TemplateTuple (V := V) (X := X)
    (q₁ := q₁) (q₂ := q₂) (s := s) i) : Fin s :=
  Classical.choose r.property

noncomputable def selector (i : Fin w) (r : TemplateTuple (V := V) (X := X)
    (q₁ := q₁) (q₂ := q₂) (s := s) i) : Template q₁ q₂ X :=
  Classical.choose (Classical.choose_spec r.property)

theorem coordinate_eq (i : Fin w) (r : TemplateTuple (V := V) (X := X)
    (q₁ := q₁) (q₂ := q₂) (s := s) i) :
    r.val i = .inl (bin i r, selector i r) :=
  Classical.choose_spec (Classical.choose_spec r.property)

/-- The retained two-stream rows are precisely the original surviving
template tuples. -/
def retainedTuples (i : Fin w) (Y' : Set (Fin w → K V X q₁ q₂ s)) :
    Set (TemplateTuple (V := V) (X := X) (q₁ := q₁) (q₂ := q₂) (s := s) i) :=
  fun r => r.val ∈ Y'

/-- A fixed-bin selector image is the exact image of the retained row
set under `bin` and `selector`. -/
theorem binImage_eq_rows (i : Fin w)
    (Y' : Set (Fin w → K V X q₁ q₂ s)) (p : Fin s)
    (z : Template q₁ q₂ X) :
    z ∈ binImage Y' i p ↔
      ∃ r ∈ retainedTuples i Y', bin i r = p ∧ selector i r = z := by
  constructor
  · rintro ⟨y, hy, hcoord⟩
    let r : TemplateTuple (V := V) (X := X) (q₁ := q₁)
      (q₂ := q₂) (s := s) i := ⟨y, ⟨p, z, hcoord⟩⟩
    refine ⟨r, hy, ?_, ?_⟩
    · have h := coordinate_eq i r
      change y i = _ at h
      rw [hcoord] at h
      exact (Prod.mk.inj (Sum.inl.inj h)).1.symm
    · have h := coordinate_eq i r
      change y i = _ at h
      rw [hcoord] at h
      exact (Prod.mk.inj (Sum.inl.inj h)).2.symm
  · rintro ⟨r, hr, hp, hz⟩
    refine ⟨r.val, hr, ?_⟩
    simpa [hp, hz] using coordinate_eq i r

/-- A paired selector has a chosen surviving original row of this
template-tuple carrier. -/
noncomputable def pairTuple (i j : Fin w) (Y' : Set (Fin w → K V X q₁ q₂ s))
    (p r : Fin s) (z : pairImage Y' i j p r) :
    TemplateTuple (V := V) (X := X) (q₁ := q₁) (q₂ := q₂) (s := s) i :=
  ⟨pairRepresentative Y' i j p r z,
    ⟨p, z.val.1, (pairRepresentative_coordinates Y' i j p r z).1⟩⟩

theorem pairTuple_retained (i j : Fin w)
    (Y' : Set (Fin w → K V X q₁ q₂ s)) (p r : Fin s)
    (z : pairImage Y' i j p r) : pairTuple i j Y' p r z ∈ retainedTuples i Y' :=
  pairRepresentative_survives Y' i j p r z

theorem pairTuple_labels (i j : Fin w)
    (Y' : Set (Fin w → K V X q₁ q₂ s)) (p r : Fin s)
    (z : pairImage Y' i j p r) :
    bin i (pairTuple i j Y' p r z) = p ∧
      selector i (pairTuple i j Y' p r z) = z.val.1 ∧
      (pairTuple i j Y' p r z).val j = .inl (r,z.val.2) := by
  have hcoord := coordinate_eq i (pairTuple i j Y' p r z)
  have hp := (pairRepresentative_coordinates Y' i j p r z).1
  have hj := (pairRepresentative_coordinates Y' i j p r z).2
  have h := Prod.mk.inj (Sum.inl.inj (hcoord.symm.trans hp))
  exact ⟨h.1, h.2, hj⟩

private theorem prod_fst_pushes {A B : Type*} [Fintype A] [Fintype B]
    (α : FiniteLaw A) (β : FiniteLaw B) :
    (α.prod β).PushesTo α Prod.fst := by
  classical
  intro E
  conv_lhs => rw [FiniteLaw.prod_prob α β (fun a _ => E a)]
  have hinner (a : A) : β.prob (fun _ : B => E a) = if E a then 1 else 0 := by
    by_cases ha : E a <;> simp [ha]
  simp_rw [hinner]
  simp only [FiniteLaw.prob]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a <;> simp [ha]

private theorem pair_fst_mass (σ : FiniteLaw (Template q₁ q₂ X))
    (P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X)) (a : ℝ)
    (ha : a ≤ (σ.prod σ).prob (· ∈ (P0 : Set _))) :
    a ≤ σ.prob (· ∈ (fun z : Template q₁ q₂ X × Template q₁ q₂ X => z.1) ''
      (P0 : Set _)) :=
  ha.trans (FiniteLaw.prob_le_image (σ.prod σ) σ
    (fun z : Template q₁ q₂ X × Template q₁ q₂ X => z.1)
    (prod_fst_pushes σ σ) (P0 : Set _))

/-- Outside `P0`, the representative is merely totalized by a fixed
template tuple.  Every rule used by the two-stream theorem is local to
`P0`. -/
noncomputable def pairInput (i j : Fin w)
    (Y' : Set (Fin w → K V X q₁ q₂ s)) (p r : Fin s)
    (P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X))
    (hP0 : ∀ e, e ∈ P0 ↔ e ∈ pairImage Y' i j p r)
    (z₀ : Template q₁ q₂ X)
    (e : Template q₁ q₂ X × Template q₁ q₂ X) :
    TemplateTuple (V := V) (X := X) (q₁ := q₁) (q₂ := q₂) (s := s) i := by
  classical
  exact if he : e ∈ P0 then pairTuple i j Y' p r ⟨e, (hP0 e).mp he⟩
    else ⟨(fun _ => .inl (p,z₀)), ⟨p,z₀,rfl⟩⟩

theorem pairInput_retained (i j : Fin w)
    (Y' : Set (Fin w → K V X q₁ q₂ s)) (p r : Fin s)
    (P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X))
    (hP0 : ∀ e, e ∈ P0 ↔ e ∈ pairImage Y' i j p r)
    (z₀ : Template q₁ q₂ X) (e) (he : e ∈ P0) :
    pairInput i j Y' p r P0 hP0 z₀ e ∈ retainedTuples i Y' := by
  simp only [pairInput, dif_pos he]
  exact pairTuple_retained i j Y' p r ⟨e, (hP0 e).mp he⟩

theorem pairInput_labels (i j : Fin w)
    (Y' : Set (Fin w → K V X q₁ q₂ s)) (p r : Fin s)
    (P0 : Finset (Template q₁ q₂ X × Template q₁ q₂ X))
    (hP0 : ∀ e, e ∈ P0 ↔ e ∈ pairImage Y' i j p r)
    (z₀ : Template q₁ q₂ X) (e) (he : e ∈ P0) :
    bin i (pairInput i j Y' p r P0 hP0 z₀ e) = p ∧
    selector i (pairInput i j Y' p r P0 hP0 z₀ e) = e.1 ∧
    (pairInput i j Y' p r P0 hP0 z₀ e).val j = .inl (r,e.2) := by
  simp only [pairInput, dif_pos he]
  exact pairTuple_labels i j Y' p r ⟨e, (hP0 e).mp he⟩

/-- The matrix is the transpose of the actual first interlace on two
families of its original copy-and-tag rows. -/
def rectangleMatrix [NeZero s] {F : Type*}
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w)
    (tag : F → TaggedColumn q₁ q₂ s Y)
    (r : TemplateTuple (V := V) (X := X) (q₁ := q₁) (q₂ := q₂) (s := s) i)
    (c : RawColumn q₁ q₂ s Y ⊕ F) : Bool :=
  match c with
  | .inl Z => fullInterlace (N base activity ξ₀) w (i, .unrestricted Z) r.val
  | .inr f => fullInterlace (N base activity ξ₀) w (j, tag f) r.val

theorem rectangle_ordinary_entry [NeZero s] {F : Type*}
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w)
    (tag : F → TaggedColumn q₁ q₂ s Y)
    (r : TemplateTuple (V := V) (X := X) (q₁ := q₁) (q₂ := q₂) (s := s) i)
    (Z : RawColumn q₁ q₂ s Y) :
    rectangleMatrix base activity ξ₀ i j tag r (.inl Z) =
      T base (selector i r) (Z.2 (bin i r)) := by
  change N base activity ξ₀ (.unrestricted Z) (r.val i) = _
  rw [coordinate_eq i r]
  rfl

/-- Restriction-cost comparison uses only the actual original owner
rectangle.  No density or independent-column premise enters this map. -/
theorem rectangle_restriction_le_owner [NeZero s] {F : Type*} [Fintype F]
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (i j : Fin w)
    (tag : F → TaggedColumn q₁ q₂ s Y)
    (Y' : Set (Fin w → K V X q₁ q₂ s))
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (O : Set (RawColumn q₁ q₂ s Y)) (G : Set F)
    (hO : ∀ Z ∈ O, (i, .unrestricted Z) ∈ R)
    (hG : ∀ f ∈ G, (j, tag f) ∈ R) :
    Compression.restrictionD
      (rectangleMatrix base activity ξ₀ i j tag)
      (retainedTuples i Y') (TwoStreamInitial.retainedColumns O G) ≤
    Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' := by
  classical
  let fr : (retainedTuples i Y') → Y' :=
    fun r => ⟨r.val.val, r.property⟩
  let fc : (TwoStreamInitial.retainedColumns O G) → R := fun c => by
    rcases c with ⟨c, hc⟩
    rcases c with Z | f
    · exact ⟨(i, .unrestricted Z), hO Z (TwoStreamInitial.inl_mem O G Z |>.mp hc)⟩
    · exact ⟨(j, tag f), hG f (TwoStreamInitial.inr_mem O G f |>.mp hc)⟩
  have heq : (fun (r : retainedTuples i Y')
      (c : TwoStreamInitial.retainedColumns O G) =>
      rectangleMatrix base activity ξ₀ i j tag r.val c.val) =
      (fun r c => fullInterlace (N base activity ξ₀) w (fc c).val (fr r).val) := by
    funext r c
    rcases c with ⟨Z | f, hc⟩ <;> rfl
  change D (fun (r : retainedTuples i Y')
    (c : TwoStreamInitial.retainedColumns O G) =>
      rectangleMatrix base activity ξ₀ i j tag r.val c.val) ≤ _
  rw [heq]
  have h := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (y : Y') (a : R) =>
      fullInterlace (N base activity ξ₀) w a.val y.val) fr fc
  have htranspose : D (fun (y : Y') (a : R) =>
      fullInterlace (N base activity ξ₀) w a.val y.val) =
      Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' :=
    SourceProjection.restrictionD_transpose
      (fullInterlace (N base activity ξ₀) w) R Y'
  exact h.trans_eq htranspose

section SourceRectangle

private theorem width_ge_four (L : ℕ) : 4 ≤ width L := by
  unfold width
  have h := exponent_ge L
  have hp : 2 ^ 2 ≤ 2 ^ exponent L :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  exact hp

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by
  unfold outerWidth
  positivity⟩

local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

local instance (L : ℕ) : NeZero (width L) := ⟨by
  unfold width
  positivity⟩

private theorem lower_generic {F : Type*} [Fintype F]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w : ℕ)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) (i j : Fin w)
    (tag : F → TaggedColumn (width L - 2) (outerWidth L) (width L) Y)
    (κF : FiniteLaw F)
    (ψ : Fin (width L) → F →
      OuterColumn (width L - 2) (outerWidth L) (width L) Y)
    (hψ : ∀ r, κF.PushesTo
      (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw (ψ r))
    (htag : ∀ r z f,
      N base activity ξ₀ (tag f) (.inl (r, z)) = T base z (ψ r f))
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y))
    (Y' : Set (Fin w → K V X (width L - 2) (outerWidth L) (width L)))
    (η ε δ x0 : ℝ)
    (hpair : (99 / 100 : ℝ) ≤
      (((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (width_ge_four L)).toFiniteLaw).prod
        ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (width_ge_four L)).toFiniteLaw)).prob
        (· ∈ (fun y => (y i, y j)) '' Y'))
    (hsingle : 1 - η ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
        (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw)
      (· ∈ Y') {i})
    (hO : 1 - ε ≤
      (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun Z => (i, .unrestricted Z) ∈ R))
    (hF : δ ≤ κF.prob (fun f => (j, tag f) ∈ R))
    (hδ : δ ≤ 1)
    (hslack : 2 * outerWidth L * x L + 5 * ε + 2 / outerWidth L ≤ δ)
    (hsmall : 2 * (width L : ℝ) * x0 ≤ 1 / 1000)
    (hother : 2 * (width L : ℝ) * x0 <
      1 - η * (width L : ℝ) / (255 / 256 : ℝ))
    (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hx : x0 = x L) :
    d + exponent L + outerExponent L + exponent L + 1 ≤
      Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' := by
  classical
  subst x0
  let σ := (templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw
  let χ := (matrixColumnLaw (V := V) μ (width L - 2)
    (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw
  let O : Set (RawColumn (width L - 2) (outerWidth L) (width L) Y) :=
    fun Z => (i, .unrestricted Z) ∈ R
  let G : Set F := fun f => (j, tag f) ∈ R
  obtain ⟨p, r, P0, hP0, ha, hret⟩ :=
    ForeignOwnerProjection.original_pair_package (V := V) μ (width_ge_four L)
      i j Y' hpair (2 * width L * x L)
      (by
        have hm := RestorationSourceMargins.pair_margin (width L) (x L) hsmall
        simpa only [Nat.cast_ofNat] using hm)
  let z₀ : Template (width L - 2) (outerWidth L) X :=
    Classical.choice σ.nonempty
  let ι := pairInput i j Y' p r P0 hP0 z₀
  let M := rectangleMatrix base activity ξ₀ i j tag
  have hpairfloor : 2 * width L * x L ≤
      σ.prob (· ∈ (fun e : Template (width L - 2) (outerWidth L) X ×
        Template (width L - 2) (outerWidth L) X => e.1) '' (P0 : Set _)) := by
    have hm := pair_fst_mass σ P0 _ ha
    have hsmall' := RestorationSourceMargins.pair_margin (width L) (x L) hsmall
    dsimp only [σ] at hm
    linarith
  have hrow : ∀ b ≠ p, 2 * width L * x L ≤
      σ.prob (fun z => ∃ t ∈ retainedTuples i Y',
        bin i t = b ∧ selector i t = z) := by
    intro b _
    have hm := ForeignOwnerOtherBins.every_bin_mass_of_projection
      (V := V) μ (width_ge_four L) Y' i η hsingle b
    have heq : (fun z : Template (width L - 2) (outerWidth L) X =>
        z ∈ binImage Y' i b) =
        (fun z => ∃ t ∈ retainedTuples i Y',
          bin i t = b ∧ selector i t = z) := by
      funext z
      exact propext (binImage_eq_rows i Y' b z)
    rw [heq] at hm
    exact (le_of_lt hother).trans hm
  have hlower := TwoStreamSource.restriction_lower μ ν base L d hd hp
    hinner houter hwide href
    M κF (σ.prod σ) (bin i) (selector i) (ψ r)
    (by exact rectangle_ordinary_entry base activity ξ₀ i j tag)
    (hψ r) ι id (by intro E; rfl) p P0 (retainedTuples i Y') O G
    (by intro e he; exact pairInput_retained i j Y' p r P0 hP0 z₀ e he)
    (by intro e he
        exact ⟨(pairInput_labels i j Y' p r P0 hP0 z₀ e he).1,
          (pairInput_labels i j Y' p r P0 hP0 z₀ e he).2.1⟩)
    (by
      intro e he f
      change N base activity ξ₀ (tag f) ((ι e).val j) = _
      rw [(pairInput_labels i j Y' p r P0 hP0 z₀ e he).2.2]
      exact htag r e.2 f)
    (by simpa only [Function.id_comp] using hpairfloor)
    hrow (by
      intro P' hsub hloss
      simpa only [Set.image_id] using hret P' hsub hloss)
    ε δ hO hF hδ hslack
  exact hlower.trans (rectangle_restriction_le_owner base activity ξ₀ i j
    tag Y' R O G (by intro Z hZ; exact hZ) (by intro f hf; exact hf))

private theorem short_owner_impossible {A B : Type*} [Fintype A] [Fintype B]
    (M : A → B → Bool) (R : Set A) (Y' : Set B)
    (C : ℕ) (hlower : C ≤ Compression.restrictionD M R Y')
    (P : Protocol A B Bool)
    (hP : ∀ a ∈ R, ∀ y ∈ Y', P.eval a y = M a y)
    (hcost : P.cost ≤ C - 1) (hC : 1 ≤ C) : False := by
  classical
  let Q := Workspace.UpperBound.Protocol.comap
    (fun a : R => a.val) (fun y : Y' => y.val) P
  have hQ : Q.Computes (fun (a : R) (y : Y') => M a.val y.val) := by
    intro a y
    simpa [Q, Workspace.UpperBound.Protocol.comap_eval] using
      hP a.val a.property y.val y.property
  have hupper : Compression.restrictionD M R Y' ≤ P.cost := by
    have h : Compression.restrictionD M R Y' ≤ Q.cost :=
      Nat.sInf_le ⟨Q, rfl, hQ⟩
    simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using h
  omega

/-- The fixed-tail protected family on the other copy yields a lower
bound on the actual owner rectangle.  Its coordinate marginal and source
entry identity are unfolded here, not postulated. -/
theorem fixedTail_owner_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w : ℕ)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) (i j : Fin w) (hij : i ≠ j)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y))
    (Y' : Set (Fin w → K V X (width L - 2) (outerWidth L) (width L)))
    (δsrc ζsrc ε δ : ℝ)
    (hpair : (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (width_ge_four L)).toFiniteLaw) (· ∈ Y') {i,j})
    (hsingle : 1 - SourceDeletionParameters.eta (width L) δsrc ζsrc ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw)
        (· ∈ Y') {i})
    (hO : 1 - ε ≤
      (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun Z => (i, .unrestricted Z) ∈ R))
    (hF : δ ≤
      (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun f => (j, .fixedTail f) ∈ R))
    (hδ : δ ≤ 1)
    (hslack : 2 * outerWidth L * x L + 5 * ε + 2 / outerWidth L ≤ δ)
    (hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 1000)
    (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000) :
    d + exponent L + outerExponent L + exponent L + 1 ≤
      Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' := by
  let χ := (matrixColumnLaw (V := V) μ (width L - 2)
    (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw
  have hpairImage := ReferenceProjectionMass.pair_image_mass_ge
    χ Y' i j hij (99 / 100 : ℝ) hpair
  have hother := RestorationSourceMargins.other_bin_margin
    (width L) (by unfold width; positivity) δsrc ζsrc (x L) hsmall
  refine lower_generic μ ν base L d w activity ξ₀ i j
    (fun f => .fixedTail f)
    (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
    (fun r f => f r) ?_ ?_ R Y'
    (SourceDeletionParameters.eta (width L) δsrc ζsrc) ε δ (x L)
    hpairImage hsingle hO hF hδ hslack hsmall hother
    hd hp hinner houter hwide href rfl
  · intro r E
    exact SourceLaws.fixedTail_bin_marginal ν
      (width L - 2) (outerWidth L) (width L) r E
  · intro r z f
    rfl

/-- The diagonal protected family uses the same original rectangle; its
ambient outer law and identity coordinate map are literal. -/
theorem diagonal_owner_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w : ℕ)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) (i j : Fin w) (hij : i ≠ j)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y))
    (Y' : Set (Fin w → K V X (width L - 2) (outerWidth L) (width L)))
    (δsrc ζsrc ε δ : ℝ)
    (hpair : (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (width_ge_four L)).toFiniteLaw) (· ∈ Y') {i,j})
    (hsingle : 1 - SourceDeletionParameters.eta (width L) δsrc ζsrc ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw)
        (· ∈ Y') {i})
    (hO : 1 - ε ≤
      (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun Z => (i, .unrestricted Z) ∈ R))
    (hF : δ ≤
      (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ R))
    (hδ : δ ≤ 1)
    (hslack : 2 * outerWidth L * x L + 5 * ε + 2 / outerWidth L ≤ δ)
    (hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 1000)
    (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000) :
    d + exponent L + outerExponent L + exponent L + 1 ≤
      Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' := by
  let χ := (matrixColumnLaw (V := V) μ (width L - 2)
    (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw
  have hpairImage := ReferenceProjectionMass.pair_image_mass_ge
    χ Y' i j hij (99 / 100 : ℝ) hpair
  have hother := RestorationSourceMargins.other_bin_margin
    (width L) (by unfold width; positivity) δsrc ζsrc (x L) hsmall
  refine lower_generic μ ν base L d w activity ξ₀ i j
    (fun f => .diagonal f)
    (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
    (fun _ f => f) ?_ ?_ R Y'
    (SourceDeletionParameters.eta (width L) δsrc ζsrc) ε δ (x L)
    hpairImage hsingle hO hF hδ hslack hsmall hother
    hd hp hinner houter hwide href rfl
  · intro r E
    rfl
  · intro r z f
    rfl

/-- A final owner with `C-1` physical bits cannot receive a protected
population of the other copy at the stated density.  The two alternatives
are its actual fixed-tail and diagonal tags, with their own ambient laws. -/
theorem foreign_owner_impossible
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w : ℕ)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) (i j : Fin w) (hij : i ≠ j)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y))
    (Y' : Set (Fin w → K V X (width L - 2) (outerWidth L) (width L)))
    (P : Protocol (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y)
      (Fin w → K V X (width L - 2) (outerWidth L) (width L)) Bool)
    (hP : ∀ a ∈ R, ∀ y ∈ Y',
      P.eval a y = fullInterlace (N base activity ξ₀) w a y)
    (δsrc ζsrc ε δ : ℝ)
    (hpair : (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (width_ge_four L)).toFiniteLaw) (· ∈ Y') {i,j})
    (hsingle : 1 - SourceDeletionParameters.eta (width L) δsrc ζsrc ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L) (width_ge_four L)).toFiniteLaw)
        (· ∈ Y') {i})
    (hO : 1 - ε ≤
      (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun Z => (i, .unrestricted Z) ∈ R))
    (hprotected :
      δ ≤ (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun f => (j, .fixedTail f) ∈ R) ∨
      δ ≤ (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
        (fun f => (j, .diagonal f) ∈ R))
    (hδ : δ ≤ 1)
    (hslack : 2 * outerWidth L * x L + 5 * ε + 2 / outerWidth L ≤ δ)
    (hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 1000)
    (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hcost : P.cost ≤ d + exponent L + outerExponent L + exponent L) :
    False := by
  let C := d + exponent L + outerExponent L + exponent L + 1
  have hC : 1 ≤ C := by omega
  have hlower : C ≤
      Compression.restrictionD (fullInterlace (N base activity ξ₀) w) R Y' := by
    rcases hprotected with hf | hdia
    · exact fixedTail_owner_lower μ ν base L d w activity ξ₀ i j hij
        R Y' δsrc ζsrc ε δ hpair hsingle hO hf hδ hslack hsmall
        hd hp hinner houter hwide href
    · exact diagonal_owner_lower μ ν base L d w activity ξ₀ i j hij
        R Y' δsrc ζsrc ε δ hpair hsingle hO hdia hδ hslack hsmall
        hd hp hinner houter hwide href
  apply short_owner_impossible (fullInterlace (N base activity ξ₀) w)
    R Y' C hlower P hP
  · dsimp only [C]
    omega
  · exact hC

end SourceRectangle

end Paper2.ForeignOwnerRectangle

#print axioms Paper2.ForeignOwnerRectangle.binImage_eq_rows
#print axioms Paper2.ForeignOwnerRectangle.pairTuple_labels
#print axioms Paper2.ForeignOwnerRectangle.rectangle_ordinary_entry
#print axioms Paper2.ForeignOwnerRectangle.rectangle_restriction_le_owner
#print axioms Paper2.ForeignOwnerRectangle.fixedTail_owner_lower
#print axioms Paper2.ForeignOwnerRectangle.diagonal_owner_lower
#print axioms Paper2.ForeignOwnerRectangle.foreign_owner_impossible
