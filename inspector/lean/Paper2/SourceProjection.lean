import Paper2.SourceLawBinding
import Paper2.ProductProjections
import Paper2.RestrictionProfiles

/-!
# Actual retained projections in the source construction

Frozen v12 Section 4, `eq:product-projection`, `src:profiles`, and the
retained-template argument in `src:near-full`. Every projected label has
a chosen input from the original retained set; correlated surviving words
are never replaced by a Cartesian product of their individual projections.
The probability identities below use the actual source product laws.
-/

namespace Paper2.SourceProjection

open Workspace.Types.CommComplexity SourceMatrix

variable {A B C D X Y I : Type*}

/-- One actual surviving input for each projected label. -/
noncomputable def representative (f : A → B) (U : Set A) : (f '' U) → U :=
  Function.surjInv (retainedImageMap_surjective f U)

theorem representative_maps (f : A → B) (U : Set A) (b : f '' U) :
    f (representative f U b).val = b.val :=
  congrArg Subtype.val (Function.surjInv_eq (retainedImageMap_surjective f U) b)

theorem representative_survives (f : A → B) (U : Set A) (b : f '' U) :
    (representative f U b).val ∈ U := (representative f U b).property

/-- Restricting through actual maps into surviving inputs cannot increase
the available protocol cost. Correctness is pointwise, not almost sure. -/
theorem restrictionD_map_le [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → Bool) (f : C → A) (g : D → B)
    (U : Set A) (V : Set B) (S : Set C) (T : Set D)
    (hf : Set.MapsTo f S U) (hg : Set.MapsTo g T V) :
    Compression.restrictionD (fun c d => F (f c) (g d)) S T ≤
      Compression.restrictionD F U V := by
  classical
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : U) (b : V) => F a.val b.val)
    (fun c : S => (⟨f c.val, hf c.property⟩ : U))
    (fun d : T => (⟨g d.val, hg d.property⟩ : V))

theorem restrictionD_transpose [Fintype A] [Fintype B]
    (F : A → B → Bool) (U : Set A) (V : Set B) :
    Compression.restrictionD (fun b a => F a b) V U = Compression.restrictionD F U V := by
  classical
  exact transpose_D (fun (a : U) (b : V) => F a.val b.val)

/-- Projected matrix entries are realised by the SAME surviving original
columns for all rows. The entry identity is the only matrix hypothesis. -/
theorem restrictionD_projected_le [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (F : A → B → Bool) (H : C → D → Bool) (f : C → A) (p : B → D)
    (U : Set A) (V : Set B) (S : Set C) (hf : Set.MapsTo f S U)
    (hentry : ∀ c ∈ S, ∀ b ∈ V, F (f c) b = H c (p b)) :
    Compression.restrictionD H S (p '' V) ≤ Compression.restrictionD F U V := by
  classical
  let rows : S → U := fun c => ⟨f c.val, hf c.property⟩
  let cols : (p '' V) → V := representative p V
  have heq : (fun (c : S) (d : p '' V) => H c.val d.val) =
      fun c d => F (rows c).val (cols d).val := by
    funext c d
    rw [hentry c.val c.property (cols d).val (cols d).property]
    exact congrArg (H c.val) (representative_maps p V d).symm
  change Workspace.Types.CommComplexity.D (fun (c : S) (d : p '' V) => H c.val d.val) ≤ _
  rw [heq]
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : U) (b : V) => F a.val b.val) rows cols

section Probability

variable [Fintype A] {n k : ℕ}

theorem iid_restrict_pushes (μ : FiniteLaw A) (e : Fin k → Fin n)
    (he : Function.Injective e) :
    (μ.iid n).PushesTo (μ.iid k) (fun z j => z (e j)) := by
  intro E
  exact FiniteLaw.pi_prob_restrict (fun _ : Fin n => μ) e he E

theorem iid_projection_mass (μ : FiniteLaw A) (e : Fin k → Fin n)
    (he : Function.Injective e) (U : Set (Fin n → A)) :
    (μ.iid n).prob (· ∈ U) ≤ (μ.iid k).prob (· ∈ (fun z j => z (e j)) '' U) :=
  FiniteLaw.prob_le_image _ _ _ (iid_restrict_pushes μ e he) U

end Probability

section SourceMaps

variable {q₁ q₂ s k : ℕ}

def headPosition (q₁ s : ℕ) (i : Fin q₁) : Fin (q₁ + s + 1) := ⟨i.val, by omega⟩

theorem headPosition_injective (q₁ s : ℕ) : Function.Injective (headPosition q₁ s) := by
  intro i j h
  exact Fin.ext (congrArg (fun j : Fin (q₁ + s + 1) => j.val) h)

def wordProjection (e : Fin k → Fin (q₁ + s + 1)) (γ : Word q₁ s Y) : Fin k → Y :=
  fun j => γ (e j)

/-- The selected tuple contains coordinates of one original word. -/
def headProjection (e : Fin k → Fin q₁) (γ : Word q₁ s Y) : Fin k → Y :=
  wordProjection (headPosition q₁ s ∘ e) γ

theorem M₁_projected_entry (R : X → Y → Bool) (e : Fin k → Fin q₁)
    (a : Fin k × X) (γ : Word q₁ s Y) :
    M₁ R (e a.1, a.2) γ = fullInterlace R k a (headProjection e γ) := rfl

def templateProjection (e : Fin k → Fin q₂) (z : Template q₁ q₂ X) :
    Fin k → InnerRow q₁ X := fun j => z (e j)

theorem M₂_projected_entry (R : X → Y → Bool) (e : Fin k → Fin q₂)
    (a : Fin k × Word q₁ s Y) (z : Template q₁ q₂ X) :
    M₂ R (e a.1, a.2) z =
      fullInterlace (fun γ j => M₁ R j γ) k a (templateProjection e z) := rfl

def rawBinProjection (e : Fin k → Fin s) (Z : RawColumn q₁ q₂ s Y) :
    Fin k → OuterColumn q₁ q₂ s Y := fun j => Z.2 (e j)

def tagBinProjection (ξ₀ : Tail s Y) (e : Fin k → Fin s)
    (Z : TaggedColumn q₁ q₂ s Y) : Fin k → OuterColumn q₁ q₂ s Y :=
  rawBinProjection e (forgetTag ξ₀ Z)

theorem N_template_projected_entry [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (e : Fin k → Fin s) (a : Fin k × Template q₁ q₂ X) (Z : TaggedColumn q₁ q₂ s Y) :
    N R activity ξ₀ Z (.inl (e a.1, a.2)) =
      fullInterlace (T R) k a (tagBinProjection ξ₀ e Z) := rfl

section Mass

variable [Fintype X] [Fintype Y]

theorem word_projection_mass (ν : PositiveRationalLaw Y)
    (e : Fin k → Fin (q₁ + s + 1)) (he : Function.Injective e)
    (W : Set (Word q₁ s Y)) :
    (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W) ≤
      (ν.iid k).toFiniteLaw.prob (· ∈ wordProjection e '' W) := by
  simp only [PositiveRationalLaw.toFiniteLaw_iid]
  exact iid_projection_mass ν.toFiniteLaw e he W

theorem head_projection_mass (ν : PositiveRationalLaw Y)
    (e : Fin k → Fin q₁) (he : Function.Injective e) (W : Set (Word q₁ s Y)) :
    (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W) ≤
      (ν.iid k).toFiniteLaw.prob (· ∈ headProjection e '' W) :=
  word_projection_mass ν (headPosition q₁ s ∘ e)
    ((headPosition_injective q₁ s).comp he) W

theorem template_projection_mass (μ : PositiveRationalLaw X) [NeZero q₁]
    (e : Fin k → Fin q₂) (he : Function.Injective e) (U : Set (Template q₁ q₂ X)) :
    (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ U) ≤
      (SourceLaws.templateLaw μ q₁ k).toFiniteLaw.prob (· ∈ templateProjection e '' U) := by
  simp only [SourceLaws.templateLaw, PositiveRationalLaw.toFiniteLaw_iid]
  exact iid_projection_mass _ e he U

theorem template_coordinate_mass (μ : PositiveRationalLaw X) [NeZero q₁]
    (α : Fin q₂) (U : Set (Template q₁ q₂ X)) :
    (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ U) ≤
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw.prob
        (· ∈ (fun z => z α) '' U) :=
  FiniteLaw.prob_le_image _ _ _ (SourceLaws.template_coordinate_marginal μ q₁ q₂ α) U

/-- The actual retained row mass is the mean of the base-row masses in
the labelled selector blocks. This is the input to population counting. -/
theorem inner_block_average (μ : PositiveRationalLaw X) [NeZero q₁]
    (U : Set (InnerRow q₁ X)) :
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw.prob (· ∈ U) =
      (q₁ : ℝ)⁻¹ * ∑ i : Fin q₁, μ.toFiniteLaw.prob (fun x => (i, x) ∈ U) := by
  rw [PositiveRationalLaw.toFiniteLaw_prod,
    FiniteLaw.prod_prob _ _ (fun i x => (i, x) ∈ U)]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.mul_sum]

/-- The full outer law is uniform in the actual coordinate labels and has
the original independent word law in each fibre, including diagonal tags. -/
theorem outer_word_average (ν : PositiveRationalLaw Y) [NeZero q₂]
    (U : Set (OuterColumn q₁ q₂ s Y)) :
    (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U) =
      (q₂ : ℝ)⁻¹ * ∑ α : Fin q₂,
        (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (α, γ) ∈ U) := by
  rw [SourceLaws.outerLaw, PositiveRationalLaw.toFiniteLaw_prod,
    FiniteLaw.prod_prob _ _ (fun α γ => (α, γ) ∈ U)]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.mul_sum]

/-- Fixed-tail retained words keep at least their mass when any distinct
bin coordinates are projected. Independence belongs to the ambient law. -/
theorem fixedTail_projection_mass (ν : PositiveRationalLaw Y) [NeZero q₂]
    (e : Fin k → Fin s) (he : Function.Injective e)
    (U : Set (Fin s → OuterColumn q₁ q₂ s Y)) :
    (SourceLaws.fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U) ≤
      ((SourceLaws.outerLaw ν q₁ q₂ s).iid k).toFiniteLaw.prob
        (· ∈ (fun z j => z (e j)) '' U) := by
  simp only [SourceLaws.fixedTailLaw, PositiveRationalLaw.toFiniteLaw_iid]
  exact iid_projection_mass _ e he U

/-- The unused tail is first forgotten, then the selected bin coordinates
are projected. Every actual raw retained column remains in its image. -/
theorem raw_projection_mass (ν : PositiveRationalLaw Y) [NeZero q₂]
    (e : Fin k → Fin s) (he : Function.Injective e) (U : Set (RawColumn q₁ q₂ s Y)) :
    (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U) ≤
      ((SourceLaws.outerLaw ν q₁ q₂ s).iid k).toFiniteLaw.prob (· ∈ rawBinProjection e '' U) := by
  apply FiniteLaw.prob_le_image
  intro E
  rw [SourceLaws.rawLaw, PositiveRationalLaw.toFiniteLaw_prod]
  change ((ν.iid (s + 1)).toFiniteLaw.prod
    ((SourceLaws.outerLaw ν q₁ q₂ s).iid s).toFiniteLaw).prob
      (fun z => E (fun j => z.2 (e j))) = _
  rw [FiniteLaw.prod_prob_snd (ν.iid (s + 1)).toFiniteLaw
      ((SourceLaws.outerLaw ν q₁ q₂ s).iid s).toFiniteLaw
      (fun js => E (fun j => js (e j))), PositiveRationalLaw.toFiniteLaw_iid,
    PositiveRationalLaw.toFiniteLaw_iid]
  exact iid_restrict_pushes _ e he E

end Mass

section RetainedMatrices

variable [Fintype X] [Fintype Y] [Fintype I]

/-- Actual selected blocks of M₁ against projected retained words. -/
theorem M₁_projection_D_le (R : X → Y → Bool) (e : Fin k → Fin q₁)
    (U : Set (InnerRow q₁ X)) (W : Set (Word q₁ s Y)) (S : Set (Fin k × X))
    (hS : ∀ a ∈ S, (e a.1, a.2) ∈ U) :
    Compression.restrictionD (fullInterlace R k) S (headProjection e '' W) ≤
      Compression.restrictionD (M₁ R) U W :=
  restrictionD_projected_le (M₁ R) (fullInterlace R k)
    (fun a => (e a.1, a.2)) (headProjection e) U W S hS (fun _ _ _ _ => rfl)

/-- Actual selected outer blocks of M₂, with surviving whole templates as
representatives of the projected template labels. -/
theorem M₂_projection_D_le (R : X → Y → Bool) (e : Fin k → Fin q₂)
    (U : Set (OuterColumn q₁ q₂ s Y)) (W : Set (Template q₁ q₂ X))
    (S : Set (Fin k × Word q₁ s Y)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ U) :
    Compression.restrictionD (fullInterlace (fun γ j => M₁ R j γ) k)
      S (templateProjection e '' W) ≤ Compression.restrictionD (M₂ R) U W :=
  restrictionD_projected_le (M₂ R)
    (fullInterlace (fun (γ : Word q₁ s Y) (j : InnerRow q₁ X) => M₁ R j γ) k)
    (fun a : Fin k × Word q₁ s Y => (e a.1, a.2))
    (templateProjection e) U W S hS (fun _ _ _ _ => rfl)

/-- Projecting one surviving template coordinate literally exposes an M₁
restriction at that coordinate. This chooses no new tuple coordinates. -/
theorem T_coordinate_D_le (R : X → Y → Bool) (α : Fin q₂)
    (A : Set (Template q₁ q₂ X)) (W : Set (Word q₁ s Y))
    (V : Set (OuterColumn q₁ q₂ s Y)) (hV : ∀ γ ∈ W, (α, γ) ∈ V) :
    Compression.restrictionD (M₁ R) ((fun z => z α) '' A) W ≤
      Compression.restrictionD (T R) A V := by
  have h := restrictionD_projected_le (M₂ R) (fun γ j => M₁ R j γ)
    (fun γ => (α, γ)) (fun z => z α) V A W hV (fun _ _ _ _ => rfl)
  rw [restrictionD_transpose (M₁ R)] at h
  have ht := restrictionD_transpose (T R) A V
  change Compression.restrictionD (M₂ R) V A = _ at ht
  rwa [ht] at h

/-- Any retained tagged source rectangle contains the interlace on its
retained template bins and its actual projected tagged rows. -/
theorem N_template_projection_D_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (e : Fin k → Fin s)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (S : Set (Fin k × Template q₁ q₂ X))
    (hS : ∀ a ∈ S, Sum.inl (e a.1, a.2) ∈ V) :
    Compression.restrictionD (fullInterlace (T R) k) S (tagBinProjection ξ₀ e '' U) ≤
      Compression.restrictionD (N R activity ξ₀) U V := by
  have h := restrictionD_projected_le (fun k Z => N R activity ξ₀ Z k)
    (fullInterlace (T R) k) (fun a => Sum.inl (e a.1, a.2))
    (tagBinProjection ξ₀ e) V U S hS (fun _ _ _ _ => rfl)
  rwa [restrictionD_transpose (N R activity ξ₀)] at h

/-- The reference-family projection, with exactly the correlated raw
columns measured by `raw_projection_mass`. -/
theorem reference_projection_D_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (e : Fin k → Fin s)
    (U : Set (RawColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (S : Set (Fin k × Template q₁ q₂ X))
    (hS : ∀ a ∈ S, Sum.inl (e a.1, a.2) ∈ V) :
    Compression.restrictionD (fullInterlace (T R) k) S (rawBinProjection e '' U) ≤
      Compression.restrictionD (fun Z k => N R activity ξ₀ (.unrestricted Z) k) U V := by
  have h := restrictionD_projected_le (raw R activity) (fullInterlace (T R) k)
    (fun a => Sum.inl (e a.1, a.2)) (rawBinProjection e) V U S hS (fun _ _ _ _ => rfl)
  have ht := restrictionD_transpose (raw R activity) V U
  exact h.trans_eq ht.symm

/-- Fixed-tail retained inputs expose the same interlace, using one
actually retained fixed-tail tuple for every projected word. -/
theorem fixedTail_projection_D_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (e : Fin k → Fin s)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (S : Set (Fin k × Template q₁ q₂ X))
    (hS : ∀ a ∈ S, Sum.inl (e a.1, a.2) ∈ V) :
    Compression.restrictionD (fullInterlace (T R) k) S
      ((fun z j => z (e j)) '' (TaggedColumn.fixedTail ⁻¹' U)) ≤
      Compression.restrictionD (N R activity ξ₀) U V := by
  let W : Set (Fin s → OuterColumn q₁ q₂ s Y) := TaggedColumn.fixedTail ⁻¹' U
  have h := restrictionD_projected_le (fun k js => N R activity ξ₀ (.fixedTail js) k)
    (fullInterlace (T R) k) (fun a => Sum.inl (e a.1, a.2))
    (fun z j => z (e j)) V W S hS (fun _ _ _ _ => rfl)
  have he := restrictionD_map_le (fun k Z => N R activity ξ₀ Z k)
    id TaggedColumn.fixedTail V U V W (fun _ h => h) (fun _ h => h)
  have ht := restrictionD_transpose (N R activity ξ₀) U V
  exact h.trans (he.trans_eq ht)

/-- On a retained diagonal coordinate, projecting a surviving template
set exposes a literal M₁ submatrix inside the same retained source table.
The chosen template rows do not change when the diagonal word varies. -/
theorem diagonal_template_D_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (W : Set (Word q₁ s Y))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hW : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U) :
    Compression.restrictionD (M₁ R) ((fun z => z α) '' A) W ≤
      Compression.restrictionD (N R activity ξ₀) U V := by
  let F : Word q₁ s Y → Template q₁ q₂ X → Bool :=
    fun γ z => N R activity ξ₀ (.diagonal (α, γ)) (.inl (p, z))
  have hp := restrictionD_projected_le F (fun γ j => M₁ R j γ) id
    (fun z => z α) W A W (fun _ h => h) (fun _ _ _ _ => rfl)
  rw [restrictionD_transpose (M₁ R)] at hp
  have he := restrictionD_map_le (N R activity ξ₀)
    (fun γ => TaggedColumn.diagonal (α, γ)) (fun z => Sum.inl (p, z)) U V W A hW hA
  exact hp.trans he

end RetainedMatrices
end SourceMaps

end Paper2.SourceProjection

#print axioms Paper2.SourceProjection.representative_maps
#print axioms Paper2.SourceProjection.word_projection_mass
#print axioms Paper2.SourceProjection.raw_projection_mass
#print axioms Paper2.SourceProjection.M₁_projection_D_le
#print axioms Paper2.SourceProjection.M₂_projection_D_le
#print axioms Paper2.SourceProjection.reference_projection_D_le
#print axioms Paper2.SourceProjection.fixedTail_projection_D_le
#print axioms Paper2.SourceProjection.diagonal_template_D_le
