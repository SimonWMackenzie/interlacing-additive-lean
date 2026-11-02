import CurrentAdditive.V38IndexedTwoTag
import CurrentAdditive.V38Matrix
import CurrentAdditive.GeneratedOwnerTuple
import Paper2.ReferencePrefix

namespace CurrentAdditive.V39FullProductSources

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol

universe u

/-- A literal full product is an exact source of every finite order. -/
noncomputable def fullCode {A : Type u} [Fintype A] [DecidableEq A]
    (D q : ℕ) (μ : PositiveRationalLaw A) : CodeSource D q A μ where
  Label := Fin q → A
  finite := inferInstance
  decEq := inferInstance
  law := μ.iid q
  decode := id
  exactLaw := by
    intro J _hJ E
    rw [PositiveRationalLaw.toFiniteLaw_iid]
    exact FiniteLaw.pi_prob_restrict (fun _ : Fin q => μ.toFiniteLaw)
      (fun j : J => j.val) Subtype.val_injective E

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

/-- The same source data type, instantiated by actual full word, template,
and outer-tuple labels, with iid rational laws and identity decoders. -/
noncomputable def fullSources (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y) :
    Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY where
  gamma := fullCode D (q₁+s+1) μY
  inner := fullCode D q₂ ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
  outer := fullCode D s ((PositiveRationalLaw.uniform (Fin q₂)).prod
    (μY.iid (q₁+s+1)))

variable (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)

noncomputable abbrev FullSource := fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY

noncomputable def rowEquiv : Row (I := I) (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) ≃ RawRow q₁ q₂ s X I :=
  Equiv.refl _

theorem decodeRow_eq_rowEquiv
    (a : Row (I := I) (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)) :
    Sources.decodeRow _ a = rowEquiv (D := D) μX μY a := by
  cases a <;> rfl

/-- The ordinary decoder forgets the unused head of its independent word.
No injectivity or bijectivity assertion is made for this map. -/
noncomputable def columnMap : V38IndexedTwoTag.Column (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) →
    V38Matrix.TaggedColumn q₁ q₂ s Y
  | .inl (js, γ) => .inl (tail γ, js)
  | .inr j => .inr j

theorem tail_pushes :
    (μY.iid (q₁+s+1)).toFiniteLaw.PushesTo (μY.iid (s+1)).toFiniteLaw
      (tail (q₁ := q₁) (s := s)) := by
  intro E
  rw [PositiveRationalLaw.toFiniteLaw_iid, PositiveRationalLaw.toFiniteLaw_iid]
  exact FiniteLaw.pi_prob_restrict (fun _ : Fin (q₁+s+1) => μY.toFiniteLaw)
    (fun i : Fin (s+1) => (⟨q₁+i.val, by omega⟩ : Fin (q₁+s+1)))
    (by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega) E

theorem ordinary_pushes :
    ((FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).outer.law.prod (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).gamma.law).toFiniteLaw.PushesTo
      (SourceLaws.rawLaw μY q₁ q₂ s).toFiniteLaw
      (fun z => (tail z.2, z.1)) := by
  classical
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro z
  rcases z with ⟨ξ,js⟩
  rw [PositiveRationalLaw.toFiniteLaw_prod]
  calc
    _ = ((FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).outer.law.toFiniteLaw.prod
        (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).gamma.law.toFiniteLaw).prob
        (fun z => z.1 = js ∧ tail z.2 = ξ) := by
      congr 1
      funext z
      apply propext
      constructor
      · intro h
        exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
      · rintro ⟨h1,h2⟩
        exact Prod.ext h2 h1
    _ = (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).outer.law.toFiniteLaw.weight js *
        (μY.iid (q₁+s+1)).toFiniteLaw.prob (fun γ => tail γ = ξ) :=
      FiniteLaw.prod_prob_fixed_fst _ _ js (fun γ => tail γ = ξ)
    _ = _ := by
      rw [tail_pushes μY (fun a => a = ξ), FiniteLaw.prob_singleton]
      simp only [FullSource, fullSources, fullCode, SourceLaws.rawLaw,
        SourceLaws.outerLaw, PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod,
        Rat.cast_mul]
      ring

theorem tagged_pushes :
    (V38IndexedTwoTag.law (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)).toFiniteLaw.PushesTo
      (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY).toFiniteLaw
      (columnMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) := by
  intro E
  rw [V38IndexedTwoTag.prob_split, V38Matrix.tagged_prob]
  have ho := ordinary_pushes (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY (fun z => E (.inl z))
  change (255/256 : ℝ) *
      ((FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).outer.law.prod (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).gamma.law).toFiniteLaw.prob
        (fun z => E (.inl (tail z.2,z.1))) + _ = _
  rw [ho]
  rfl

/-- Exact probability equality for every original per-copy retained event,
including arbitrary receipt predicates or actual protocol routes. -/
theorem copy_event_prob {w : ℕ} (i : Fin w)
    (E : (Fin w × V38Matrix.TaggedColumn q₁ q₂ s Y) → Prop) :
    (V38IndexedTwoTag.law (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)).toFiniteLaw.prob
        (fun c => E (i,columnMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY c)) =
      (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := s) μY).toFiniteLaw.prob
        (fun c => E (i,c)) :=
  tagged_pushes (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY (fun c => E (i,c))

theorem matrix_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (c : V38IndexedTwoTag.Column (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY))
    (a : Row (I := I) (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)) :
    V38IndexedTwoTag.matrix (FullSource (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) R activity ξ₀ c a =
      raw R activity (rowEquiv (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) (I := I) μX μY a)
        (V38Matrix.forgetTag ξ₀ (columnMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY c)) := by
  cases a <;> cases c <;> rfl

#print axioms fullCode
#print axioms fullSources
#print axioms tail_pushes
#print axioms ordinary_pushes
#print axioms tagged_pushes
#print axioms copy_event_prob
#print axioms matrix_entry

end CurrentAdditive.V39FullProductSources
