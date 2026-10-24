import CurrentAdditive.V39FullProductSources
import CurrentAdditive.GeneratedOwnerRowJoint

namespace CurrentAdditive.V39FullProductSources

open Paper2 Paper2.SourceMatrix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)

noncomputable def fullStreams (μI : PositiveRationalLaw I) (w : ℕ) :
    InternalStreams
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI w where
  metadataStream := fullCode D w (metadataLaw (s := s) μI)
  baseStream := fullCode D w μX
  selectorStream := fullCode D w
    (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY).inner.law

noncomputable def tupleMap (μI : PositiveRationalLaw I) (w : ℕ)
    (t : InternalLabel
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w)) :
    Fin w → RawRow q₁ q₂ s X I :=
  fun p => Sources.decodeRow _ (InternalStreams.decode _ _ t p)

/-- For literal full selectors the indexed row decoder is the identity.
The equality is propositional because the decoder pattern-matches on rows. -/
theorem tupleMap_eq_decode (μI : PositiveRationalLaw I) (w : ℕ) :
    tupleMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w =
      InternalStreams.decode
        (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
        (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w) := by
  funext t p
  exact decodeRow_eq_rowEquiv μX μY _

section RowLaw

variable {G V Aux : Type*} [Fintype G] [Fintype V] [Fintype Aux]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  (μI : PositiveRationalLaw (G × (V ⊕ Aux))) (w : ℕ)

/-- Full independent complete streams push to the entire iid raw-row tuple,
not merely to its small marginals. The bounded joint theorem is instantiated
at order w on literal full sources; their laws and decoders ignore D. -/
theorem tuple_pushes :
    (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w).law.toFiniteLaw.PushesTo
      ((rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI).toFiniteLaw.iid w)
      (tupleMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w) := by
  let ρ := (rowLaw
    (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI).toFiniteLaw
  have hw₀ := internal_streams_row_dwise
    (fullSources (D := w) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY) μI
    (fullStreams (D := w) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w)
  have hw : IsDWise w
    (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w).law.toFiniteLaw
    (InternalStreams.decode
      (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY μI w)) ρ := by
    convert hw₀ using 1
    apply FiniteLaw.eq_of_weight_eq
    funext a
    cases a <;> rfl

  rw [← tupleMap_eq_decode μX μY μI w] at hw
  intro E
  let J : Finset (Fin w) := Finset.univ
  have h := hw J (by simp [J])
    (fun z : J → RawRow q₁ q₂ s X (G × (V ⊕ Aux)) =>
      E (fun p => z ⟨p,Finset.mem_univ p⟩))
  have hp := FiniteLaw.pi_prob_restrict (fun _ : J => ρ)
    (fun p : Fin w => (⟨p,Finset.mem_univ p⟩ : J))
    (by intro i j hij; exact congrArg Subtype.val hij) E
  exact h.trans hp

end RowLaw

section GraphLaw

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex] [Nonempty Vertex]

noncomputable def graphItemLaw (hs : 4 ≤ s) :
    PositiveRationalLaw (SourceConstruction.Items s Vertex) := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0,by omega⟩⟩
  exact itemLaw (G := Fin (4*s)) (V := Vertex) (A := Fin (s-3))

/-- The indexed source's literal full-template row law is the current
full-product raw-row law, including its two separate item classes. -/
theorem raw_law_eq_current (hs : 4 ≤ s) :
    (rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
      (graphItemLaw (Vertex := Vertex) hs)).toFiniteLaw =
      (V38Matrix.columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := Vertex) μX hs).toFiniteLaw := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0,by omega⟩⟩
  have hw :
      (rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
        (graphItemLaw (Vertex := Vertex) hs)).toFiniteLaw.weight =
      (V38Matrix.columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := Vertex) μX hs).toFiniteLaw.weight := by
    funext a
    rcases a with ⟨p,z⟩ | ⟨⟨g,v | b⟩,x⟩
    all_goals
      simp [rowLaw, templateRowLaw, sourceRowLaw, graphItemLaw, itemLaw,
        halfSumLaw, fullSources, fullCode, V38Matrix.columnLaw,
        EdgeSourceMatrix.matrixColumnLaw, SourceLawBinding.matrixColumnLaw,
        PositiveRationalLaw.relabel, SourceLawBinding.rawRowEquiv,
        SourceLawBinding.itemEquiv, SourceLaws.rowLaw, SourceLaws.itemRowLaw,
        SourceLaws.templateRowLaw, SourceLaws.templateLaw,
        PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.prod,
        PositiveRationalLaw.uniform, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
        <;> ring
  cases h₁ : (rowLaw (fullSources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (graphItemLaw (Vertex := Vertex) hs)).toFiniteLaw
  cases h₂ : (V38Matrix.columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := Vertex) μX hs).toFiniteLaw
  simp only [h₁,h₂] at hw
  cases hw
  rfl

theorem graph_tuple_pushes (hs : 4 ≤ s) (w : ℕ) :
    (fullStreams (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY
      (graphItemLaw (Vertex := Vertex) hs) w).law.toFiniteLaw.PushesTo
      ((V38Matrix.columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := Vertex) μX hs).toFiniteLaw.iid w)
      (tupleMap (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY
        (graphItemLaw (Vertex := Vertex) hs) w) := by
  rw [← raw_law_eq_current (D := D) μX μY hs]
  exact tuple_pushes (D := D) μX μY (graphItemLaw (Vertex := Vertex) hs) w

end GraphLaw

#print axioms tuple_pushes
#print axioms raw_law_eq_current
#print axioms graph_tuple_pushes

end CurrentAdditive.V39FullProductSources
