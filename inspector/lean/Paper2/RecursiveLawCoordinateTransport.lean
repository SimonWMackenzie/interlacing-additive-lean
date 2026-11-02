import Paper2.SourceSuccessorConjugacy
import Paper2.SourceLawCoordinateTransport
import Paper2.RecursiveSampling

/-! Exact rational weights and arbitrary-event laws on the complete
recursive carriers under the already checked carrier equivalences. -/

namespace Paper2.RecursiveLawCoordinateTransport

open SourceMatrix SourceLawCoordinateTransport SourceSuccessorConjugacy

variable {X X' Y Y' V : Type} {s q₁ q₂ w Q : ℕ}
variable [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
  [Fintype V] [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

theorem laws_weight (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) (k : ℕ) :
    (∀ x : RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k,
      (RecursiveSampling.laws (V := V) hs μ' ν' k).1.weight
        ((carrierEquivs π eX eY k).1 x) =
      (RecursiveSampling.laws (V := V) hs μ ν k).1.weight x) ∧
    (∀ y : RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k,
      (RecursiveSampling.laws (V := V) hs μ' ν' k).2.weight
        ((carrierEquivs π eX eY k).2 y) =
      (RecursiveSampling.laws (V := V) hs μ ν k).2.weight y) := by
  induction k with
  | zero => exact ⟨hX, hY⟩
  | succ k ih =>
      constructor
      · intro x
        let old := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
          (w := w) (Q := Q) hs μ ν k
        let new := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
          (w := w) (Q := Q) hs μ' ν' k
        let eqv := carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
          (J := SourceConstruction.Items s V) π eX eY k
        let e : (Fin w × TaggedColumn q₁ q₂ s
            (RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) ≃
            (Fin w × TaggedColumn q₁ q₂ s
              (RecursiveEntries.Column X' Y' (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :=
          Equiv.prodCongr (Equiv.refl (Fin w))
            (SourceCoordinateConjugacy.taggedEquiv π eqv.2)
        have hp : ∀ p : Fin w × TaggedColumn q₁ q₂ s
            (RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k),
            ((PositiveRationalLaw.uniform (Fin w)).prod
              (SourceLawBinding.matrixRowLaw new.2 q₁ q₂ s)).weight (e p) =
            ((PositiveRationalLaw.uniform (Fin w)).prod
              (SourceLawBinding.matrixRowLaw old.2 q₁ q₂ s)).weight p := by
          intro p
          change (PositiveRationalLaw.uniform (Fin w)).weight p.1 *
            (SourceLawBinding.matrixRowLaw new.2 q₁ q₂ s).weight
              (SourceCoordinateConjugacy.taggedMap π eqv.2 p.2) =
            (PositiveRationalLaw.uniform (Fin w)).weight p.1 *
              (SourceLawBinding.matrixRowLaw old.2 q₁ q₂ s).weight p.2
          change (PositiveRationalLaw.uniform (Fin w)).weight p.1 *
            (SourceLaws.taggedLaw new.2 q₁ q₂ s).weight
              (SourceCoordinateConjugacy.taggedMap π eqv.2 p.2) =
            (PositiveRationalLaw.uniform (Fin w)).weight p.1 *
              (SourceLaws.taggedLaw old.2 q₁ q₂ s).weight p.2
          rw [tagged_weight old.2 new.2 π eqv.2 ih.2 p.2]
        exact CoordinateLawTransport.iid_weight
          ((PositiveRationalLaw.uniform (Fin w)).prod
            (SourceLawBinding.matrixRowLaw old.2 q₁ q₂ s))
          ((PositiveRationalLaw.uniform (Fin w)).prod
            (SourceLawBinding.matrixRowLaw new.2 q₁ q₂ s))
          Q (Equiv.refl _) e hp x
      · intro y
        let old := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
          (w := w) (Q := Q) hs μ ν k
        let new := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
          (w := w) (Q := Q) hs μ' ν' k
        let eqv := carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
          (J := SourceConstruction.Items s V) π eX eY k
        have hc : ∀ z : RawRow q₁ q₂ s
            (RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)
            (SourceConstruction.Items s V),
            (SourceLawBinding.matrixColumnLaw new.1 q₁ q₂ s hs).weight
              (SourceCoordinateConjugacy.rawRowEquiv π eqv.1 z) =
            (SourceLawBinding.matrixColumnLaw old.1 q₁ q₂ s hs).weight z :=
          matrixColumn_weight hs old.1 new.1 π eqv.1 ih.1
        change ((PositiveRationalLaw.uniform (Fin Q)).prod
            ((SourceLawBinding.matrixColumnLaw new.1 q₁ q₂ s hs).iid w)).weight
              (columnEquiv π eqv.1 y) =
          ((PositiveRationalLaw.uniform (Fin Q)).prod
            ((SourceLawBinding.matrixColumnLaw old.1 q₁ q₂ s hs).iid w)).weight y
        simp only [PositiveRationalLaw.prod, columnEquiv_apply]
        simp only [PositiveRationalLaw.iid]
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        exact hc (y.2 i)

private theorem pushes_of_weight {B C : Type} [Fintype B] [Fintype C]
    (α : PositiveRationalLaw B) (β : PositiveRationalLaw C)
    (e : B ≃ C) (h : ∀ b, β.weight (e b) = α.weight b) :
    α.toFiniteLaw.PushesTo β.toFiniteLaw e := by
  intro E
  classical
  unfold FiniteLaw.prob
  have hs := e.sum_comp (fun c => if E c then (β.weight c : ℝ) else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw, h] using hs

/-- Both actual recursive source laws push forward along the same carrier
equivalences used by the entry-conjugacy theorem. The predicates in
`PushesTo` range over arbitrary events on each complete labelled carrier. -/
theorem laws_pushes (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y) (k : ℕ) :
    (RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k).1.toFiniteLaw.PushesTo
      (RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs μ' ν' k).1.toFiniteLaw
      (carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
        (J := SourceConstruction.Items s V) π eX eY k).1 ∧
    (RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k).2.toFiniteLaw.PushesTo
      (RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
        (w := w) (Q := Q) hs μ' ν' k).2.toFiniteLaw
      (carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
        (J := SourceConstruction.Items s V) π eX eY k).2 := by
  obtain ⟨hr, hc⟩ := laws_weight (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ μ' ν ν' π eX eY hX hY k
  exact ⟨pushes_of_weight _ _ _ hr, pushes_of_weight _ _ _ hc⟩

end Paper2.RecursiveLawCoordinateTransport

#print axioms Paper2.RecursiveLawCoordinateTransport.laws_weight
#print axioms Paper2.RecursiveLawCoordinateTransport.laws_pushes
