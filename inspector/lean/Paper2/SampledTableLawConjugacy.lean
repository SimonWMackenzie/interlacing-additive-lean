import Paper2.RecursiveLawCoordinateTransport
import Paper2.SourceSuccessorConjugacy

/-! Exact law transport of the independent row/column samples and every
predicate of their complete Boolean table. -/

namespace Paper2.SampledTableLawConjugacy

open SourceMatrix SourceSuccessorConjugacy

variable {X X' Y Y' V : Type} {s q₁ q₂ w Q : ℕ}
variable [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
  [Fintype V] [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Both labelled sample lists are transported positionwise. No quotient by
repeated values is taken; `mX=0` and `mY=0` are permitted. -/
def sampleEquiv (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (k mX mY : ℕ) :
    ((Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) ≃
    ((Fin mX → RecursiveEntries.Row X' Y' (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mY → RecursiveEntries.Column X' Y' (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :=
  Equiv.prodCongr
    (CoordinateLawTransport.tupleEquiv mX (Equiv.refl _)
      (carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
        (J := SourceConstruction.Items s V) π eX eY k).1)
    (CoordinateLawTransport.tupleEquiv mY (Equiv.refl _)
      (carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
        (J := SourceConstruction.Items s V) π eX eY k).2)

/-- The actual independent positive-rational laws used for sampled rows and
columns at depth `k`; the first tuple is rows and the second is columns. -/
noncomputable def pairedLaw (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (k mX mY : ℕ) :
    PositiveRationalLaw
      ((Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
        (Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :=
  ((RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ ν k).1.iid mX).prod
    ((RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
      (w := w) (Q := Q) hs μ ν k).2.iid mY)

theorem paired_weight (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (k mX mY : ℕ)
    (p : (Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :
    (pairedLaw (V := V) hs μ' ν' k mX mY).weight
      (sampleEquiv π eX eY k mX mY p) =
      (pairedLaw (V := V) hs μ ν k mX mY).weight p := by
  let old := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ ν k
  let new := RecursiveSampling.laws (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ' ν' k
  let eqv := carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
    (J := SourceConstruction.Items s V) π eX eY k
  obtain ⟨hr, hc⟩ := RecursiveLawCoordinateTransport.laws_weight
    (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hs μ μ' ν ν' π eX eY hX hY k
  have hr' := CoordinateLawTransport.iid_weight old.1 new.1 mX
    (Equiv.refl _) eqv.1 hr p.1
  have hc' := CoordinateLawTransport.iid_weight old.2 new.2 mY
    (Equiv.refl _) eqv.2 hc p.2
  change (new.1.iid mX).weight
      (CoordinateLawTransport.tupleEquiv mX (Equiv.refl _) eqv.1 p.1) *
      (new.2.iid mY).weight
        (CoordinateLawTransport.tupleEquiv mY (Equiv.refl _) eqv.2 p.2) =
    (old.1.iid mX).weight p.1 * (old.2.iid mY).weight p.2
  rw [hr', hc']

private theorem pushes_of_weight {B C : Type} [Fintype B] [Fintype C]
    (α : PositiveRationalLaw B) (β : PositiveRationalLaw C)
    (e : B ≃ C) (h : ∀ b, β.weight (e b) = α.weight b) :
    α.toFiniteLaw.PushesTo β.toFiniteLaw e := by
  intro E
  classical
  unfold FiniteLaw.prob
  have hs := e.sum_comp (fun c => if E c then (β.weight c : ℝ) else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw, h] using hs

theorem paired_pushes (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (k mX mY : ℕ) :
    (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hs μ ν k mX mY).toFiniteLaw.PushesTo
      (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        hs μ' ν' k mX mY).toFiniteLaw
      (sampleEquiv (s := s) (q₁ := q₁) (w := w) (Q := Q)
        (V := V) π eX eY k mX mY) := by
  apply pushes_of_weight
  intro p
  exact paired_weight (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ μ' ν ν' π eX eY hX hY k mX mY p

/-- Equality for every predicate on the complete sampled Boolean table.
The two samples on each side are independent iid tuples with the *actual*
recursive row and column laws. Their labels are coupled by `sampleEquiv`,
not by asking the two generators to reuse one bit tape. -/
theorem table_event_prob [NeZero s] (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (F : X → Y → Bool) (F' : X' → Y' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : (Fin mX → Fin mY → Bool) → Prop) :
    (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hs μ ν k mX mY).toFiniteLaw.prob
        (fun p => E (RecursiveEntries.table F activity ξ k p.1 p.2)) =
    (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hs μ' ν' k mX mY).toFiniteLaw.prob
        (fun p => E (RecursiveEntries.table F'
          (SourceCoordinateConjugacy.activityNew π activity)
          (tailsMap π eX eY ξ) k p.1 p.2)) := by
  let eqv := carrierEquivs (s := s) (q₁ := q₁) (w := w) (Q := Q)
    (J := SourceConstruction.Items s V) π eX eY k
  have htable (p :
      (Fin mX → RecursiveEntries.Row X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mY → RecursiveEntries.Column X Y (SourceConstruction.Items s V) s q₁ q₂ w Q k)) :
      RecursiveEntries.table F'
        (SourceCoordinateConjugacy.activityNew π activity)
        (tailsMap π eX eY ξ) k
        (sampleEquiv π eX eY k mX mY p).1
        (sampleEquiv π eX eY k mX mY p).2 =
      RecursiveEntries.table F activity ξ k p.1 p.2 := by
    change RecursiveEntries.table F'
      (SourceCoordinateConjugacy.activityNew π activity)
      (tailsMap π eX eY ξ) k
      (fun i => eqv.1 (p.1 i)) (fun j => eqv.2 (p.2 j)) =
      RecursiveEntries.table F activity ξ k p.1 p.2
    exact SourceSuccessorConjugacy.table_map π eX eY F F' hF
      activity ξ k p.1 p.2
  have hp := paired_pushes (V := V) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs μ μ' ν ν' π eX eY hX hY k mX mY
    (fun p => E (RecursiveEntries.table F'
      (SourceCoordinateConjugacy.activityNew π activity)
      (tailsMap π eX eY ξ) k p.1 p.2))
  calc
    (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hs μ ν k mX mY).toFiniteLaw.prob
        (fun p => E (RecursiveEntries.table F activity ξ k p.1 p.2)) =
      (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        hs μ ν k mX mY).toFiniteLaw.prob
          (fun p => E (RecursiveEntries.table F'
            (SourceCoordinateConjugacy.activityNew π activity)
            (tailsMap π eX eY ξ) k
            (sampleEquiv π eX eY k mX mY p).1
            (sampleEquiv π eX eY k mX mY p).2)) := by
        congr 1
        funext p
        exact propext (by rw [htable p])
    _ = _ := hp

/-- Any deterministic postprocessing of the complete table inherits the
same arbitrary-event law. This includes a literal row-major encoding once
that encoding is supplied as `out`. -/
theorem output_event_prob [NeZero s] {O : Type} (mX mY : ℕ)
    (out : (Fin mX → Fin mY → Bool) → O)
    (hs : 4 ≤ s)
    (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') (eY : Y ≃ Y')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (F : X → Y → Bool) (F' : X' → Y' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X Y (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k : ℕ) (E : O → Prop) :
    (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hs μ ν k mX mY).toFiniteLaw.prob
        (fun p => E (out (RecursiveEntries.table F activity ξ k p.1 p.2))) =
    (pairedLaw (V := V) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hs μ' ν' k mX mY).toFiniteLaw.prob
        (fun p => E (out (RecursiveEntries.table F'
          (SourceCoordinateConjugacy.activityNew π activity)
          (tailsMap π eX eY ξ) k p.1 p.2))) :=
  table_event_prob hs μ μ' ν ν' π eX eY hX hY F F' hF
    activity ξ k mX mY (fun table => E (out table))

end Paper2.SampledTableLawConjugacy

#print axioms Paper2.SampledTableLawConjugacy.paired_weight
#print axioms Paper2.SampledTableLawConjugacy.paired_pushes
#print axioms Paper2.SampledTableLawConjugacy.table_event_prob
#print axioms Paper2.SampledTableLawConjugacy.output_event_prob
