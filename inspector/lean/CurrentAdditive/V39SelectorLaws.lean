import CurrentAdditive.V39SelectorConjugacy
import Paper2.SourceLawCoordinateTransport

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

namespace CurrentAdditive.V39SelectorTransport
noncomputable section
open Paper2 SourceMatrix SourceCoordinateConjugacy V39RecursiveGenerator

variable {X X' Y Y' : Type} [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
  {q₁ q₂ s w Q n : ℕ}

/-- The literal 255/256 ordinary and 1/256 diagonal law is preserved.
No three-family tagged law is used here. -/
theorem tagged_weight [NeZero q₂]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (Z : V38Matrix.TaggedColumn q₁ q₂ s Y) :
    (V38Matrix.taggedLaw (q₁:=q₁) (q₂:=q₂) (s:=s) ν').weight (taggedMap π eY Z) =
      (V38Matrix.taggedLaw (q₁:=q₁) (q₂:=q₂) (s:=s) ν).weight Z := by
  cases Z with
  | inl Z => exact congrArg ((255/256 : ℚ) * ·) (SourceLawCoordinateTransport.raw_weight ν ν' π eY hY Z)
  | inr j => exact congrArg ((1/256 : ℚ) * ·) (SourceLawCoordinateTransport.outer_weight ν ν' π eY hY j)

theorem successorRow_weight [NeZero q₂] [NeZero w]
    (ν : PositiveRationalLaw Y) (ν' : PositiveRationalLaw Y')
    (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (hY : ∀ y, ν'.weight (eY y) = ν.weight y)
    (x : V38OneStep.RowLabel q₁ q₂ s w Q Y) :
    (V38OneStep.successorRowLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (w:=w) (Q:=Q) ν').weight
      (rowEquiv π eY x) =
    (V38OneStep.successorRowLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (w:=w) (Q:=Q) ν).weight x := by
  simp only [V38OneStep.successorRowLaw, PositiveRationalLaw.iid, PositiveRationalLaw.prod]
  apply Finset.prod_congr rfl
  intro i _
  change (PositiveRationalLaw.uniform (Fin w)).weight (x i).1 * _ = _
  exact congrArg ((PositiveRationalLaw.uniform (Fin w)).weight (x i).1 * ·)
    (tagged_weight ν ν' π eY hY (x i).2)

theorem successorColumn_weight [NeZero n] [NeZero q₁] [NeZero Q]
    (hs : 4 ≤ s) (μ : PositiveRationalLaw X) (μ' : PositiveRationalLaw X')
    (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (hX : ∀ x, μ'.weight (eX x) = μ.weight x)
    (y : V38OneStep.ColumnLabel q₁ q₂ s w Q X (Fin n)) :
    (V38OneStep.successorColumnLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (w:=w) (Q:=Q) (V:=Fin n) μ' hs).weight
      (columnEquiv π eX y) =
    (V38OneStep.successorColumnLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (w:=w) (Q:=Q) (V:=Fin n) μ hs).weight y := by
  simp only [V38OneStep.successorColumnLaw, PositiveRationalLaw.prod]
  congr 1
  simp only [PositiveRationalLaw.iid]
  apply Finset.prod_congr rfl
  intro i _
  exact SourceLawCoordinateTransport.matrixColumn_weight hs μ μ' π eX hX (y.2 i)

variable (n p q₁ q₂ s w Q : ℕ)
  [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂] [NeZero s]
  [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

/-- Both complete recursive laws retain their exact rational weights. -/
theorem laws_weight (π : Fin q₂ ≃ Fin q₂) (k : ℕ) :
    (∀ x, (laws n p q₁ q₂ s w Q k).1.weight (eR n p q₁ q₂ s w Q π k x) =
      (laws n p q₁ q₂ s w Q k).1.weight x) ∧
    (∀ y, (laws n p q₁ q₂ s w Q k).2.weight (eC n p q₁ q₂ s w Q π k y) =
      (laws n p q₁ q₂ s w Q k).2.weight y) := by
  induction k with
  | zero => exact ⟨fun _ => rfl,fun _ => rfl⟩
  | succ k ih =>
    exact ⟨successorRow_weight _ _ π _ ih.2,
      successorColumn_weight (by have h := NeZero.pos (s-3); omega) _ _ π _ ih.1⟩

def sampleEquiv (π : Fin q₂ ≃ Fin q₂) (k m : ℕ) :
    ((Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) ≃
      ((Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) :=
  Equiv.prodCongr
    (CoordinateLawTransport.tupleEquiv m (Equiv.refl _) (eR n p q₁ q₂ s w Q π k))
    (CoordinateLawTransport.tupleEquiv m (Equiv.refl _) (eC n p q₁ q₂ s w Q π k))

theorem sampleLaw_weight (π : Fin q₂ ≃ Fin q₂) (k m : ℕ) (z) :
    (sampleLaw n p q₁ q₂ s w Q k m).weight (sampleEquiv n p q₁ q₂ s w Q π k m z) =
      (sampleLaw n p q₁ q₂ s w Q k m).weight z := by
  obtain ⟨hr,hc⟩ := laws_weight n p q₁ q₂ s w Q π k
  simp only [sampleLaw, PositiveRationalLaw.prod]
  exact congrArg₂ (· * ·)
    (CoordinateLawTransport.iid_weight _ _ m (Equiv.refl _) _ hr z.1)
    (CoordinateLawTransport.iid_weight _ _ m (Equiv.refl _) _ hc z.2)

theorem pushes_of_weight {A B : Type} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) (e : A ≃ B)
    (h : ∀ a, ν.weight (e a) = μ.weight a) :
    μ.toFiniteLaw.PushesTo ν.toFiniteLaw e := by
  intro E
  classical
  unfold FiniteLaw.prob
  have hs := e.sum_comp (fun b => if E b then (ν.weight b : ℝ) else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw,h] using hs

theorem laws_pushes (π : Fin q₂ ≃ Fin q₂) (k : ℕ) :
    (laws n p q₁ q₂ s w Q k).1.toFiniteLaw.PushesTo
      (laws n p q₁ q₂ s w Q k).1.toFiniteLaw (eR n p q₁ q₂ s w Q π k) ∧
    (laws n p q₁ q₂ s w Q k).2.toFiniteLaw.PushesTo
      (laws n p q₁ q₂ s w Q k).2.toFiniteLaw (eC n p q₁ q₂ s w Q π k) := by
  obtain ⟨hr,hc⟩ := laws_weight n p q₁ q₂ s w Q π k
  exact ⟨pushes_of_weight _ _ _ hr,pushes_of_weight _ _ _ hc⟩

/-- Joint iid law, with every labelled position retained, including m=0. -/
theorem sampleLaw_pushes (π : Fin q₂ ≃ Fin q₂) (k m : ℕ) :
    (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.PushesTo
      (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw (sampleEquiv n p q₁ q₂ s w Q π k m) :=
  pushes_of_weight _ _ _ (sampleLaw_weight n p q₁ q₂ s w Q π k m)

end
end CurrentAdditive.V39SelectorTransport

#print axioms CurrentAdditive.V39SelectorTransport.laws_weight
#print axioms CurrentAdditive.V39SelectorTransport.sampleLaw_pushes
