import CurrentAdditive.V39RecursiveTable
import Paper2.SourceSuccessorConjugacy

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

namespace CurrentAdditive.V39SelectorTransport
open Paper2 SourceMatrix SourceCoordinateConjugacy
open V39RecursiveGenerator

variable {X X' Y Y' : Type} {q₁ q₂ s w Q : ℕ}

/-- Both current tags keep their identity. Only selector coordinates and
the recursively retained payload values are changed. -/
def taggedMap (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    V38Matrix.TaggedColumn q₁ q₂ s Y → V38Matrix.TaggedColumn q₁ q₂ s Y'
  | .inl Z => .inl (rawColumnMap π eY Z)
  | .inr j => .inr (outerMap π eY j)

theorem taggedMap_inverse (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (Z : V38Matrix.TaggedColumn q₁ q₂ s Y) :
    taggedMap π.symm eY.symm (taggedMap π eY Z) = Z := by
  cases Z with
  | inl Z => exact congrArg Sum.inl (rawColumnMap_inverse π eY Z)
  | inr j => exact congrArg Sum.inr (outerMap_inverse π eY j)

def taggedEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    V38Matrix.TaggedColumn q₁ q₂ s Y ≃ V38Matrix.TaggedColumn q₁ q₂ s Y' where
  toFun := taggedMap π eY
  invFun := taggedMap π.symm eY.symm
  left_inv := taggedMap_inverse π eY
  right_inv := taggedMap_inverse π.symm eY.symm

def rowEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    V38OneStep.RowLabel q₁ q₂ s w Q Y ≃ V38OneStep.RowLabel q₁ q₂ s w Q Y' :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr (Equiv.refl (Fin w)) (taggedEquiv π eY))

def columnEquiv {n : ℕ} (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') :
    V38OneStep.ColumnLabel q₁ q₂ s w Q X (Fin n) ≃
      V38OneStep.ColumnLabel q₁ q₂ s w Q X' (Fin n) :=
  SourceSuccessorConjugacy.columnEquiv π eX

theorem eraseTag_map (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (Z : V38Matrix.TaggedColumn q₁ q₂ s Y) :
    V39RecursiveTable.eraseTag (taggedMap π eY Z) =
      rawColumnMap π eY (V39RecursiveTable.eraseTag Z) := by
  cases Z with
  | inl Z => rfl
  | inr j => rfl

variable (n p q₁ q₂ s w Q : ℕ)

/-- Actual current complete carriers, with an identity seed and the same
selector change at each recursive level. No labels are removed or merged. -/
def carrierEquivs (π : Fin q₂ ≃ Fin q₂) : (k : ℕ) →
    (Row n p q₁ q₂ s w Q k ≃ Row n p q₁ q₂ s w Q k) ×
    (Column n p q₁ q₂ s w Q k ≃ Column n p q₁ q₂ s w Q k)
  | 0 => (Equiv.refl _,Equiv.refl _)
  | k+1 =>
    let previous := carrierEquivs π k
    (rowEquiv π previous.2,columnEquiv π previous.1)

abbrev eR (π : Fin q₂ ≃ Fin q₂) (k : ℕ) := (carrierEquivs n p q₁ q₂ s w Q π k).1
abbrev eC (π : Fin q₂ ≃ Fin q₂) (k : ℕ) := (carrierEquivs n p q₁ q₂ s w Q π k).2

variable {n p q₁ q₂ s w Q} [NeZero s]

theorem request_map (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k : ℕ)
    (x : Row n p q₁ q₂ s w Q (k+1)) (y : Column n p q₁ q₂ s w Q (k+1)) :
    V39RecursiveTable.request (activityNew π A) k
      (eR n p q₁ q₂ s w Q π (k+1) x) (eC n p q₁ q₂ s w Q π (k+1) y) =
    (eR n p q₁ q₂ s w Q π k (V39RecursiveTable.request A k x y).1,
      eC n p q₁ q₂ s w Q π k (V39RecursiveTable.request A k x y).2) := by
  change baseRequest (activityNew π A)
    (rawRowMap π (eR n p q₁ q₂ s w Q π k) (y.2 (x y.1).1))
    (V39RecursiveTable.eraseTag (taggedMap π (eC n p q₁ q₂ s w Q π k) (x y.1).2)) = _
  rw [eraseTag_map]
  exact baseRequest_map π _ _ A _ _

/-- Exact recursive entry equality for the current two-family construction. -/
theorem matrix_map (π : Fin q₂ ≃ Fin q₂)
    (A : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s)) (k : ℕ)
    (x : Row n p q₁ q₂ s w Q k) (y : Column n p q₁ q₂ s w Q k) :
    V39RecursiveTable.matrix (activityNew π A) k
      (eR n p q₁ q₂ s w Q π k x) (eC n p q₁ q₂ s w Q π k y) =
      V39RecursiveTable.matrix A k x y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change V39RecursiveTable.matrix (activityNew π A) k
      (V39RecursiveTable.request (activityNew π A) k _ _).1
      (V39RecursiveTable.request (activityNew π A) k _ _).2 =
        V39RecursiveTable.matrix A k (V39RecursiveTable.request A k x y).1
          (V39RecursiveTable.request A k x y).2
    rw [request_map]
    exact ih _ _

end CurrentAdditive.V39SelectorTransport

#print axioms CurrentAdditive.V39SelectorTransport.request_map
#print axioms CurrentAdditive.V39SelectorTransport.matrix_map
