import Paper2.SourceCoordinateConjugacy
import Paper2.RecursiveEntries

/-!
Exact relabelling of both final interlaces, continuing the checked one-step
source-coordinate conjugacy. This is a finite entry identity, not a runtime
or equality of outputs on the same random tape.
-/

namespace Paper2.SourceSuccessorConjugacy

open SourceMatrix SourceCoordinateConjugacy

variable {X X' Y Y' I : Type*} {q₁ q₂ s w Q : ℕ}

def rowEquiv (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y') :
    (Fin Q → Fin w × TaggedColumn q₁ q₂ s Y) ≃
      (Fin Q → Fin w × TaggedColumn q₁ q₂ s Y') :=
  Equiv.piCongrRight (fun _ =>
    Equiv.prodCongr (Equiv.refl (Fin w)) (taggedEquiv π eY))

def columnEquiv (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X') :
    (Fin Q × (Fin w → RawRow q₁ q₂ s X I)) ≃
      (Fin Q × (Fin w → RawRow q₁ q₂ s X' I)) :=
  Equiv.prodCongr (Equiv.refl (Fin Q))
    (Equiv.piCongrRight (fun _ => rawRowEquiv π eX))

@[simp] theorem rowEquiv_apply (π : Fin q₂ ≃ Fin q₂) (eY : Y ≃ Y')
    (x : Fin Q → Fin w × TaggedColumn q₁ q₂ s Y) (i : Fin Q) :
    rowEquiv π eY x i = ((x i).1, taggedMap π eY (x i).2) := rfl

@[simp] theorem columnEquiv_apply (π : Fin q₂ ≃ Fin q₂) (eX : X ≃ X')
    (y : Fin Q × (Fin w → RawRow q₁ q₂ s X I)) :
    columnEquiv π eX y = (y.1, fun i => rawRowMap π eX (y.2 i)) := rfl

theorem successor_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X ≃ X') (eY : Y ≃ Y') (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ : Tail s Y)
    (x : Fin Q → Fin w × TaggedColumn q₁ q₂ s Y)
    (y : Fin Q × (Fin w → RawRow q₁ q₂ s X I)) :
    successor (fun x' y' => R (eX.symm x') (eY.symm y'))
      (activityNew π activity) (tailMap eY ξ) w Q
      (rowEquiv π eY x) (columnEquiv π eX y) =
        successor R activity ξ w Q x y := by
  change N (fun x' y' => R (eX.symm x') (eY.symm y'))
    (activityNew π activity) (tailMap eY ξ)
    (taggedMap π eY (x y.1).2)
    (rawRowMap π eX (y.2 (x y.1).1)) = _
  exact N_map π eX eY R activity ξ _ _

theorem successor_map_of_entries [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X ≃ X') (eY : Y ≃ Y')
    (R : X → Y → Bool) (R' : X' → Y' → Bool)
    (hR : ∀ x y, R' (eX x) (eY y) = R x y)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ : Tail s Y)
    (x : Fin Q → Fin w × TaggedColumn q₁ q₂ s Y)
    (y : Fin Q × (Fin w → RawRow q₁ q₂ s X I)) :
    successor R' (activityNew π activity) (tailMap eY ξ) w Q
      (rowEquiv π eY x) (columnEquiv π eX y) =
        successor R activity ξ w Q x y := by
  have h : R' = fun x' y' => R (eX.symm x') (eY.symm y') := by
    funext x' y'
    simpa using hR (eX.symm x') (eY.symm y')
  rw [h]
  exact successor_map π eX eY R activity ξ x y

section Iteration

variable {X₀ X₀' Y₀ Y₀' J : Type}

/-- Explicit equivalences of the complete recursive carriers. No values or
labelled positions are identified. -/
def carrierEquivs (π : Fin q₂ ≃ Fin q₂) (eX : X₀ ≃ X₀') (eY : Y₀ ≃ Y₀') :
    (k : ℕ) →
      (RecursiveEntries.Row X₀ Y₀ J s q₁ q₂ w Q k ≃
        RecursiveEntries.Row X₀' Y₀' J s q₁ q₂ w Q k) ×
      (RecursiveEntries.Column X₀ Y₀ J s q₁ q₂ w Q k ≃
        RecursiveEntries.Column X₀' Y₀' J s q₁ q₂ w Q k)
  | 0 => (eX, eY)
  | k + 1 =>
      let previous := carrierEquivs π eX eY k
      (rowEquiv π previous.2, columnEquiv π previous.1)

def tailsMap (π : Fin q₂ ≃ Fin q₂) (eX : X₀ ≃ X₀') (eY : Y₀ ≃ Y₀')
    (ξ : RecursiveEntries.Tails X₀ Y₀ J s q₁ q₂ w Q) :
    RecursiveEntries.Tails X₀' Y₀' J s q₁ q₂ w Q :=
  fun k i => (carrierEquivs π eX eY k).2 (ξ k i)

theorem matrix_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X₀ ≃ X₀') (eY : Y₀ ≃ Y₀')
    (F : X₀ → Y₀ → Bool) (F' : X₀' → Y₀' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : J → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X₀ Y₀ J s q₁ q₂ w Q) (k : ℕ)
    (x : RecursiveEntries.Row X₀ Y₀ J s q₁ q₂ w Q k)
    (y : RecursiveEntries.Column X₀ Y₀ J s q₁ q₂ w Q k) :
    RecursiveEntries.matrix F' (activityNew π activity) (tailsMap π eX eY ξ) k
      ((carrierEquivs π eX eY k).1 x) ((carrierEquivs π eX eY k).2 y) =
        RecursiveEntries.matrix F activity ξ k x y := by
  induction k with
  | zero => exact hF x y
  | succ k ih =>
      exact successor_map_of_entries π
        (carrierEquivs π eX eY k).1 (carrierEquivs π eX eY k).2
        (RecursiveEntries.matrix F activity ξ k)
        (RecursiveEntries.matrix F' (activityNew π activity) (tailsMap π eX eY ξ) k)
        ih activity (ξ k) x y

theorem evaluate_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X₀ ≃ X₀') (eY : Y₀ ≃ Y₀')
    (F : X₀ → Y₀ → Bool) (F' : X₀' → Y₀' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : J → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X₀ Y₀ J s q₁ q₂ w Q) (k : ℕ)
    (x : RecursiveEntries.Row X₀ Y₀ J s q₁ q₂ w Q k)
    (y : RecursiveEntries.Column X₀ Y₀ J s q₁ q₂ w Q k) :
    RecursiveEntries.evaluate F' (activityNew π activity) (tailsMap π eX eY ξ) k
      ((carrierEquivs π eX eY k).1 x) ((carrierEquivs π eX eY k).2 y) =
        RecursiveEntries.evaluate F activity ξ k x y := by
  rw [RecursiveEntries.evaluate_eq_matrix, RecursiveEntries.evaluate_eq_matrix]
  exact matrix_map π eX eY F F' hF activity ξ k x y

/-- The relabelled sampled table agrees entry by entry, with repetitions
preserved. The sampled labels are transported, not regenerated on one tape. -/
theorem table_map [NeZero s] (π : Fin q₂ ≃ Fin q₂)
    (eX : X₀ ≃ X₀') (eY : Y₀ ≃ Y₀')
    (F : X₀ → Y₀ → Bool) (F' : X₀' → Y₀' → Bool)
    (hF : ∀ x y, F' (eX x) (eY y) = F x y)
    (activity : J → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails X₀ Y₀ J s q₁ q₂ w Q) (k : ℕ) {m n : ℕ}
    (xs : Fin m → RecursiveEntries.Row X₀ Y₀ J s q₁ q₂ w Q k)
    (ys : Fin n → RecursiveEntries.Column X₀ Y₀ J s q₁ q₂ w Q k) :
    RecursiveEntries.table F' (activityNew π activity) (tailsMap π eX eY ξ) k
      (fun i => (carrierEquivs π eX eY k).1 (xs i))
      (fun j => (carrierEquivs π eX eY k).2 (ys j)) =
        RecursiveEntries.table F activity ξ k xs ys := by
  funext i j
  exact evaluate_map π eX eY F F' hF activity ξ k (xs i) (ys j)

end Iteration

#print axioms successor_map
#print axioms successor_map_of_entries
#print axioms matrix_map
#print axioms evaluate_map
#print axioms table_map

end Paper2.SourceSuccessorConjugacy
