import Paper2.SourceMatrix

/-!
# The actual diagonal entries at a collision witness

Frozen v12 Section 4, `src:near-full`, the four displayed base entries.
A diagonal word serves all ordinary head coordinates, the distinct positions
of two active items, and the neutral position of an inactive item. We exhibit
the coordinate injection explicitly. No retained representative, activity
injectivity, or lower bound is postulated by these identities.
-/

namespace Paper2.SourceProjectionDiagonal

open SourceMatrix

variable {X Y I : Type*} {q₁ q₂ s : ℕ}

/-- The two specified active positions followed by the neutral position. -/
def collisionTailPosition (p p' : Fin s) : Fin 3 → Fin (s + 1) :=
  Fin.cases p.castSucc (Fin.cases p'.castSucc (fun _ => Fin.last s))

@[simp] theorem collisionTailPosition_zero (p p' : Fin s) :
    collisionTailPosition p p' 0 = p.castSucc := rfl

@[simp] theorem collisionTailPosition_one (p p' : Fin s) :
    collisionTailPosition p p' 1 = p'.castSucc := rfl

@[simp] theorem collisionTailPosition_two (p p' : Fin s) :
    collisionTailPosition p p' 2 = Fin.last s := rfl

/-- Distinct active positions are also distinct from the neutral last slot. -/
theorem collisionTailPosition_injective (p p' : Fin s) (hpp : p ≠ p') :
    Function.Injective (collisionTailPosition p p') := by
  intro a b hab
  have hpp' : p.val ≠ p'.val := fun h => hpp (Fin.ext h)
  have hp := p.isLt
  have hp' := p'.isLt
  apply Fin.ext
  have hval := congrArg Fin.val hab
  fin_cases a <;> fin_cases b
  · rfl
  · change p.val = p'.val at hval
    omega
  · change p.val = s at hval
    omega
  · change p'.val = p.val at hval
    omega
  · rfl
  · change p'.val = s at hval
    omega
  · change s = p.val at hval
    omega
  · change s = p'.val at hval
    omega
  · rfl

/-- The explicit selection of all head coordinates and the three collision
tail coordinates. No order-preserving property is needed or asserted. -/
def selectedCoordinate (p p' : Fin s) :
    Fin q₁ ⊕ Fin 3 → Fin (q₁ + s + 1)
  | .inl r => ⟨r.val, by omega⟩
  | .inr t => ⟨q₁ + (collisionTailPosition p p' t).val, by
      have h := (collisionTailPosition p p' t).isLt
      omega⟩

@[simp] theorem selectedCoordinate_head (p p' : Fin s) (r : Fin q₁) :
    (selectedCoordinate p p' (.inl r)).val = r.val := rfl

@[simp] theorem selectedCoordinate_tail (p p' : Fin s) (t : Fin 3) :
    (selectedCoordinate (q₁ := q₁) p p' (.inr t)).val =
      q₁ + (collisionTailPosition p p' t).val := rfl

theorem selectedCoordinate_injective (p p' : Fin s) (hpp : p ≠ p') :
    Function.Injective (selectedCoordinate (q₁ := q₁) p p') := by
  intro a b hab
  have hval := congrArg Fin.val hab
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (Fin.ext hval)
  · simp only [selectedCoordinate_head, selectedCoordinate_tail] at hval
    have h := a.isLt
    omega
  · simp only [selectedCoordinate_head, selectedCoordinate_tail] at hval
    have h := b.isLt
    omega
  · simp only [selectedCoordinate_tail] at hval
    apply congrArg Sum.inr
    apply collisionTailPosition_injective p p' hpp
    apply Fin.ext
    omega

/-- The same concrete injection indexed by one finite ordinal. -/
def selectedCoordinateFin (p p' : Fin s) : Fin (q₁ + 3) → Fin (q₁ + s + 1) :=
  selectedCoordinate p p' ∘ finSumFinEquiv.symm

theorem selectedCoordinateFin_injective (p p' : Fin s) (hpp : p ≠ p') :
    Function.Injective (selectedCoordinateFin (q₁ := q₁) p p') :=
  (selectedCoordinate_injective p p' hpp).comp finSumFinEquiv.symm.injective

@[simp] theorem selected_word_head (p p' : Fin s) (γ : Word q₁ s Y) (r : Fin q₁) :
    γ (selectedCoordinate p p' (.inl r)) = head γ r := rfl

@[simp] theorem selected_word_tail (p p' : Fin s) (γ : Word q₁ s Y) (t : Fin 3) :
    γ (selectedCoordinate p p' (.inr t)) = tail γ (collisionTailPosition p p' t) := rfl

section Entries

variable [NeZero s]

theorem diagonal_template_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (γ : Word q₁ s Y) (b : Fin s) (z : Template q₁ q₂ X) :
    N R activity ξ₀ (.diagonal (α, γ)) (.inl (b, z)) =
      R (z α).2 (head γ (z α).1) := rfl

theorem diagonal_active_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (γ : Word q₁ s Y) (i : I) (u : X) (p : Fin s)
    (hi : activity i α = some p) :
    N R activity ξ₀ (.diagonal (α, γ)) (.inr (i, u)) = R u (tail γ p.castSucc) := by
  change R u (tail γ (sourcePosition activity i (forgetTag ξ₀ (.diagonal (α, γ))))) = _
  rw [sourcePosition_diagonal]
  simp [hi]

theorem diagonal_inactive_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (γ : Word q₁ s Y) (i : I) (u : X)
    (hi : activity i α = none) :
    N R activity ξ₀ (.diagonal (α, γ)) (.inr (i, u)) = R u (tail γ (Fin.last s)) := by
  change R u (tail γ (sourcePosition activity i (forgetTag ξ₀ (.diagonal (α, γ))))) = _
  rw [sourcePosition_diagonal]
  simp [hi]

/-- The actual two active labels and inactive label, in collision order. -/
def collisionItem (i₁ i₂ i₀ : I) : Fin 3 → I :=
  Fin.cases i₁ (Fin.cases i₂ (fun _ => i₀))

/-- The source's computed positions, not separate surrogate coordinates,
are exactly the three selected tail positions. -/
theorem collision_source_positions
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (γ : Word q₁ s Y) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none) (t : Fin 3) :
    sourcePosition activity (collisionItem i₁ i₂ i₀ t)
        (forgetTag ξ₀ (.diagonal (α, γ))) = collisionTailPosition p p' t := by
  rw [sourcePosition_diagonal]
  fin_cases t
  · change (activity i₁ α).elim (Fin.last s) Fin.castSucc = p.castSucc
    rw [h₁]
    rfl
  · change (activity i₂ α).elim (Fin.last s) Fin.castSucc = p'.castSucc
    rw [h₂]
    rfl
  · change (activity i₀ α).elim (Fin.last s) Fin.castSucc = Fin.last s
    rw [h₀]
    rfl

/-- Consequently the actual three source positions are pairwise distinct. -/
theorem collision_source_positions_injective
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (γ : Word q₁ s Y) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none) (hpp : p ≠ p') :
    Function.Injective (fun t => sourcePosition activity (collisionItem i₁ i₂ i₀ t)
      (forgetTag ξ₀ (.diagonal (α, γ)))) := by
  intro a b hab
  simp only [collision_source_positions activity ξ₀ α γ i₁ i₂ i₀ p p' h₁ h₂ h₀] at hab
  exact collisionTailPosition_injective p p' hpp hab

/-- An actual template representative realizing `(r,u)` requests its
selected head coordinate for every word. The row is fixed before the word. -/
theorem diagonal_template_selected_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (b p p' : Fin s) (z : Template q₁ q₂ X)
    (r : Fin q₁) (u : X) (hz : z α = (r, u)) (γ : Word q₁ s Y) :
    N R activity ξ₀ (.diagonal (α, γ)) (.inl (b, z)) =
      R u (γ (selectedCoordinate p p' (.inl r))) := by
  rw [diagonal_template_entry, hz]
  rfl

/-- All three actual source rows request the selected tail coordinates.
The item and base-row labels are fixed before varying the diagonal word. -/
theorem diagonal_source_selected_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (α : Fin q₂) (i₁ i₂ i₀ : I) (p p' : Fin s)
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none) (t : Fin 3) (u : X) (γ : Word q₁ s Y) :
    N R activity ξ₀ (.diagonal (α, γ)) (.inr (collisionItem i₁ i₂ i₀ t, u)) =
      R u (γ (selectedCoordinate p p' (.inr t))) := by
  change R u (tail γ (sourcePosition activity (collisionItem i₁ i₂ i₀ t)
    (forgetTag ξ₀ (.diagonal (α, γ))))) = _
  rw [collision_source_positions activity ξ₀ α γ i₁ i₂ i₀ p p' h₁ h₂ h₀]
  rfl

end Entries

end Paper2.SourceProjectionDiagonal

#print axioms Paper2.SourceProjectionDiagonal.selectedCoordinateFin_injective
#print axioms Paper2.SourceProjectionDiagonal.collision_source_positions_injective
#print axioms Paper2.SourceProjectionDiagonal.diagonal_template_selected_entry
#print axioms Paper2.SourceProjectionDiagonal.diagonal_source_selected_entry
