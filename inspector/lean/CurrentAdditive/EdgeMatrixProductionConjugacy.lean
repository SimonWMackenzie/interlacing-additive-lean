import CurrentAdditive.EdgeEncoder
import Paper2.SourceCoordinateConjugacy

namespace CurrentAdditive.LiteralEdgeEncoder

open Paper2 SourceMatrix
open SourceCoordinateConjugacy

variable {s n m r q₁ : ℕ} [NeZero s] {X Y : Type*}

abbrev Width (s m r : ℕ) := EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r

/-- Proof-side permutation from literal public selectors to the owner's
unspecified selectors. The executable construction never computes it. -/
noncomputable def selectorPermutation (s m r : ℕ) :
    Fin (Width s m r) ≃ Fin (Width s m r) :=
  (coordinateNumber s m r).symm.trans
    (EdgeSourceMatrix.coordinateEquiv (E := Fin m) r rfl).symm

theorem activity_eq_owner (hs : 3 ≤ s) (e : Fin m → Bool → Fin n) :
    activity hs e = activityNew (selectorPermutation s m r)
      (EdgeSourceMatrix.activity (itemOrder s n) e hs r rfl) := by
  funext i a
  rw [activity_eq_ordered]
  simp [activityNew, EdgeSourceMatrix.activity, selectorPermutation]

def taggedMap (π : Fin (Width s m r) ≃ Fin (Width s m r))
    (Z : V38Matrix.TaggedColumn q₁ (Width s m r) s Y) :
    V38Matrix.TaggedColumn q₁ (Width s m r) s Y :=
  match Z with
  | .inl Z => .inl (rawColumnMap π (Equiv.refl _) Z)
  | .inr j => .inr (outerMap π (Equiv.refl _) j)

theorem taggedMap_inverse (π : Fin (Width s m r) ≃ Fin (Width s m r))
    (Z : V38Matrix.TaggedColumn q₁ (Width s m r) s Y) :
    taggedMap π.symm (taggedMap π Z) = Z := by
  cases Z with
  | inl Z =>
      apply congrArg Sum.inl
      exact rawColumnMap_inverse π (Equiv.refl Y) Z
  | inr j =>
      apply congrArg Sum.inr
      exact outerMap_inverse π (Equiv.refl Y) j

def taggedEquiv (π : Fin (Width s m r) ≃ Fin (Width s m r)) :
    V38Matrix.TaggedColumn q₁ (Width s m r) s Y ≃
      V38Matrix.TaggedColumn q₁ (Width s m r) s Y where
  toFun := taggedMap π
  invFun := taggedMap π.symm
  left_inv := taggedMap_inverse π
  right_inv := taggedMap_inverse π.symm

theorem forgetTag_map (π : Fin (Width s m r) ≃ Fin (Width s m r))
    (ξ : Tail s Y) (Z : V38Matrix.TaggedColumn q₁ (Width s m r) s Y) :
    V38Matrix.forgetTag ξ (taggedMap π Z) =
      rawColumnMap π (Equiv.refl _) (V38Matrix.forgetTag ξ Z) := by
  cases Z with
  | inl Z => rfl
  | inr j => rfl

/-- Executable two-family transpose, on the exact v38/v39 carriers. -/
def matrix (hs : 3 ≤ s) (e : Fin m → Bool → Fin n) (R : X → Y → Bool)
    (ξ : Tail s Y) :
    V38Matrix.TaggedColumn q₁ (Width s m r) s Y →
      RawRow q₁ (Width s m r) s X (Items s n) → Bool :=
  fun Z k => raw R (activity hs e) k (V38Matrix.forgetTag ξ Z)

/-- Every transported entry agrees with the existing finite matrix. Both
ordinary and diagonal tags retain their identity, and template words are
reindexed along with the selectors. No table-identity premise is assumed. -/
theorem matrix_eq_owner [Fintype X] [Fintype Y]
    (hs : 3 ≤ s) (e : Fin m → Bool → Fin n) (R : X → Y → Bool)
    (ξ : Tail s Y) (Z : V38Matrix.TaggedColumn q₁ (Width s m r) s Y)
    (k : RawRow q₁ (Width s m r) s X (Items s n)) :
    matrix hs e R ξ (taggedMap (selectorPermutation s m r) Z)
      (rawRowMap (selectorPermutation s m r) (Equiv.refl X) k) =
      V38Matrix.matrix (itemOrder s n) e hs r rfl R ξ Z k := by
  unfold matrix V38Matrix.matrix
  rw [activity_eq_owner, forgetTag_map]
  simp only [raw, baseRequest_map, Equiv.refl_apply]

#print axioms activity_eq_owner
#print axioms matrix
#print axioms taggedEquiv
#print axioms matrix_eq_owner

end CurrentAdditive.LiteralEdgeEncoder
