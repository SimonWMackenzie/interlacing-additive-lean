import Paper2.SourceConstruction
import Paper2.SourceRepetition

/-!
Concrete, computable labels for indexed graph instances.  This is only a
labeling layer: it does not replace SourceConstruction.coordinateEquiv.
-/

namespace Paper2.CanonicalSourceLabels

open SourceItems SourcePadding SourceProfileParameters SourceRepetitionScratch

/-- The fixed numeric order is `none=0`, `some false=1`, `some true=2`. -/
def optionBoolIndex : Option Bool ≃ Fin 3 where
  toFun
    | none => 0
    | some false => 1
    | some true => 2
  invFun i := if i.val = 0 then none else if i.val = 1 then some false else some true
  left_inv x := by cases x with
    | none => rfl
    | some b => cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] theorem optionBoolIndex_none : optionBoolIndex none = 0 := rfl
@[simp] theorem optionBoolIndex_false : optionBoolIndex (some false) = 1 := rfl
@[simp] theorem optionBoolIndex_true : optionBoolIndex (some true) = 2 := rfl

/-- Row-major true-coordinate index: group, indexed edge occurrence, then
the three-valued label. Distinct parallel edge occurrences remain distinct. -/
def coordIndex (s m : ℕ) : Coord (Fin (4 * s)) (Fin m) ≃ Fin (12 * s * m) :=
  (((Equiv.refl (Fin (4 * s))).prodCongr
    ((Equiv.refl (Fin m)).prodCongr optionBoolIndex)).trans
  ((Equiv.refl (Fin (4 * s))).prodCongr finProdFinEquiv)).trans
  (finProdFinEquiv.trans (finCongr (by ring)))

theorem coordIndex_val (s m : ℕ) (c : Coord (Fin (4 * s)) (Fin m)) :
    (coordIndex s m c).val =
      c.1.val * (m * 3) + c.2.1.val * 3 + (optionBoolIndex c.2.2).val := by
  simp [coordIndex, finProdFinEquiv, finCongr_apply]
  ring

theorem coordIndex_roundtrip (s m : ℕ)
    (c : Coord (Fin (4 * s)) (Fin m)) :
    (coordIndex s m).symm (coordIndex s m c) = c :=
  (coordIndex s m).symm_apply_apply c

private theorem raw_le_q0 (s m : ℕ) :
    12 * s * m ≤ sourceQ0 (Fin (4 * s)) (Fin m) := by
  have hc : Fintype.card (Coord (Fin (4 * s)) (Fin m)) = 12 * s * m := by
    rw [card_coord, Fintype.card_fin, Fintype.card_fin]
    ring
  rw [sourceQ0, hc]
  exact le_powTwoCeil _

/-- True coordinates occupy the initial block; padding follows numerically. -/
def paddedIndex (s m : ℕ) :
    Padded (Coord (Fin (4 * s)) (Fin m))
      (sourceQ0 (Fin (4 * s)) (Fin m)) ≃
      Fin (sourceQ0 (Fin (4 * s)) (Fin m)) :=
  ((coordIndex s m).sumCongr (finCongr (by
      rw [card_coord, Fintype.card_fin, Fintype.card_fin]))).trans
    finSumFinEquiv |>.trans (finCongr (by
      have h := raw_le_q0 s m
      have heq : 3 * (4 * s) * m = 12 * s * m := by ring
      rw [heq]
      exact Nat.add_sub_of_le h))

/-- Repetition is the innermost index: a padded coordinate at index `j`
and copy `t` has flattened index `j * rep + t`. -/
def sourceCoordIndex (s m rep : ℕ) :
    SourceCoord (Fin (4 * s)) (Fin m) rep ≃
      Fin (sourceQ0 (Fin (4 * s)) (Fin m) * rep) :=
  ((paddedIndex s m).prodCongr (Equiv.refl (Fin rep))).trans finProdFinEquiv

theorem sourceCoordIndex_val (s m rep : ℕ)
    (c : SourceCoord (Fin (4 * s)) (Fin m) rep) :
    (sourceCoordIndex s m rep c).val = (paddedIndex s m c.1).val * rep + c.2.val := by
  simp [sourceCoordIndex, finProdFinEquiv]
  ring

theorem sourceCoordIndex_card (s m rep : ℕ) :
    Fintype.card (SourceCoord (Fin (4 * s)) (Fin m) rep) =
      sourceQ0 (Fin (4 * s)) (Fin m) * rep := by
  simpa using Fintype.card_congr (sourceCoordIndex s m rep)

/-- Inverse of the flattened index, transported across an exact public width. -/
def coordOrder (s m rep q₂ : ℕ)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * rep) :
    Fin q₂ ≃ SourceCoord (Fin (4 * s)) (Fin m) rep :=
  (finCongr hq).trans (sourceCoordIndex s m rep).symm

theorem coordOrder_roundtrip (s m rep q₂ : ℕ)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin m) * rep)
    (a : Fin q₂) :
    (coordOrder s m rep q₂ hq).symm (coordOrder s m rep q₂ hq a) = a :=
  (coordOrder s m rep q₂ hq).symm_apply_apply a

/-- The width in the output is the actual scheduled `outerWidth`; `rep` is
the quotient of the two public widths, not a selected witness. -/
def publicCoordOrder (L m : ℕ)
    (h : coordinateAdmissible L (Fin m)) :
    Fin (outerWidth L) ≃
      SourceCoord (Fin (4 * width L)) (Fin m) (sourceRep L (Fin m)) :=
  coordOrder (width L) m (sourceRep L (Fin m)) (outerWidth L)
    (outerWidth_eq_sourceQ0_mul_rep L (Fin m) h)

theorem publicCoordOrder_card (L m : ℕ)
    (h : coordinateAdmissible L (Fin m)) :
    Fintype.card
      (SourceCoord (Fin (4 * width L)) (Fin m) (sourceRep L (Fin m))) =
      outerWidth L := by
  rw [sourceCoordIndex_card]
  exact (outerWidth_eq_sourceQ0_mul_rep L (Fin m) h).symm

/-- Item order: group-major; within a group vertices `0,...,n-1` precede
the auxiliary labels `0,...,s-4`. -/
def itemIndex (s n : ℕ) :
    SourceConstruction.Items s (Fin n) ≃ Fin (4 * s * (n + (s - 3))) :=
  ((Equiv.refl (Fin (4 * s))).prodCongr finSumFinEquiv).trans finProdFinEquiv

theorem itemIndex_card (s n : ℕ) :
    Fintype.card (SourceConstruction.Items s (Fin n)) =
      4 * s * (n + (s - 3)) := by
  simp [Fintype.card_congr (itemIndex s n)]

/-- The same order, with exactly the cardinal domain required by the source
construction's `order` parameter. -/
def itemOrder (s n : ℕ) :
    SourceConstruction.Items s (Fin n) ≃
      Fin (Fintype.card (SourceConstruction.Items s (Fin n))) :=
  (itemIndex s n).trans (finCongr (itemIndex_card s n).symm)

theorem itemIndex_roundtrip (s n : ℕ)
    (i : SourceConstruction.Items s (Fin n)) :
    (itemIndex s n).symm (itemIndex s n i) = i :=
  (itemIndex s n).symm_apply_apply i

theorem itemIndex_vertex_val (s n : ℕ) (g : Fin (4 * s)) (v : Fin n) :
    (itemIndex s n (g, .inl v)).val = g.val * (n + (s - 3)) + v.val := by
  simp [itemIndex, finProdFinEquiv]
  ring

theorem itemIndex_aux_val (s n : ℕ) (g : Fin (4 * s)) (a : Fin (s - 3)) :
    (itemIndex s n (g, .inr a)).val =
      g.val * (n + (s - 3)) + n + a.val := by
  simp [itemIndex, finProdFinEquiv]
  ring

-- Concrete executable checks: `m=2` supports two separate edge labels even
-- when an external endpoint function gives them the same endpoints.
#eval (optionBoolIndex none).val
#eval (optionBoolIndex (some false)).val
#eval (optionBoolIndex (some true)).val
#eval (coordIndex 3 2 (⟨0, by decide⟩, ⟨0, by decide⟩, none)).val
#eval (coordIndex 3 2 (⟨0, by decide⟩, ⟨1, by decide⟩, none)).val
#eval coordOrder 3 2 2 256 (by decide) ⟨1, by decide⟩
#eval coordOrder 3 2 2 256 (by decide) ⟨144, by decide⟩
def parallelEdge : Fin 2 → Bool → Fin 2 := fun _ b => if b then 1 else 0
#eval parallelEdge 0 false
#eval parallelEdge 1 false
#eval decide ((coordIndex 3 2 (⟨0, by decide⟩, ⟨0, by decide⟩, none)) ≠
  (coordIndex 3 2 (⟨0, by decide⟩, ⟨1, by decide⟩, none)))
-- With no edges, every coordinate is padding, but the copy labels remain.
#eval coordOrder 3 0 2 2 (by decide) ⟨0, by decide⟩
#eval coordOrder 3 0 2 2 (by decide) ⟨1, by decide⟩
#eval (itemIndex 4 2 (⟨0, by decide⟩, .inl ⟨1, by decide⟩)).val
#eval (itemIndex 4 2 (⟨0, by decide⟩, .inr ⟨0, by decide⟩)).val

#print axioms coordIndex_roundtrip
#print axioms coordIndex_val
#print axioms coordOrder_roundtrip
#print axioms sourceCoordIndex_val
#print axioms sourceCoordIndex_card
#print axioms publicCoordOrder_card
#print axioms itemIndex_roundtrip
#print axioms itemIndex_card
#print axioms itemIndex_vertex_val
#print axioms itemIndex_aux_val

end Paper2.CanonicalSourceLabels
