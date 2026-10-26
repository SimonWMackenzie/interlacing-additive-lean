import CurrentAdditive.StoredSourceAccess

namespace CurrentAdditive.StoredSourceQueries
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery StoredCellQueries
noncomputable section
attribute [local instance] Classical.propDecidable

section Input
variable {D q₁ q₂ s w Q nx ny ni : Nat}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList D Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
  (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
  (selected : Fin w × src.Column) (m : Fin st.metadata.size)
  (b : Fin st.base.size) (z : Fin st.selector.size)

local notation "x" => StoredCellBytes.input src st out R activity selected m b z
local notation "Z" => src.decodeColumn (Prod.snd selected)

theorem firstCoordinate_result : firstCoordinate.result x=some (Z.2 0).1.val.bits := by
  cases h : selected.2 with
  | inl a =>
    simpa only [h,SourceData.decodeColumn] using firstCoordinate_inl_result src st out R activity selected m b z a h
  | inr a =>
    simpa only [h,SourceData.decodeColumn] using firstCoordinate_inr_result src st out R activity selected m b z a h

theorem diagonal_result : diagonal.result x=some [decide (∀p,(Z.2 p).1=(Z.2 0).1)] := by
  cases h : selected.2 with
  | inl a =>
    have ht := (column_inl_result src st out R activity selected m b z a h).1
    have hg := ordinaryDiagonal_result x (src.outer.decode a.1 0).1 (src.outer.decode a.1)
      (firstCoordinate_inl_result src st out R activity selected m b z a h)
      (by simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 1)
      (outerWord_result src st out R activity selected m b z a h)
    simpa only [h,SourceData.decodeColumn] using branch_result columnTag ordinaryDiagonal (total (StoredCellPrimitives.constantBit true)) x _ false ht hg
  | inr a =>
    have ht := (column_inr_result src st out R activity selected m b z a h).1
    have hb : (total (StoredCellPrimitives.constantBit true)).result x=some [true] := rfl
    simpa [h,SourceData.decodeColumn] using branch_result columnTag ordinaryDiagonal
      (total (StoredCellPrimitives.constantBit true)) x [true] true ht hb

theorem position_result (i : Fin ni) (hi : st.metadata.decode m selected.1=.inr i) :
    position.result x=some (SourceMatrix.sourcePosition activity i Z).val.bits := by
  have hd := diagonal_result src st out R activity selected m b z
  have ha := activityPosition_result src st out R activity selected m b z i (Z.2 0).1 hi
    (firstCoordinate_result src st out R activity selected m b z)
  have hn := neutralPosition_result src st out R activity selected m b z
  by_cases h : ∀p,(Z.2 p).1=(Z.2 0).1
  · have hd' : diagonal.result x=some [true] := by simpa [h] using hd
    have hp := branch_result diagonal neutralPosition activityPosition x _ true hd' ha
    have he : (SourceMatrix.sourcePosition activity i Z).val=
        StoredStepContext.activityValue activity i (Z.2 0).1 := by
      simp only [SourceMatrix.sourcePosition,if_pos h,StoredStepContext.activityValue]
      cases activity i (Z.2 0).1 <;> rfl
    simpa only [position,he] using hp
  · have hd' : diagonal.result x=some [false] := by simpa [h] using hd
    have hp := branch_result diagonal neutralPosition activityPosition x _ false hd' hn
    simpa only [position,SourceMatrix.sourcePosition,if_neg h,Fin.val_last] using hp

theorem tailIndex_result (i : Fin ni) (hi : st.metadata.decode m selected.1=.inr i) :
    tailIndex.result x=some (BitMachineBinaryAddAny.addAny q₁.bits
      (SourceMatrix.sourcePosition activity i Z).val.bits false) := by
  have hp := pair_result q1Bits position x _ _ (q1Bits_result src st out R activity selected m b z)
    (position_result src st out R activity selected m b z i hi)
  exact compose_result _ _ x _ _ hp (by simp only [total,StoredBinaryAdd.result_packet])

end Input
end
end CurrentAdditive.StoredSourceQueries

#print axioms CurrentAdditive.StoredSourceQueries.position_result
#print axioms CurrentAdditive.StoredSourceQueries.tailIndex_result
