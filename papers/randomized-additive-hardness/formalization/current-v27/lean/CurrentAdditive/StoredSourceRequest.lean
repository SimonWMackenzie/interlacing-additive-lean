import CurrentAdditive.StoredSourcePosition

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CurrentAdditive.StoredSourceQueries
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery StoredCellQueries
noncomputable section

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

theorem column_from_gamma_result (i : Fin ni) (hi : st.metadata.decode m selected.1=.inr i)
    (g : Fin src.gamma.size)
    (hw : globalGammaWord.result x=some (StoredCellBytes.tuple (fun p => (src.gamma.decode g p).val)))
    (hg : Z.1=SourceMatrix.tail (src.gamma.decode g)) :
    column.result x=some (SourceMatrix.sourceColumn activity i Z).val.bits := by
  let pos := SourceMatrix.sourcePosition activity i Z
  let idx : Fin (q₁+s+1) := ⟨q₁+pos.val,by have := pos.isLt;omega⟩
  let bits := BitMachineBinaryAddAny.addAny q₁.bits pos.val.bits false
  have hv : EncodedCommunication.bitsValue bits=idx.val := by
    simp only [bits,idx,StoredBinaryAdd.output_value,EncodedCommunication.bitsValue_bits]
  have hp := tailIndex_result src st out R activity selected m b z i hi
  have hl := lookup_ofFn globalGammaWord tailIndex x bits
    (fun p => (src.gamma.decode g p).val.bits) idx hw hp hv
  have hy : src.gamma.decode g idx=SourceMatrix.sourceColumn activity i Z := by
    unfold SourceMatrix.sourceColumn
    rw [hg]
    rfl
  simpa only [hy] using hl

theorem column_result (i : Fin ni) (hi : st.metadata.decode m selected.1=.inr i) :
    column.result x=some (SourceMatrix.sourceColumn activity i Z).val.bits := by
  cases h : selected.2 with
  | inl a =>
    rw [← h]
    apply column_from_gamma_result src st out R activity selected m b z i hi a.2
    · exact gammaWord_result src st out R activity selected m b z a.1 a.2
        (column_inl_result src st out R activity selected m b z a h).2
    · simp only [h,SourceData.decodeColumn]
  | inr a =>
    rw [← h]
    apply column_from_gamma_result src st out R activity selected m b z i hi a.2
    · exact gammaWord_result src st out R activity selected m b z a.1 a.2
        (column_inr_result src st out R activity selected m b z a h).2
    · simp only [h,SourceData.decodeColumn]

theorem request_result (i : Fin ni) (hi : st.metadata.decode m selected.1=.inr i) :
    request.result x=some (BitMachineBankCodec.encode
      ![(st.base.decode b selected.1).val.bits,
        (SourceMatrix.sourceColumn activity i Z).val.bits]) := by
  exact pair_result sourceRow column x _ _
    (sourceRow_result src st out R activity selected m b z)
    (column_result src st out R activity selected m b z i hi)

/-- This is the actual source-arm execution. Only the intrinsic metadata
case is assumed; the diagonal test, activity position, and tail read are all
performed by the fixed machine. Its polynomial is fixed before all data. -/
theorem outputs (i : Fin ni) (hi : st.metadata.decode m selected.1=.inr i) :
    request.machine.OutputsWithin x (BitMachineBankCodec.encode
      ![(st.base.decode b selected.1).val.bits,
        (SourceMatrix.sourceColumn activity i Z).val.bits])
      (request.coefficient*((x).length+1)^request.degree) :=
  request.outputs x _ (request_result src st out R activity selected m b z i hi)

end Input
end
end CurrentAdditive.StoredSourceQueries

#print axioms CurrentAdditive.StoredSourceQueries.request_result
#print axioms CurrentAdditive.StoredSourceQueries.outputs
