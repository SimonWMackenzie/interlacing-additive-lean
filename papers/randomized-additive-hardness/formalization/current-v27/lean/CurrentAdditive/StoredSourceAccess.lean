import CurrentAdditive.StoredSourceDiagonal

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

theorem gammaWord_result {k : Nat} (a : Fin k) (g : Fin src.gamma.size)
    (hp : columnPair.result x=some (BitMachineBankCodec.encode ![a.val.bits,g.val.bits])) :
    globalGammaWord.result x=some (StoredCellBytes.tuple (fun p => (src.gamma.decode g p).val)) := by
  apply lookup_ofFn (source 0) (field (1 : Fin 2) columnPair) x g.val.bits
    (fun j => StoredCellBytes.tuple (fun p => (src.gamma.decode j p).val)) g
  · simpa [StoredCellBytes.sources,StoredCellBytes.gammaWords,StoredCellBytes.words]
      using source_result src st out R activity selected m b z 0
  · exact field_packet (1 : Fin 2) columnPair x _ hp
  · exact EncodedCommunication.bitsValue_bits _

theorem outerWord_result (a : Fin src.outer.size × Fin src.gamma.size)
    (h : selected.2=.inl a) : ordinaryOuterWord.result x=some
      (StoredCellBytes.tuple (fun p => (finProdFinEquiv (src.outer.decode a.1 p)).val)) := by
  have hp := (column_inl_result src st out R activity selected m b z a h).2
  apply lookup_ofFn (source 2) (field (0 : Fin 2) columnPair) x a.1.val.bits
    (fun j => StoredCellBytes.tuple (fun p => (finProdFinEquiv (src.outer.decode j p)).val)) a.1
  · simpa [StoredCellBytes.sources,StoredCellBytes.outerWords,StoredCellBytes.words]
      using source_result src st out R activity selected m b z 2
  · exact field_packet (0 : Fin 2) columnPair x _ hp
  · exact EncodedCommunication.bitsValue_bits _

theorem firstCoordinate_inl_result (a : Fin src.outer.size × Fin src.gamma.size)
    (h : selected.2=.inl a) : firstCoordinate.result x=some (src.outer.decode a.1 0).1.val.bits := by
  have ht := (column_inl_result src st out R activity selected m b z a h).1
  have hw := outerWord_result src st out R activity selected m b z a h
  have hl : firstOuterLabel.result x=some (finProdFinEquiv (src.outer.decode a.1 0)).val.bits := by
    apply lookup_ofFn ordinaryOuterWord zero x []
      (fun p => (finProdFinEquiv (src.outer.decode a.1 p)).val.bits) 0 hw rfl
    rfl
  have hp : firstOuterPair.result x=some (BitMachineBankCodec.encode
      ![(src.outer.decode a.1 0).1.val.bits,(src.outer.decode a.1 0).2.val.bits]) := by
    apply product_lookup _ _ x (src.outer.decode a.1 0)
    · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 1
    · exact hl
  exact branch_result columnTag _ _ x _ false ht
    (field_packet (0 : Fin 2) firstOuterPair x _ hp)

theorem firstCoordinate_inr_result (a : Fin q₂ × Fin src.gamma.size)
    (h : selected.2=.inr a) : firstCoordinate.result x=some a.1.val.bits := by
  obtain ⟨ht,hp⟩ := column_inr_result src st out R activity selected m b z a h
  exact branch_result columnTag _ _ x _ true ht (field_packet (0 : Fin 2) columnPair x _ hp)

theorem sourceRow_result : sourceRow.result x=some (st.base.decode b selected.1).val.bits := by
  apply lookup_ofFn baseWord coordinate x selected.1.val.bits
    (fun p => (st.base.decode b p).val.bits) selected.1
  · simpa [baseWord,StoredCellBytes.input,StoredCellBytes.tuple] using slot_result (3 : Fin 5) x
  · exact coordinate_result src st out R activity selected m b z
  · exact EncodedCommunication.bitsValue_bits _

theorem neutralPosition_result : neutralPosition.result x=some s.bits := by
  have hp : (publicField 2).result x=some (List.replicate s true) := by
    simpa [StoredStepContext.context] using public_result src st out R activity selected m b z 2
  exact compose_result _ _ x _ _ hp (by simp [total,StoredCellPrimitives.unaryBits])

theorem q1Bits_result : q1Bits.result x=some q₁.bits := by
  have hp : (publicField 0).result x=some (List.replicate q₁ true) := by
    simpa [StoredStepContext.context] using public_result src st out R activity selected m b z 0
  exact compose_result _ _ x _ _ hp (by simp [total,StoredCellPrimitives.unaryBits])

theorem activityPosition_result (i : Fin ni) (a : Fin q₂)
    (hi : st.metadata.decode m selected.1=.inr i)
    (ha : firstCoordinate.result x=some a.val.bits) : activityPosition.result x=
      some (StoredStepContext.activityValue activity i a).bits := by
  have hm := (metadata_inr_result src st out R activity selected m b z i hi).2
  have hp : (publicField 6).result x=some (StoredStepContext.activityWords activity) := by
    simpa [StoredStepContext.context] using public_result src st out R activity selected m b z 6
  have hw : activityWord.result x=some (SourceListEncoding.encode (List.ofFn
      (fun a : Fin q₂ => (StoredStepContext.activityValue activity i a).bits))) := by
    exact lookup_ofFn (publicField 6) metadataIndex x i.val.bits _ i hp hm
      (EncodedCommunication.bitsValue_bits _)
  exact lookup_ofFn activityWord firstCoordinate x a.val.bits _ a hw ha
    (EncodedCommunication.bitsValue_bits _)

end Input
end
end CurrentAdditive.StoredSourceQueries

#print axioms CurrentAdditive.StoredSourceQueries.activityPosition_result
