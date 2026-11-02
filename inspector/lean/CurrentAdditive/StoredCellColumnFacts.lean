import CurrentAdditive.StoredCellQueryFacts

namespace CurrentAdditive.StoredCellQueries
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery
noncomputable section

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

theorem metadata_inl_result (bin : Fin s) (h : st.metadata.decode m selected.1=.inl bin) :
    metadataTag.result x=some [false] ∧ metadataIndex.result x=some bin.val.bits := by
  have hp := metadataPair_result src st out R activity selected m b z
  rw [h] at hp
  exact ⟨field_packet (0 : Fin 2) metadataPair x _ hp,
    field_packet (1 : Fin 2) metadataPair x _ hp⟩

theorem metadata_inr_result (i : Fin ni) (h : st.metadata.decode m selected.1=.inr i) :
    metadataTag.result x=some [true] ∧ metadataIndex.result x=some i.val.bits := by
  have hp := metadataPair_result src st out R activity selected m b z
  rw [h] at hp
  exact ⟨field_packet (0 : Fin 2) metadataPair x _ hp,
    field_packet (1 : Fin 2) metadataPair x _ hp⟩

theorem column_inl_result (a : Fin src.outer.size × Fin src.gamma.size) (h : selected.2=.inl a) :
    columnTag.result x=some [false] ∧ columnPair.result x=
      some (BitMachineBankCodec.encode ![a.1.val.bits,a.2.val.bits]) := by
  have hp := columnFamily_result src st out R activity selected m b z
  rw [h] at hp
  change columnFamily.result x=some (BitMachineBankCodec.encode ![[false],(finProdFinEquiv a).val.bits]) at hp
  have ht := field_packet (0 : Fin 2) columnFamily x _ hp
  have hi := field_packet (1 : Fin 2) columnFamily x _ hp
  refine ⟨ht,?_⟩
  apply branch_result columnTag _ _ x _ false ht
  change (lookup (companion 3) columnIndex).result x=some _
  apply product_lookup _ _ x a
  · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 3
  · exact hi

theorem column_inr_result (a : Fin q₂ × Fin src.gamma.size) (h : selected.2=.inr a) :
    columnTag.result x=some [true] ∧ columnPair.result x=
      some (BitMachineBankCodec.encode ![a.1.val.bits,a.2.val.bits]) := by
  have hp := columnFamily_result src st out R activity selected m b z
  rw [h] at hp
  change columnFamily.result x=some (BitMachineBankCodec.encode ![[true],(finProdFinEquiv a).val.bits]) at hp
  have ht := field_packet (0 : Fin 2) columnFamily x _ hp
  have hi := field_packet (1 : Fin 2) columnFamily x _ hp
  refine ⟨ht,?_⟩
  apply branch_result columnTag _ _ x _ true ht
  change (lookup (companion 1) columnIndex).result x=some _
  apply product_lookup _ _ x a
  · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 1
  · exact hi

end
end CurrentAdditive.StoredCellQueries

#print axioms CurrentAdditive.StoredCellQueries.column_inl_result
#print axioms CurrentAdditive.StoredCellQueries.column_inr_result
