import CurrentAdditive.StoredCellQueries

namespace CurrentAdditive.StoredCellQueries
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery
noncomputable section

theorem field_packet {K : Nat} (j : Fin K) (A : Query) (x : List Bool)
    (S : Fin K → List Bool) (ha : A.result x=some (BitMachineBankCodec.encode S)) :
    (field j A).result x=some (S j) := by
  simpa only [BankFieldProjection.result_encode] using field_result j A x _ ha

theorem product_lookup (S I : Query) (x : List Bool) {m n : Nat} (a : Fin m × Fin n)
    (hs : S.result x=some (SourceListEncoding.encode (StoredCellBytes.productCompanions m n)))
    (hi : I.result x=some (finProdFinEquiv a).val.bits) :
    (lookup S I).result x=some (BitMachineBankCodec.encode ![a.1.val.bits,a.2.val.bits]) := by
  have h := lookup_ofFn S I x (finProdFinEquiv a).val.bits
    (fun k : Fin (m*n) => let ij:=finProdFinEquiv.symm k
      BitMachineBankCodec.encode ![ij.1.val.bits,ij.2.val.bits])
    (finProdFinEquiv a) hs hi (EncodedCommunication.bitsValue_bits _)
  simpa only [Equiv.symm_apply_apply] using h

def sumWord {m n : Nat} (a : Fin m ⊕ Fin n) : List Bool :=
  match a with
  | .inl i => BitMachineBankCodec.encode ![[false],i.val.bits]
  | .inr j => BitMachineBankCodec.encode ![[true],j.val.bits]

theorem sum_lookup (S I : Query) (x : List Bool) {m n : Nat} (a : Fin m ⊕ Fin n)
    (hs : S.result x=some (SourceListEncoding.encode (StoredCellBytes.sumCompanions m n)))
    (hi : I.result x=some (finSumFinEquiv a).val.bits) :
    (lookup S I).result x=some (sumWord a) := by
  have h := lookup_ofFn S I x (finSumFinEquiv a).val.bits
    (fun k : Fin (m+n) => sumWord (finSumFinEquiv.symm k))
    (finSumFinEquiv a) hs hi (EncodedCommunication.bitsValue_bits _)
  simpa only [Equiv.symm_apply_apply] using h

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

theorem context_result : context.result x=some (StoredCellBytes.context src st out R activity) := by
  simpa only [context,StoredCellBytes.input,BankFieldProjection.result_encode,Matrix.cons_val_zero]
    using slot_result (0 : Fin 5) x

theorem source_result (j : Fin 7) : (source j).result x=
    some (BankFieldProjection.result j (StoredCellBytes.sources src st out)) := by
  have h := field_packet (2 : Fin 4) context x _ (context_result src st out R activity selected m b z)
  exact field_result j sources x _ h

theorem companion_result (j : Fin 6) : (companion j).result x=
    some (BankFieldProjection.result j (StoredCellBytes.companions src (ni := ni) (w := w))) := by
  have h := field_packet (3 : Fin 4) context x _ (context_result src st out R activity selected m b z)
  exact field_result j companions x _ h

theorem public_result (j : Fin 7) : (publicField j).result x=
    some (BankFieldProjection.result j (StoredStepContext.context q₁ w Q μI activity)) := by
  have h := field_packet (0 : Fin 4) context x _ (context_result src st out R activity selected m b z)
  exact field_result j stepContext x _ h

theorem finalPair_result : finalPair.result x=
    some (BitMachineBankCodec.encode ![selected.1.val.bits,(src.columnOrder selected.2).val.bits]) := by
  apply product_lookup (companion 5) finalLabel x (selected.1,src.columnOrder selected.2)
  · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 5
  · simpa [finalLabel,StoredCellBytes.input] using slot_result (1 : Fin 5) x

theorem coordinate_result : coordinate.result x=some selected.1.val.bits := by
  exact field_packet (0 : Fin 2) finalPair x _ (finalPair_result src st out R activity selected m b z)

theorem columnLabel_result : columnLabel.result x=some (src.columnOrder selected.2).val.bits := by
  exact field_packet (1 : Fin 2) finalPair x _ (finalPair_result src st out R activity selected m b z)

theorem metadataLabel_result : metadataLabel.result x=
    some (finSumFinEquiv (st.metadata.decode m selected.1)).val.bits := by
  apply lookup_ofFn metadataWord coordinate x selected.1.val.bits
    (fun p : Fin w => (finSumFinEquiv (st.metadata.decode m p)).val.bits) selected.1
  · simpa [metadataWord,StoredCellBytes.input,StoredCellBytes.tuple] using slot_result (2 : Fin 5) x
  · exact coordinate_result src st out R activity selected m b z
  · exact EncodedCommunication.bitsValue_bits _

theorem metadataPair_result : metadataPair.result x=some (sumWord (st.metadata.decode m selected.1)) := by
  apply sum_lookup
  · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 2
  · exact metadataLabel_result src st out R activity selected m b z

theorem columnFamily_result : columnFamily.result x=
    some (sumWord ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv) selected.2)) := by
  apply sum_lookup
  · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 4
  · exact columnLabel_result src st out R activity selected m b z

end Input
end
end CurrentAdditive.StoredCellQueries

#print axioms CurrentAdditive.StoredCellQueries.finalPair_result
#print axioms CurrentAdditive.StoredCellQueries.metadataPair_result
#print axioms CurrentAdditive.StoredCellQueries.columnFamily_result
