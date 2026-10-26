import CurrentAdditive.StoredCellColumnFacts

namespace CurrentAdditive.StoredTemplateRequest
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery StoredCellQueries
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

def selectedPair (col : src.Column) (bin : Fin s) : Fin q₂ × Fin src.gamma.size :=
  match col with
  | .inl pair => src.outer.decode pair.1 bin
  | .inr pair => pair

theorem outerWord_result (a : Fin src.outer.size × Fin src.gamma.size)
    (hc : selected.2=.inl a) : ordinaryOuterWord.result x=
      some (StoredCellBytes.tuple (fun p => (finProdFinEquiv (src.outer.decode a.1 p)).val)) := by
  have hp := (column_inl_result src st out R activity selected m b z a hc).2
  apply lookup_ofFn (source 2) (field (0 : Fin 2) columnPair) x a.1.val.bits
    (fun j => StoredCellBytes.tuple (fun p => (finProdFinEquiv (src.outer.decode j p)).val)) a.1
  · simpa [StoredCellBytes.sources,StoredCellBytes.outerWords,StoredCellBytes.words]
      using source_result src st out R activity selected m b z 2
  · exact field_packet (0 : Fin 2) columnPair x _ hp
  · exact EncodedCommunication.bitsValue_bits _

theorem templateColumnPair_result (bin : Fin s)
    (hm : st.metadata.decode m selected.1=.inl bin) :
    templateColumnPair.result x=some (BitMachineBankCodec.encode
      ![(selectedPair src selected.2 bin).1.val.bits,(selectedPair src selected.2 bin).2.val.bits]) := by
  have hmidx := (metadata_inl_result src st out R activity selected m b z bin hm).2
  cases hc : selected.2 with
  | inl a =>
    obtain ⟨htag,hpair⟩ := column_inl_result src st out R activity selected m b z a hc
    apply branch_result columnTag chosenOuterPair columnPair x _ false htag
    change chosenOuterPair.result x=some _
    have hlabel : chosenOuterLabel.result x=
        some (finProdFinEquiv (src.outer.decode a.1 bin)).val.bits := by
      apply lookup_ofFn ordinaryOuterWord metadataIndex x bin.val.bits
        (fun p => (finProdFinEquiv (src.outer.decode a.1 p)).val.bits) bin
      · exact outerWord_result src st out R activity selected m b z a hc
      · exact hmidx
      · exact EncodedCommunication.bitsValue_bits _
    have hp := product_lookup (companion 1) chosenOuterLabel x (src.outer.decode a.1 bin)
      (by simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 1)
      hlabel
    simpa [selectedPair,hc] using hp
  | inr a =>
    obtain ⟨htag,hpair⟩ := column_inr_result src st out R activity selected m b z a hc
    apply branch_result columnTag chosenOuterPair columnPair x _ true htag
    simpa [selectedPair,hc] using hpair

theorem templateWord_result : templateWord.result x=
    some (StoredCellBytes.tuple (fun p =>
      (finProdFinEquiv (src.inner.decode (st.selector.decode z selected.1) p)).val)) := by
  have hselector : (lookup selectorWord coordinate).result x=
      some (st.selector.decode z selected.1).val.bits := by
    apply lookup_ofFn selectorWord coordinate x selected.1.val.bits
      (fun p => (st.selector.decode z p).val.bits) selected.1
    · simpa [selectorWord,StoredCellBytes.input,StoredCellBytes.tuple] using slot_result (4 : Fin 5) x
    · exact coordinate_result src st out R activity selected m b z
    · exact EncodedCommunication.bitsValue_bits _
  apply lookup_ofFn (source 1) (lookup selectorWord coordinate) x
    (st.selector.decode z selected.1).val.bits
    (fun j => StoredCellBytes.tuple (fun p => (finProdFinEquiv (src.inner.decode j p)).val))
    (st.selector.decode z selected.1)
  · simpa [StoredCellBytes.sources,StoredCellBytes.innerWords,StoredCellBytes.words]
      using source_result src st out R activity selected m b z 1
  · exact hselector
  · exact EncodedCommunication.bitsValue_bits _

theorem request_result (bin : Fin s)
    (hm : st.metadata.decode m selected.1=.inl bin) :
    templateRequest.result x=some (BitMachineBankCodec.encode
      ![(src.inner.decode (st.selector.decode z selected.1) (selectedPair src selected.2 bin).1).2.val.bits,
        (Paper2.SourceMatrix.head (src.gamma.decode (selectedPair src selected.2 bin).2)
          (src.inner.decode (st.selector.decode z selected.1) (selectedPair src selected.2 bin).1).1).val.bits]) := by
  let a := selectedPair src selected.2 bin
  let iz := src.inner.decode (st.selector.decode z selected.1) a.1
  have hpair := templateColumnPair_result src st out R activity selected m b z bin hm
  have hlabel : templateInnerLabel.result x=some (finProdFinEquiv iz).val.bits := by
    apply lookup_ofFn templateWord (field (0 : Fin 2) templateColumnPair) x a.1.val.bits
      (fun p => (finProdFinEquiv (src.inner.decode (st.selector.decode z selected.1) p)).val.bits) a.1
    · exact templateWord_result src st out R activity selected m b z
    · exact field_packet (0 : Fin 2) templateColumnPair x _ hpair
    · exact EncodedCommunication.bitsValue_bits _
  have hinner : templateInnerPair.result x=some (BitMachineBankCodec.encode ![iz.1.val.bits,iz.2.val.bits]) := by
    apply product_lookup (companion 0) templateInnerLabel x iz
    · simpa [StoredCellBytes.companions] using companion_result src st out R activity selected m b z 0
    · exact hlabel
  have hgamma : templateGammaWord.result x=some (StoredCellBytes.tuple
      (fun p => (src.gamma.decode a.2 p).val)) := by
    apply lookup_ofFn (source 0) (field (1 : Fin 2) templateColumnPair) x a.2.val.bits
      (fun j => StoredCellBytes.tuple (fun p => (src.gamma.decode j p).val)) a.2
    · simpa [StoredCellBytes.sources,StoredCellBytes.gammaWords,StoredCellBytes.words]
        using source_result src st out R activity selected m b z 0
    · exact field_packet (1 : Fin 2) templateColumnPair x _ hpair
    · exact EncodedCommunication.bitsValue_bits _
  apply pair_result (field (1 : Fin 2) templateInnerPair)
    (lookup templateGammaWord (field (0 : Fin 2) templateInnerPair)) x
  · exact field_packet (1 : Fin 2) templateInnerPair x _ hinner
  · apply lookup_ofFn templateGammaWord (field (0 : Fin 2) templateInnerPair) x iz.1.val.bits
      (fun p : Fin (q₁+s+1) => (src.gamma.decode a.2 p).val.bits)
      ⟨iz.1.val,by have:=iz.1.isLt;omega⟩
    · exact hgamma
    · exact field_packet (0 : Fin 2) templateInnerPair x _ hinner
    · exact EncodedCommunication.bitsValue_bits _

end
end CurrentAdditive.StoredTemplateRequest

#print axioms CurrentAdditive.StoredTemplateRequest.request_result
