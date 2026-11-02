import CurrentAdditive.StoredWeightedState

namespace CurrentAdditive.StoredWeightedState

open Paper2
open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction

def encodeNumbered (R : NumberedMatrix) : List Bool :=
  BitMachineBankCodec.encode ![MatrixMaterialization.rowMajor R.entry,lawBytes R.rowLaw,lawBytes R.colLaw]

theorem encode_numbered (R : StoredMatrix) : encode R=encodeNumbered R.numbered := rfl

theorem encode_ofNumbered (R : NumberedMatrix) :
    encode (StoredMatrix.ofNumbered R)=encodeNumbered R := by
  rw [encode_numbered,StoredMatrix.ofNumbered_numbered]

namespace SourceData

variable {D q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : V39GeneratedConstruction.SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList D Q (Fin w × src.Column) (product (uniform w) src.columnLaw))

def baseRequest (activity : Fin ni → Fin q₂ → Option (Fin s))
    (r : Fin out.size) (c : Fin (Q*(st.metadata.size*(st.base.size*st.selector.size)))) :
    Fin nx × Fin ny :=
  let col := (V39GeneratedConstruction.SourceData.successorColumnOrder src st).symm c
  let selected := out.decode r col.1
  Paper2.SourceMatrix.baseRequest activity
    (src.decodeRow (V39GeneratedConstruction.SourceData.Streams.decode src st col.2 selected.1))
    (src.decodeColumn selected.2)

theorem numbered_entry_request (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (r : Fin out.size) (c : Fin (Q*(st.metadata.size*(st.base.size*st.selector.size)))) :
    src.numberedEntry st out R activity r c=
      R (baseRequest src st out activity r c).1 (baseRequest src st out activity r c).2 := rfl

theorem stored_successor_bytes (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    encode (StoredMatrix.ofNumbered (src.numbered st out R activity))=
      BitMachineBankCodec.encode ![MatrixMaterialization.rowMajor (src.numberedEntry st out R activity),
        lawBytes out.law,
        lawBytes (reindex (V39GeneratedConstruction.SourceData.successorColumnOrder src st)
          (product (uniform Q) (V39GeneratedConstruction.SourceData.Streams.law src st)))] := by
  rw [encode_ofNumbered]
  rfl

end SourceData
end CurrentAdditive.StoredWeightedState

#print axioms CurrentAdditive.StoredWeightedState.encode_ofNumbered
#print axioms CurrentAdditive.StoredWeightedState.SourceData.stored_successor_bytes
