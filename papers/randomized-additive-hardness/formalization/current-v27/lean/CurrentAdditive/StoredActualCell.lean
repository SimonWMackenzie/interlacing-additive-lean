import CurrentAdditive.StoredTemplateRequest
import CurrentAdditive.StoredSourceRequest
import CurrentAdditive.StoredCellRead

/-! A single fixed physical current-cell evaluator. Both current column
families, both metadata arms, the real diagonal test, public activity lookup,
and the final raw Boolean-table read are executed. No requested base cell or
desired Boolean answer is supplied to the endpoint. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.StoredActualCell
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery StoredCellQueries
noncomputable section

def request := branch metadataTag templateRequest StoredSourceQueries.request
def query := compose (retain request) StoredCellRead.query
def machine := query.machine
def coefficient := query.coefficient
def degree := query.degree

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

def predecessor : Fin nx × Fin ny := SourceMatrix.baseRequest activity
  (src.decodeRow (SourceData.Streams.decode src st (m,(b,z)) selected.1))
  (src.decodeColumn selected.2)

theorem request_result : request.result x=some (BitMachineBankCodec.encode
    ![(predecessor src st activity selected m b z).1.val.bits,
      (predecessor src st activity selected m b z).2.val.bits]) := by
  cases hm : st.metadata.decode m selected.1 with
  | inl bin =>
    apply branch_result metadataTag templateRequest StoredSourceQueries.request x _ false
      (metadata_inl_result src st out R activity selected m b z bin hm).1
    have h := StoredTemplateRequest.request_result src st out R activity selected m b z bin hm
    cases hc : selected.2 <;>
      simpa [predecessor,SourceData.Streams.decode,hm,SourceData.decodeRow,SourceData.decodeColumn,
        SourceMatrix.baseRequest,SourceMatrix.head,StoredTemplateRequest.selectedPair,hc] using h
  | inr i =>
    apply branch_result metadataTag templateRequest StoredSourceQueries.request x _ true
      (metadata_inr_result src st out R activity selected m b z i hm).1
    simpa [predecessor,SourceData.Streams.decode,hm,SourceData.decodeRow,SourceMatrix.baseRequest]
      using StoredSourceQueries.request_result src st out R activity selected m b z i hm

theorem result : query.result x=some [src.B R activity
    (SourceData.Streams.decode src st (m,(b,z)) selected.1) selected.2] := by
  have hrequest := request_result src st out R activity selected m b z
  have hret : (retain request).result x=some (BitMachineBankCodec.encode
      ![x,BitMachineBankCodec.encode ![(predecessor src st activity selected m b z).1.val.bits,
        (predecessor src st activity selected m b z).2.val.bits]]) := by
    simp only [retain,hrequest,Option.map_some]
  have hstate : oldState.result x=some (StoredCellBytes.baseState (μX := μX) (μY := μY) R) :=
    field_packet (1 : Fin 4) context x _ (context_result src st out R activity selected m b z)
  have hread := StoredCellRead.result μX μY R x
    (predecessor src st activity selected m b z).1 (predecessor src st activity selected m b z).2 hstate
  exact compose_result (retain request) StoredCellRead.query x _ _ hret hread

attribute [local irreducible] query

/-- The polynomial constants belong to one fixed finite program, before all
source lists, matrices, law weights, activity tables, and selected indices. -/
theorem outputs : machine.OutputsWithin x [src.B R activity
    (SourceData.Streams.decode src st (m,(b,z)) selected.1) selected.2]
    (coefficient*((x).length+1)^degree) := query.outputs x _ (result src st out R activity selected m b z)

end Input
end
end CurrentAdditive.StoredActualCell

#print axioms CurrentAdditive.StoredActualCell.outputs
