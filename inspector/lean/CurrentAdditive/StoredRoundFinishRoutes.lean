import CurrentAdditive.StoredRoundStages
import CurrentAdditive.StoredRoundPrepared
import CurrentAdditive.StoredWeightedNumbered

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundFinishRoutes
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open PhysicalProducer V40LawJobsClock StoredRoundData
noncomputable section

def phaseTuple (i : Fin 7) := PhysicalProducer.compose (StoredRoundRoutes.phase i) (projection (2 : Fin 3))
def sourcePacket := DynamicGetterOrdinary.bankFields (List.ofFn phaseTuple)
def builderComp (i : Fin 7) := PhysicalProducer.compose
  (PhysicalProducer.compose (StoredRoundRoutes.previous i) (projection (0 : Fin 2)))
  (projection (2 : Fin 3))
def columnTree := PhysicalProducer.compose (builderComp 6) (projection (0 : Fin 2))
def companionPacket := DynamicGetterOrdinary.bankFields
  [builderComp 1,builderComp 2,builderComp 3,
   PhysicalProducer.compose columnTree (projection (0 : Fin 3)),
   PhysicalProducer.compose columnTree (projection (2 : Fin 3)),
   PhysicalProducer.compose (builderComp 6) (projection (1 : Fin 2))]
def cellContext := DynamicGetterOrdinary.bankFields
  [StoredRoundRoutes.context,StoredRoundRoutes.old,sourcePacket,companionPacket]
def prepared := pair cellContext (phaseTuple 6)
def routeCells := pair identity prepared

def columnData (a : Data) := V40ActualSevenRequests.successorData a.parameters
def columnRequest := DynamicGetterOrdinary.bankFields
  [StoredRoundRoutes.publicField 4,StoredRoundRoutes.phaseLaw 3,
   StoredRoundRoutes.phaseLaw 4,StoredRoundRoutes.phaseLaw 5]

theorem phaseTuple_result (a : Data) (i : Fin 7) :
    (phaseTuple i).result (state a 7)=StoredSourcePhase.tupleBytes (call a i) := by
  simp only [phaseTuple,StoredRoundRoutes.phase,PhysicalProducer.compose,Function.comp_apply,
    projection,StoredRoundRoutes.previous_result a i 7 i.isLt,StoredRoundProjection.record_tuples]

theorem sourcePacket_result (a : Data) :
    sourcePacket.result (state a 7)=StoredRoundProjection.sourcePacket a := by
  simp only [sourcePacket,DynamicGetterOrdinary.bankFields_result,List.flatMap_def,
    List.map_ofFn,Function.comp_def,phaseTuple_result]
  simp [StoredRoundProjection.sourcePacket,BitMachineBankCodec.encode_eq_list,
    List.ofFn_succ,List.ofFn_zero]

theorem builderComp_result (a : Data) (i : Fin 7) :
    (builderComp i).result (state a 7)=StoredRoundProjection.builderComp a i := by
  simp [builderComp,PhysicalProducer.compose,projection,
    StoredRoundRoutes.previous_result a i 7 i.isLt,record,StoredRoundProjection.builderComp]

theorem columnTree_result (a : Data) :
    columnTree.result (state a 7)=StoredRoundProjection.columnTree a := by
  simp [columnTree,PhysicalProducer.compose,projection,builderComp_result,
    StoredRoundProjection.columnTree]

theorem companionPacket_result (a : Data) :
    companionPacket.result (state a 7)=StoredRoundProjection.companionPacket a := by
  simp [companionPacket,DynamicGetterOrdinary.bankFields_result,PhysicalProducer.compose,
    projection,builderComp_result,columnTree_result,StoredRoundProjection.companionPacket,
    BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.ofFn_zero]

theorem prepared_result (a : Data) :
    prepared.result (state a 7)=StoredActualCells.input (src a) (streams a) (final a)
      a.parameters.R.entry a.activity := by
  have h : prepared.result (state a 7)=StoredRoundProjection.prepared a := by
    simp [prepared,cellContext,DynamicGetterOrdinary.bankFields_result,
      StoredRoundRoutes.context_result,StoredRoundRoutes.old_result,sourcePacket_result,
      companionPacket_result,phaseTuple_result,StoredRoundProjection.prepared,
      BitMachineBankCodec.encode_eq_list,List.ofFn_succ,List.ofFn_zero]
  exact h.trans (StoredRoundProjection.prepared_eq a)

theorem columnRequest_result (a : Data) :
    columnRequest.result (state a 7)=V40SuccessorColumnLaw.input (columnData a) := by
  simp [columnRequest,DynamicGetterOrdinary.bankFields_result,StoredRoundRoutes.public_result,
    StoredRoundRoutes.phaseLaw_result,StoredRoundData.call,StoredRoundData.metadata,
    StoredRoundData.base,StoredRoundData.selector,StoredSourcePhase.lawBytes,
    StoredSourcePhase.source,columnData,V40ActualSevenRequests.successorData,
    V40SuccessorColumnLaw.input,src,streams,BitMachineBankCodec.encode_eq_list,
    List.ofFn_succ,List.ofFn_zero]
  rfl

end
end CurrentAdditive.StoredRoundFinishRoutes

#print axioms CurrentAdditive.StoredRoundFinishRoutes.prepared_result
#print axioms CurrentAdditive.StoredRoundFinishRoutes.columnRequest_result
