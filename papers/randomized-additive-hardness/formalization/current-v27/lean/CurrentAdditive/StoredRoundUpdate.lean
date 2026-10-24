import CurrentAdditive.StoredRoundData
import CurrentAdditive.DynamicGetterOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundUpdate
open EthInapproximability.CurrentPaper PhysicalProducer V40LawJobsClock StoredRoundData
noncomputable section

def previous := PhysicalProducer.compose (projection (0 : Fin 2)) (projection (0 : Fin 2))
def newRecord := pair
  (PhysicalProducer.compose (projection (0 : Fin 2)) (projection (1 : Fin 2)))
  (projection (1 : Fin 2))
def implementation (i : Fin 7) := DynamicGetterOrdinary.bankFields
  (List.ofFn (fun j : Fin 8 => if j.val=i.val+1 then newRecord else
    PhysicalProducer.compose previous (projection j)))

def phaseOutput (a : Data) (i : Fin 7) := V40LawPacket.packet
  (V40LawPacket.packet (state a i.val) (V40ActualSevenRequests.output a.parameters i))
  (StoredSourcePhase.output (call a i))

theorem generic_result (i : Fin 7) (x : List Bool) : (implementation i).result x=
    BitMachineBankCodec.encode (fun j : Fin 8 => if j.val=i.val+1 then newRecord.result x else
      BankFieldProjection.result j (previous.result x)) := by
  simp only [implementation,DynamicGetterOrdinary.bankFields_result,
    BitMachineBankCodec.encode_eq_list,List.flatMap_def,List.map_ofFn,Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext j
  by_cases h : j.val=i.val+1 <;> simp [h,PhysicalProducer.compose,projection]

theorem state_update (a : Data) (i : Fin 7) :
    BitMachineBankCodec.encode (fun j : Fin 8 => if j.val=i.val+1 then record a i else
      BankFieldProjection.result j (state a i.val))=state a (i.val+1) := by
  unfold state
  simp only [BankFieldProjection.result_encode]
  congr 1
  funext j
  by_cases hz : j.val=0
  · have hn : ¬j.val=i.val+1 := by omega
    simp [hz,hn]
  · have hp : 0<j.val := by omega
    by_cases hu : j.val=i.val+1
    · simp [hu,hp]
    · by_cases hj : j.val ≤ i.val
      · have hk : j.val ≤ i.val+1 := by omega
        simp [hz,hp,hu,hj,hk]
      · have hk : ¬j.val ≤ i.val+1 := by omega
        simp [hz,hp,hu,hj,hk]

theorem result (a : Data) (i : Fin 7) :
    (implementation i).result (phaseOutput a i)=state a (i.val+1) := by
  rw [generic_result]
  have hp : previous.result (phaseOutput a i)=state a i.val := by
    simp [previous,phaseOutput,PhysicalProducer.compose,projection,packet_eq]
  have hr : newRecord.result (phaseOutput a i)=record a i := by
    simp [newRecord,phaseOutput,record,PhysicalProducer.compose,projection,packet_eq]
  simp only [hp,hr]
  exact state_update a i

theorem realizes (i : Fin 7) : Realizes (implementation i).machine
    (fun a : Data=>phaseOutput a i) (fun a=>state a (i.val+1)) := by
  have h := producer (implementation i) (fun a : Data=>phaseOutput a i)
  simpa only [result] using h

end
end CurrentAdditive.StoredRoundUpdate

#print axioms CurrentAdditive.StoredRoundUpdate.realizes
