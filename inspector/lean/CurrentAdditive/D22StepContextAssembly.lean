import CurrentAdditive.D22PostSearchCompiler

/-! The source writer supplies the actual law/activity fields in Bank14.
This adapter frames exactly the agreed seven-field context and preserves
selected L,K in an outer envelope that the seed and rounds retain verbatim. -/
namespace D22StepContextAssembly
open EthInapproximability.CurrentPaper
open CurrentAdditive D22PacketPrimitives D22PacketWordExpression D22PostSearchPacket
open D22PostSearchCompiler
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def contextExpr : WExpr 14 := join
  [.frame (.proj 5),.frame (.proj 6),.frame (.proj 7),.frame (.proj 8),.frame (.proj 9),
    .frame (.proj 12),.frame (.proj 13)]
def envelopeExpr : WExpr 14 := join [.frame (.proj 3),.frame (.proj 4),.frame contextExpr]
def seedExpr : WExpr 14 := join [.frame envelopeExpr,.frame (.proj 3)]
def seedInput (L K : ℕ) (law activity : List Bool) := BitMachineBankCodec.encode
  ![envelope L K law activity,List.replicate L true]

noncomputable def contextMachine : BitMachine.Machine := (contextExpr.producer 1 2 3).machine
noncomputable def envelopeMachine : BitMachine.Machine := (envelopeExpr.producer 1 2 3).machine
noncomputable def seedInputMachine : BitMachine.Machine := (seedExpr.producer 1 2 3).machine

theorem context_result (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    (contextExpr.producer 1 2 3).result (withSource graph n m L K law activity)=stepContext L law activity := by
  simp only [contextExpr,join_result,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project,
    withSource,BankFieldProjection.result_encode]
  simp [withSourceWords,stepContext,BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

theorem envelope_result (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    (envelopeExpr.producer 1 2 3).result (withSource graph n m L K law activity)=envelope L K law activity := by
  simp only [envelopeExpr,join_result,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project]
  rw [context_result]
  simp only [withSource,BankFieldProjection.result_encode]
  simp [withSourceWords,envelope,BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

theorem seed_result (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    (seedExpr.producer 1 2 3).result (withSource graph n m L K law activity)=seedInput L K law activity := by
  simp only [seedExpr,join_result,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project]
  rw [envelope_result]
  simp only [withSource,BankFieldProjection.result_encode]
  simp [withSourceWords,seedInput,BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

theorem context_outputs (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    contextMachine.OutputsWithin (withSource graph n m L K law activity) (stepContext L law activity)
      (contextExpr.timeCoefficient*(2^L+(withSource graph n m L K law activity).length+1)^contextExpr.timeDegree) := by
  have h := contextExpr.outputs_polynomial (1 : Fin 14) 2 3 (withSource graph n m L K law activity) n m L
    (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords])
  simpa only [contextMachine,D22PacketWordExpression.measure,context_result] using h

theorem envelope_outputs (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    envelopeMachine.OutputsWithin (withSource graph n m L K law activity) (envelope L K law activity)
      (envelopeExpr.timeCoefficient*(2^L+(withSource graph n m L K law activity).length+1)^envelopeExpr.timeDegree) := by
  have h := envelopeExpr.outputs_polynomial (1 : Fin 14) 2 3 (withSource graph n m L K law activity) n m L
    (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords])
  simpa only [envelopeMachine,D22PacketWordExpression.measure,envelope_result] using h

theorem seed_input_outputs (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    seedInputMachine.OutputsWithin (withSource graph n m L K law activity) (seedInput L K law activity)
      (seedExpr.timeCoefficient*(2^L+(withSource graph n m L K law activity).length+1)^seedExpr.timeDegree) := by
  have h := seedExpr.outputs_polynomial (1 : Fin 14) 2 3 (withSource graph n m L K law activity) n m L
    (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords])
  simpa only [seedInputMachine,D22PacketWordExpression.measure,seed_result] using h

theorem seed_input_length (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :
    (seedInput L K law activity).length ≤ seedExpr.sizeCoefficient*
      (2^L+(withSource graph n m L K law activity).length+1)^seedExpr.sizeDegree := by
  have h := (seedExpr.bounds (1 : Fin 14) 2 3 (withSource graph n m L K law activity) n m L
    (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords])).1
  simpa only [D22PacketWordExpression.measure,seed_result] using h

theorem envelope_L (L K : ℕ) (law activity : List Bool) :
    BankFieldProjection.result (0 : Fin 3) (envelope L K law activity)=List.replicate L true := by simp [envelope]
theorem envelope_K (L K : ℕ) (law activity : List Bool) :
    BankFieldProjection.result (1 : Fin 3) (envelope L K law activity)=List.replicate K true := by simp [envelope]
theorem envelope_context (L K : ℕ) (law activity : List Bool) :
    BankFieldProjection.result (2 : Fin 3) (envelope L K law activity)=stepContext L law activity := by simp [envelope]

#print axioms seed_input_outputs
#print axioms envelope_L
#print axioms envelope_K
end
end D22StepContextAssembly
