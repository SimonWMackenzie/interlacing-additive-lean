import CurrentAdditive.StoredMatrixPhysicalStep

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredMatrixEnvelopeStep
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open PhysicalProducer V40LawJobsClock
noncomputable section

def envelope (a : StoredRoundData.Data) (L K : Nat) := BitMachineBankCodec.encode
  ![List.replicate L true,List.replicate K true,
    StoredStepContext.context a.parameters.q₁ a.parameters.w a.parameters.Q a.parameters.μI a.activity]
def input (a : StoredRoundData.Data) (L K : Nat) := BitMachineBankCodec.encode
  ![envelope a L K,StoredWeightedState.encode a.parameters.R]
def output (a : StoredRoundData.Data) (L K : Nat) := BitMachineBankCodec.encode
  ![envelope a L K,StoredWeightedState.encode (StoredMatrixPhysicalStep.next a)]

def saved := projection (0 : Fin 2)
def coreInput := pair
  (PhysicalProducer.compose saved (projection (2 : Fin 3))) (projection (1 : Fin 2))
def prepare := pair saved coreInput
def finish := pair (projection (0 : Fin 2))
  (PhysicalProducer.compose (projection (1 : Fin 2)) (projection (1 : Fin 2)))
def first := BitMachineComposition.composition prepare.machine
  (V40LawBankMap.liftMachine StoredMatrixPhysicalStep.machine)
def machine := BitMachineComposition.composition first finish.machine

structure Data where
  round : StoredRoundData.Data
  L : Nat
  K : Nat

def w0 (d : Data) := V40LawPacket.packet (envelope d.round d.L d.K) (StoredRoundData.input d.round)
def w1 (d : Data) := V40LawPacket.packet (envelope d.round d.L d.K) (StoredMatrixPhysicalStep.output d.round)

theorem prepare_result (d : Data) : prepare.result (input d.round d.L d.K)=w0 d := by
  simp [prepare,saved,coreInput,input,envelope,w0,StoredRoundData.input,StoredStepContext.packet,
    PhysicalProducer.compose,projection,packet_eq]

theorem finish_result (d : Data) : finish.result (w1 d)=output d.round d.L d.K := by
  simp [finish,w1,output,StoredMatrixPhysicalStep.output,StoredStepContext.packet,
    PhysicalProducer.compose,projection,packet_eq]

theorem realizes : Realizes machine (fun d : Data=>input d.round d.L d.K)
    (fun d=>output d.round d.L d.K) := by
  have h0 := producer prepare (fun d : Data=>input d.round d.L d.K)
  simp only [prepare_result] at h0
  have hc : Realizes StoredMatrixPhysicalStep.machine
      (fun d : Data=>StoredRoundData.input d.round) (fun d=>StoredMatrixPhysicalStep.output d.round) := by
    obtain ⟨C,E,h⟩ := StoredMatrixPhysicalStep.realizes
    exact ⟨C,E,fun d=>h d.round⟩
  have h1 := bank_map _ (fun d : Data=>envelope d.round d.L d.K) _ _ hc
  have h2 := producer finish w1
  simp only [finish_result] at h2
  exact V40LawJobsClock.compose _ _ _ _ _
    (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2

def coefficient := Classical.choose realizes
def degree := Classical.choose (Classical.choose_spec realizes)
theorem outputs (a : StoredRoundData.Data) (L K : Nat) :
    machine.OutputsWithin (input a L K) (output a L K)
      (coefficient*((input a L K).length+1)^degree) :=
  Classical.choose_spec (Classical.choose_spec realizes) ⟨a,L,K⟩

end
end CurrentAdditive.StoredMatrixEnvelopeStep

#print axioms CurrentAdditive.StoredMatrixEnvelopeStep.outputs
