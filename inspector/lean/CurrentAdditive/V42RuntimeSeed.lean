import CurrentAdditive.V42RuntimePacket
import CurrentAdditive.V40ConstructorSeedAssembly

/-! Seed construction for the new ABI. The logarithm 4*k is read from
the actual scalar compiler output, and the context remains an opaque word. -/
namespace CurrentAdditive.V42RuntimeSeed
open EthInapproximability.CurrentPaper V39GeneratedConstruction
open V42RuntimePacket D22PacketWordExpression D22PostSearchCompiler
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def seedInput (k K : ℕ) (law activity : List Bool) := BitMachineBankCodec.encode
  ![V42RuntimePacket.envelope k K law activity,List.replicate (4*k) true]
def expression := D22StepContextAssembly.seedExpr
def inputMachine := (expression.producer 1 2 3).machine

theorem context_result (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) :
    (D22StepContextAssembly.contextExpr.producer 1 2 3).result
      (withSource graph n m k K law activity)=V42RuntimePacket.context k law activity := by
  simp only [D22StepContextAssembly.contextExpr,join_result,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project,
    withSource,BankFieldProjection.result_encode]
  simp [withSourceWords,V42RuntimePacket.context,BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

theorem envelope_result (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) :
    (D22StepContextAssembly.envelopeExpr.producer 1 2 3).result
      (withSource graph n m k K law activity)=V42RuntimePacket.envelope k K law activity := by
  simp only [D22StepContextAssembly.envelopeExpr,join_result,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project]
  rw [context_result]
  simp only [withSource,BankFieldProjection.result_encode]
  simp [withSourceWords,V42RuntimePacket.envelope,BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

theorem result (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) :
    (expression.producer 1 2 3).result (withSource graph n m k K law activity)=seedInput k K law activity := by
  simp only [expression,D22StepContextAssembly.seedExpr,join_result,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    WExpr.producer,D22PacketPrimitives.frame,D22PacketPrimitives.project]
  rw [envelope_result]
  simp only [withSource,BankFieldProjection.result_encode]
  simp [withSourceWords,seedInput,BitMachineBankCodec.encode_eq_list,List.ofFn_succ]

theorem input_outputs (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) :
    inputMachine.OutputsWithin (withSource graph n m k K law activity) (seedInput k K law activity)
      (expression.timeCoefficient*(2^(4*k)+(withSource graph n m k K law activity).length+1)^expression.timeDegree) := by
  have h := expression.outputs_polynomial (1 : Fin 14) 2 3 (withSource graph n m k K law activity) n m (4*k)
    (by simp [withSource,withSourceWords]) (by simp [withSource,withSourceWords])
    (by simp [withSource,withSourceWords])
  simpa only [inputMachine,D22PacketWordExpression.measure,result] using h

def machine := BitMachineComposition.composition inputMachine V40WeightedSeed.machine
def coefficient := V40ConstructorComposition.coefficient
  expression.timeCoefficient expression.timeDegree V40ConstructorSeedAssembly.seedCoefficient
  V40ConstructorSeedAssembly.seedDegree inputMachine.pushBound 1
def degree := V40ConstructorComposition.degree expression.timeDegree V40ConstructorSeedAssembly.seedDegree

theorem outputs (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) (hk : 2≤k) :
    machine.OutputsWithin (withSource graph n m k K law activity)
      (V40StoredEnvelope.input (4*k) K (V42RuntimePacket.context k law activity) (storedLookupSeed (4*k)))
      (coefficient*(2^(4*k)+(withSource graph n m k K law activity).length+1)^degree) := by
  have ha := input_outputs graph n m k K law activity
  have hs := V40ConstructorSeedAssembly.seed_outputs (V42RuntimePacket.envelope k K law activity)
    (4*k) (by omega)
  simp only [V40WeightedSeed.packet_eq] at hs
  change V40WeightedSeed.machine.OutputsWithin (seedInput k K law activity)
    (V40StoredEnvelope.input (4*k) K (V42RuntimePacket.context k law activity) (storedLookupSeed (4*k)))
    (V40ConstructorSeedAssembly.seedCoefficient*
      ((V42RuntimePacket.envelope k K law activity).length+2^(4*k)+1)^V40ConstructorSeedAssembly.seedDegree) at hs
  have hctx : (V42RuntimePacket.envelope k K law activity).length≤(seedInput k K law activity).length := by
    simp [seedInput,BitMachineBankCodec.encode_length,Fin.sum_univ_succ] <;> omega
  have hs' := BitMachine.outputsWithin_mono V40WeightedSeed.machine hs
    (Nat.mul_le_mul_left V40ConstructorSeedAssembly.seedCoefficient (Nat.pow_le_pow_left
      (show (V42RuntimePacket.envelope k K law activity).length+2^(4*k)+1≤
        2^(4*k)+(seedInput k K law activity).length+1 by omega) V40ConstructorSeedAssembly.seedDegree))
  have h := BitMachineComposition.composition_outputsWithin inputMachine V40WeightedSeed.machine ha hs'
  have hm := BitMachine.output_length_bound inputMachine ha
  apply BitMachine.outputsWithin_mono _ h
  exact V40ConstructorComposition.time_bound
    (2^(4*k)+(withSource graph n m k K law activity).length)
    expression.timeCoefficient expression.timeDegree V40ConstructorSeedAssembly.seedCoefficient
    V40ConstructorSeedAssembly.seedDegree inputMachine.pushBound 1 (2^(4*k))
    (seedInput k K law activity).length (by omega)
    (hm.trans (Nat.add_le_add_right (Nat.le_add_left _ _) _))

def roundMachine := BitMachineComposition.composition machine V40ConstructorRoundPacket.packet.machine
def roundCoefficient := V40ConstructorComposition.coefficient coefficient degree
  V40ConstructorRoundPacket.packet.coefficient V40ConstructorRoundPacket.packet.degree machine.pushBound 0
def roundDegree := V40ConstructorComposition.degree degree V40ConstructorRoundPacket.packet.degree

theorem round_outputs (graph : List Bool) (n m k K : ℕ) (law activity : List Bool) (hk : 2≤k) :
    roundMachine.OutputsWithin (withSource graph n m k K law activity)
      (WeightedIterationDriver.input
        (V40StoredEnvelope.input (4*k) K (V42RuntimePacket.context k law activity) (storedLookupSeed (4*k))) K)
      (roundCoefficient*(2^(4*k)+(withSource graph n m k K law activity).length+1)^roundDegree) := by
  have hs := outputs graph n m k K law activity hk
  have hp := V40ConstructorRoundPacket.outputs (4*k) K (V42RuntimePacket.context k law activity)
    (storedLookupSeed (4*k))
  have h := BitMachineComposition.composition_outputsWithin machine V40ConstructorRoundPacket.packet.machine hs hp
  have hm := BitMachine.output_length_bound machine hs
  apply BitMachine.outputsWithin_mono _ h
  simpa only [Nat.zero_add] using V40ConstructorComposition.time_bound
    (2^(4*k)+(withSource graph n m k K law activity).length)
    coefficient degree V40ConstructorRoundPacket.packet.coefficient V40ConstructorRoundPacket.packet.degree
    machine.pushBound 0 0
    (V40StoredEnvelope.input (4*k) K (V42RuntimePacket.context k law activity) (storedLookupSeed (4*k))).length
    (by omega) (hm.trans (Nat.add_le_add_right (Nat.le_add_left _ _) _))

#print axioms outputs
#print axioms round_outputs
end
end CurrentAdditive.V42RuntimeSeed
