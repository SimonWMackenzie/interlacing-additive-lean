import CurrentAdditive.V42ActualSource
import CurrentAdditive.V42PermittedExtraction
import CurrentAdditive.V42RuntimeDyadic
import CurrentAdditive.V40DeterministicFrontClock

namespace CurrentAdditive.V42ETHPhysical
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open PhysicalProducer V40StoredOutputPrimitives V39FramedNumerical V42ActualSource
open V39RuntimeETHNumerics V40DeterministicSourcePack
set_option maxHeartbeats 300000
set_option maxRecDepth 65536

variable (D:DinurReduction) (B:BOTReduction (booleanOccurrence D))

def classifier (E:Estimator) : Producer where
  machine:=E.machine
  result:=E.run
  coefficient:=E.clockCoefficient
  degree:=E.clockDegree
  outputs:=V39FramedNumerical.machine_outputs E

def tail (E:Estimator) := compose V42DeterministicRequest.request (classifier E)

theorem tail_result (E:Estimator) (Φ:ValidFormula) (K:ℕ) :
    (tail E).result (envelope D B Φ K)=E.run (request D B Φ K) := by
  have h:=V42DeterministicRequest.request_result (4*selected D B Φ) K
    (V42RuntimeWords.context (t10Graph D B Φ) (t10Graph_valid D B Φ) (selected D B Φ)
      (selected_two D B Φ) (V39CurrentSourceJoin.source_geometry D B Φ).1
      (V42GraphRuntime.selected_width B.degreeBound (k0 D B) (t10Graph D B Φ)
        (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B))) (run D B Φ K)
  rw [V42DeterministicRequest.generated_threshold] at h
  exact congrArg E.run h

def mainMachine (E:Estimator) := V42GraphRuntime.pipeline (k0 D B) (tail E).machine
def mainExponent (E:Estimator) := V42GraphRuntime.dyadicExponent B.degreeBound (k0 D B)
  (tail E).machine (tail E).coefficient (tail E).degree
def amplification := V42GraphRuntime.amplification (k0 D B)
def N (Φ:ValidFormula) := V42RuntimePrefix.N (k0 D B) (t10Graph D B Φ)
def mainTime (E:Estimator) (Φ:ValidFormula) (K:ℕ) := (N D B Φ)^(mainExponent D B E*(amplification D B)^K)

theorem mainExponent_ge (E:Estimator) : 1040 ≤ mainExponent D B E := by
  exact Nat.le_add_left 1040 _

#print axioms mainExponent_ge

theorem main_outputs (E:Estimator) (Φ:ValidFormula) (K:ℕ) :
    (mainMachine D B E).OutputsWithin (V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ)) K)
      (E.run (request D B Φ K)) (mainTime D B E Φ K) := by
  have ht:=(tail E).outputs (envelope D B Φ K)
  rw [tail_result] at ht
  exact (V42GraphRuntime.dyadic_outputs_with_tail B.degreeBound (k0 D B) (tail E).machine
    (tail E).coefficient (tail E).degree (t10Graph D B Φ) (t10Graph_valid D B Φ) K
    (k0_two D B) (V39CurrentSourceJoin.source_geometry D B Φ).1
    (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B) _ ht).1

#print axioms main_outputs

/-- The graph compiler and actual round counter feed the new constructor's
literal graph,zero,K input. Original variable counts determine K only. -/
def growingPackAt (amp:ℕ) := bank3 (graph D B) (UnaryProducer.constant 0).producer
  (growingRound amp)
def growingPack := growingPackAt D B (amplification D B)

theorem growing_result_at (amp:ℕ) (Φ:ValidFormula) (hN:1 ≤ Φ.val.variables) :
    (growingPackAt D B amp).result (EncodedCNF.encode Φ.val)=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ))
        (rounds amp Φ.val.variables) := by
  rw [growingPackAt,bank3_result,graph_result D B Φ hN]
  change BitMachineBankCodec.encode ![_,[],
    (V40DeterministicRounds.roundUnary amp).producer.result
      (originalVariables.result (EncodedCNF.encode Φ.val))]=_
  rw [original_result,(V40DeterministicRounds.roundUnary amp).result_eq,
    V40DeterministicRounds.round_value]
  simp only [List.length_replicate]
  rfl

theorem growing_result (Φ:ValidFormula) (hN:1 ≤ Φ.val.variables) :
    (growingPack D B).result (EncodedCNF.encode Φ.val)=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ))
        (rounds (amplification D B) Φ.val.variables) :=
  growing_result_at D B (amplification D B) Φ hN

def front (cs cutoff:ℕ) (hcut:1 ≤ cutoff) :=
  compose (sparseRoute cs cutoff hcut) (growingPack D B)

theorem front_result (cs cutoff:ℕ) (hcut:1 ≤ cutoff) (w:List Bool) :
    (front D B cs cutoff hcut).result w=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B (sparseFormula cs cutoff hcut w)))
        (rounds (amplification D B) (sparseFormula cs cutoff hcut w).val.variables) := by
  change (growingPack D B).result (AEth4.route3Out (cs+2) cutoff w)=_
  rw [AEth4.route3Out_eq]
  exact growing_result D B (sparseFormula cs cutoff hcut w)
    (hcut.trans (AEth4.routed4_variables (cs+2) cutoff w))

def machine (E:Estimator) (cs cutoff:ℕ) (hcut:1 ≤ cutoff) :=
  BitMachineComposition.composition (front D B cs cutoff hcut).machine (mainMachine D B E)
def time (E:Estimator) (cs cutoff:ℕ) (hcut:1 ≤ cutoff) (w:List Bool) :=
  let Φ:=sparseFormula cs cutoff hcut w
  V40DeterministicETHEndpoint.frontClock (front D B cs cutoff hcut) w+
    mainTime D B E Φ (rounds (amplification D B) Φ.val.variables)

theorem outputs (E:Estimator) (cs cutoff:ℕ) (hcut:1 ≤ cutoff) (w:List Bool) :
    (machine D B E cs cutoff hcut).OutputsWithin w
      (E.run (request D B (sparseFormula cs cutoff hcut w)
        (rounds (amplification D B) (sparseFormula cs cutoff hcut w).val.variables)))
      (time D B E cs cutoff hcut w) := by
  let Φ:=sparseFormula cs cutoff hcut w
  have hf:=(front D B cs cutoff hcut).outputs w
  rw [front_result] at hf
  have hm:=main_outputs D B E Φ (rounds (amplification D B) Φ.val.variables)
  have hr:=BitMachineComposition.composition_outputsWithin _ _ hf hm
  apply BitMachine.outputsWithin_mono _ hr
  change _ ≤ V40DeterministicETHEndpoint.frontClock (front D B cs cutoff hcut) w+
    mainTime D B E Φ (rounds (amplification D B) Φ.val.variables)
  unfold V40DeterministicETHEndpoint.frontClock
  rw [front_result]

#print axioms main_outputs
#print axioms outputs
end
end CurrentAdditive.V42ETHPhysical





