import CurrentV43.Parametric.Source
import CurrentV43.TimeTradeoff.SourceBounds

/-! A literal source-to-deterministic-constructor front for every paid gap
schedule of v43 `thm:time-tradeoff`. The gap program may have superpolynomial
unary output in N; its computation and serialization are charged explicitly. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V40StoredOutputPrimitives
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- Composition with literal field framing preserves a variable clock. -/
def frameVariable (A : PhysicalConcat.Producer) : PhysicalConcat.Producer where
  machine:=BitMachineComposition.composition A.machine PhysicalProducer.field.machine
  result:=fun w=>EncodedCommunication.field (A.result w)
  clock:=fun w=>A.clock w+2*(A.result w).length+2+4*((A.result w).length+1)
  outputs w:=by
    exact BitMachineComposition.composition_outputsWithin _ _ (A.outputs w)
      (by simpa only [PhysicalProducer.field,pow_one] using PhysicalProducer.field.outputs (A.result w))

def concatVariable (A B : PhysicalConcat.Producer) : PhysicalConcat.Producer where
  machine:=PhysicalConcat.machine (A:=A) (B:=B)
  result:=fun w=>A.result w++B.result w
  clock:=PhysicalConcat.clock (A:=A) (B:=B)
  outputs:=PhysicalConcat.outputs (A:=A) (B:=B)

variable (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))

/-- The source graph and zero floor are printed by fixed polynomial machines. -/
def deterministicHead : PhysicalProducer.Producer :=
  PhysicalProducer.concat
    (PhysicalProducer.compose (V40DeterministicSourcePack.graph Src Bsrc) PhysicalProducer.field)
    (PhysicalProducer.compose (UnaryProducer.constant 0).producer PhysicalProducer.field)

/-- One fixed finite front prints graph,zero,K, with K computed by the actual
schedule program. It has no access to SAT correctness or an estimator. -/
def deterministicFront (G : CurrentV43.ParametricSource.Schedule) : PhysicalConcat.Producer :=
  concatVariable (PhysicalProducer.localProducer (deterministicHead Src Bsrc))
    (frameVariable G.producer)

theorem deterministicFront_result (G : CurrentV43.ParametricSource.Schedule)
    (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (deterministicFront Src Bsrc G).result (EncodedCNF.encode Φ.val)=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph Src Bsrc Φ)) (G.gap Φ.val.variables) := by
  change (deterministicHead Src Bsrc).result (EncodedCNF.encode Φ.val)++
    EncodedCommunication.field (G.producer.result (EncodedCNF.encode Φ.val))=_
  simp only [deterministicHead,PhysicalProducer.concat,PhysicalProducer.compose,
    PhysicalProducer.field,Function.comp_apply,UnaryProducer.constant,
    V40DeterministicSourcePack.graph_result Src Bsrc Φ hN,G.correct Φ]
  simp [V42RuntimePrefix.input,V40GraphConstructorFront.input,BitMachineBankCodec.encode_eq_list,List.append_assoc]

theorem deterministicFront_outputs (G : CurrentV43.ParametricSource.Schedule)
    (Φ : ValidFormula) (hN : 1 ≤ Φ.val.variables) :
    (deterministicFront Src Bsrc G).machine.OutputsWithin (EncodedCNF.encode Φ.val)
      (V42RuntimePrefix.input (EncodedGraph.encode (t10Graph Src Bsrc Φ)) (G.gap Φ.val.variables))
      ((deterministicFront Src Bsrc G).clock (EncodedCNF.encode Φ.val)) := by
  rw [←deterministicFront_result Src Bsrc G Φ hN]
  exact (deterministicFront Src Bsrc G).outputs _

/-- A polynomial in the input length, actual unary gap and actual paid gap
clock pays every graph, framing, copying and concatenation transition. -/
theorem deterministicFront_clock (G : CurrentV43.ParametricSource.Schedule) (w : List Bool) :
    (deterministicFront Src Bsrc G).clock w ≤
      (30+(1+2*(deterministicHead Src Bsrc).machine.pushBound)*
        (deterministicHead Src Bsrc).coefficient)*
      (w.length+(G.producer.result w).length+G.producer.clock w+1)^
        ((deterministicHead Src Bsrc).degree+1) := by
  let H:=deterministicHead Src Bsrc
  let X:=w.length+(G.producer.result w).length+G.producer.clock w+1
  let P:=X^(H.degree+1)
  have hX:1 ≤ X:=by dsimp [X];omega
  have hx:w.length ≤ X:=by dsimp [X];omega
  have hk:(G.producer.result w).length ≤ X:=by dsimp [X];omega
  have ht:G.producer.clock w ≤ X:=by dsimp [X];omega
  have hXP:X ≤ P:=by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ H.degree+1 by omega)
  have hhead:H.coefficient*(w.length+1)^H.degree ≤ H.coefficient*P:=by
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by dsimp [X];omega) H.degree).trans
      (Nat.pow_le_pow_right hX (by omega))
  have hlen:(H.result w).length ≤ H.machine.pushBound*(H.coefficient*P)+X:=by
    have h:=BitMachine.output_length_bound H.machine (H.outputs w)
    exact h.trans (by nlinarith)
  have hfield:(EncodedCommunication.field (G.producer.result w)).length ≤ 2*X:=by
    rw [EncodedCommunication.field_length]
    dsimp [X]
    omega
  have hframe:G.producer.clock w+2*(G.producer.result w).length+2+
      4*((G.producer.result w).length+1) ≤ 6*X:=by dsimp [X];omega
  change 2*w.length+2+1+H.coefficient*(w.length+1)^H.degree+1+
    (G.producer.clock w+2*(G.producer.result w).length+2+4*((G.producer.result w).length+1))+
    2*(EncodedCommunication.field (G.producer.result w)).length+2+2*(H.result w).length+2+1 ≤ _
  change _ ≤ (30+(1+2*H.machine.pushBound)*H.coefficient)*P
  nlinarith

#print axioms deterministicFront_outputs
#print axioms deterministicFront_clock
end
end CurrentV43.TimeTradeoff


