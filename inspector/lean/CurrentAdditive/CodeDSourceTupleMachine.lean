import CurrentAdditive.CylinderRawInputProjection

namespace CurrentAdditive.CodeDSourceTupleMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open EthInapproximability.CurrentPaper
open CylinderProductionProjection

def machine : BitMachine.Machine := CylinderProductionProjection.tupleMachine
def coefficient : Nat := CylinderRawInputProjection.itemCoefficient+100
def clock (n : Nat) : Nat := coefficient*(n+1)^3

/-- The tuple-only projection starts with the original weighted-source
packet. Indexed records, including equal labels, keep their stored order. -/
theorem outputs {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    machine.OutputsWithin (CodeDCanonicalSourceV2.encodedSource source)
      (SourceListEncoding.encode (tupleWords source))
      (clock (CodeDCanonicalSourceV2.encodedSource source).length) := by
  have hm := CylinderRawInputProjection.input_measure_le (sourceItems source)
  have hp := CylinderRawInputProjection.projection_clock_bound
    (CylinderProductionProjectionClock.inputMeasure (sourceItems source))
    (CodeDCanonicalSourceV2.encodedSource source).length hm
  exact BitMachine.outputsWithin_mono _ (project_source_tuple source)
    ((CylinderProductionProjectionClock.tupleClock_poly source).trans hp)

#print axioms outputs
end
end CurrentAdditive.CodeDSourceTupleMachine
