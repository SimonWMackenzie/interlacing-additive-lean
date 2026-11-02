import CurrentAdditive.GaussLoopInputPreparation

namespace CurrentAdditive.GaussWholeMatrixMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper
open GaussCellPolynomialClock
open CurrentAdditive.MinimumRatioContext

def machine : BitMachine.Machine:=BitMachineComposition.composition
  GaussLoopInputPreparation.machine GaussIterationPacketMachine.machine
def clock (n : Nat) : Nat:=GaussLoopInputPreparation.clock n+
  2*GaussLoopInputPreparation.packetCap n+2+
  (5*(GaussLoopInputPreparation.packetCap n+1)+GaussWholeIteration.clock n+1)

/-- The single serialized matrix input supplies every matrix operand, actual
dimension, cursor, pivot choice and fuel value. The fixed machine returns
the exact complete Gauss state, with every matrix column retained. -/
theorem outputs {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m) :
    machine.OutputsWithin (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ)))
      (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) k))
      (clock (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length) := by
  have hprepare:=GaussLoopInputPreparation.outputs (fun i j => (A i j : ℚ)) hm
  have hloop:=GaussIterationPacketMachine.outputs A h01 hm
  have hrun:=BitMachineComposition.composition_outputsWithin
    GaussLoopInputPreparation.machine GaussIterationPacketMachine.machine hprepare hloop
  have hp:=GaussLoopInputPreparation.packet_length (fun i j => (A i j : ℚ)) hm
  apply BitMachine.outputsWithin_mono machine hrun
  unfold clock
  omega

theorem preparation_polynomial : PolynomialBound (fun _ n => GaussLoopInputPreparation.clock n) := by
  have hcols : PolynomialBound (fun _ n => GaussMatrixDimensions64.columnsClock n) := by
    unfold GaussMatrixDimensions64.columnsClock GaussRowCount.polynomialClock GaussRowCount.itemEnvelope
    repeat first | exact constant _ | exact second | apply add | apply mul | apply power
  have hi:=uniform_invocation GaussLoopInputPreparation.I second
    (add (mul (constant 3) second) (constant 8))
  have hc:=uniform_invocation GaussLoopInputPreparation.C second hcols
  have hp : PolynomialBound (fun _ n => GaussLoopInputPreparation.packetCap n):=
    add (mul (constant 8) second) (constant 30)
  exact add (add (add hi hc) (mul (constant 2) hp)) (constant 4)

theorem clock_polynomial : PolynomialBound (fun _ n => clock n) := by
  have hp : PolynomialBound (fun _ n => GaussLoopInputPreparation.packetCap n):=
    add (mul (constant 8) second) (constant 30)
  exact add (add (add preparation_polynomial (mul (constant 2) hp)) (constant 2))
    (add (add (mul (constant 5) (add hp (constant 1))) GaussWholeIteration.clock_polynomial) (constant 1))

/-- Fixed coefficient and exponent precede every zero-one matrix and both
dimensions. The clock depends only on that matrix's original input bytes. -/
theorem uniform_outputs : ∃C e : Nat,∀{m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ),
    (∀i j,A i j=0 ∨ A i j=1) → 0 < m →
    machine.OutputsWithin (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ)))
      (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) k))
      (C*((GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length+1)^e) := by
  obtain ⟨C,e,hclock⟩:=clock_polynomial
  refine ⟨C,e,?_⟩
  intro m k A h01 hm
  exact BitMachine.outputsWithin_mono machine (outputs A h01 hm)
    (by simpa only [Nat.zero_add] using hclock 0 (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length)

#print axioms outputs
#print axioms clock_polynomial
#print axioms uniform_outputs
end
end CurrentAdditive.GaussWholeMatrixMachine
