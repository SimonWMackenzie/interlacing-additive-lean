import CurrentAdditive.GaussFinalPacketPreparation
import CurrentAdditive.GaussPostloopEndpoint
import CurrentAdditive.GaussPostloopDecision

namespace CurrentAdditive.GaussMatrixPostloopMachines
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 16384
open EthInapproximability.CurrentPaper
open GaussCellPolynomialClock GaussFirstFreeCandidate GaussCertificateVectorABI

def relationMachine : BitMachine.Machine:=BitMachineComposition.composition
  GaussFinalPacketPreparation.machine GaussPostloopMachine.machine
def decisionMachine : BitMachine.Machine:=BitMachineComposition.composition
  GaussFinalPacketPreparation.machine GaussPostloopDecision.machine
def relationCoefficient:=Classical.choose GaussPostloopEndpoint.uniform_outputs
def relationExponent:=Classical.choose (Classical.choose_spec GaussPostloopEndpoint.uniform_outputs)
def decisionCoefficient:=Classical.choose GaussPostloopDecision.uniform_outputs
def decisionExponent:=Classical.choose (Classical.choose_spec GaussPostloopDecision.uniform_outputs)
def relationClock (n : Nat) : Nat:=GaussFinalPacketPreparation.clock n+
  2*GaussFinalPacketPreparation.packetCap n+2+
  relationCoefficient*(GaussFinalPacketPreparation.packetCap n+1)^relationExponent
def decisionClock (n : Nat) : Nat:=GaussFinalPacketPreparation.clock n+
  2*GaussFinalPacketPreparation.packetCap n+2+
  decisionCoefficient*(GaussFinalPacketPreparation.packetCap n+1)^decisionExponent

theorem packet_exact {m k : Nat} (B : Fin m → Fin k → ℚ) :
    BitMachineBankCodec.encode (GaussFinalPacketPreparation.words B)=
      GaussPostloopSerialized.packet (GaussControlTrace.statePacket (GaussControlTrace.after B k)) k := by
  apply congrArg BitMachineBankCodec.encode
  funext j
  fin_cases j <;> rfl

theorem cast_zero_one {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) : ∀i j,(A i j : ℚ)=0 ∨ (A i j : ℚ)=1 := by
  intro i j
  rcases h01 i j with h | h <;> simp [h]

/-- On a dependent original zero-one matrix the fixed composed program
computes its whole Gauss trace, counts its own width, and writes the exact
first-free relation in the original column order. -/
theorem relation_outputs {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (fun i j => (A i j : ℚ)) k).pivots≠none) :
    let B:=fun i j => (A i j : ℚ)
    let s:=GaussControlTrace.after B k
    ∃f : Fin k,∃hf : f.val ≤ m,
      SequentialTotality.typedFree s.pivots=some f ∧
      postloopPacket s.B s.pivots=some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) ∧
      relationMachine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
        (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
        (relationClock (GaussPhysical.encodeTypedMatrix B).length) := by
  let B:=fun i j => (A i j : ℚ)
  let s:=GaussControlTrace.after B k
  obtain ⟨f,hf,hfree,hcert,hout⟩:=Classical.choose_spec
    (Classical.choose_spec GaussPostloopEndpoint.uniform_outputs) A h01 hdependent
  have hprepare:=GaussFinalPacketPreparation.outputs B (cast_zero_one A h01) hm
  have hp:=GaussFinalPacketPreparation.packet_length B (cast_zero_one A h01) hm
  rw [←packet_exact B] at hout
  have hfull:=BitMachineComposition.composition_outputsWithin
    GaussFinalPacketPreparation.machine GaussPostloopMachine.machine hprepare hout
  refine ⟨f,hf,hfree,hcert,BitMachine.outputsWithin_mono relationMachine hfull ?_⟩
  change GaussFinalPacketPreparation.clock (GaussPhysical.encodeTypedMatrix B).length+
    2*(BitMachineBankCodec.encode (GaussFinalPacketPreparation.words B)).length+2+
    relationCoefficient*((BitMachineBankCodec.encode (GaussFinalPacketPreparation.words B)).length+1)^relationExponent≤
    relationClock (GaussPhysical.encodeTypedMatrix B).length
  unfold relationClock
  gcongr

/-- The fixed independence test also computes the full trace from the
original matrix. Its literal output bit determines the physical branch. -/
theorem decision_outputs {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m) :
    let B:=fun i j => (A i j : ℚ)
    let s:=GaussControlTrace.after B k
    let f:=GaussPivotPrefixPhysical.prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
    decisionMachine.OutputsWithin (GaussPhysical.encodeTypedMatrix B) [decide (f < k)]
      (decisionClock (GaussPhysical.encodeTypedMatrix B).length) ∧
      (SequentialTotality.typedFree s.pivots=none ↔ ¬f < k) := by
  let B:=fun i j => (A i j : ℚ)
  let s:=GaussControlTrace.after B k
  obtain ⟨hout,hnone⟩:=Classical.choose_spec
    (Classical.choose_spec GaussPostloopDecision.uniform_outputs) A h01
  have hprepare:=GaussFinalPacketPreparation.outputs B (cast_zero_one A h01) hm
  have hp:=GaussFinalPacketPreparation.packet_length B (cast_zero_one A h01) hm
  rw [←packet_exact B] at hout
  have hfull:=BitMachineComposition.composition_outputsWithin
    GaussFinalPacketPreparation.machine GaussPostloopDecision.machine hprepare hout
  refine ⟨BitMachine.outputsWithin_mono decisionMachine hfull ?_,hnone⟩
  change GaussFinalPacketPreparation.clock (GaussPhysical.encodeTypedMatrix B).length+
    2*(BitMachineBankCodec.encode (GaussFinalPacketPreparation.words B)).length+2+
    decisionCoefficient*((BitMachineBankCodec.encode (GaussFinalPacketPreparation.words B)).length+1)^decisionExponent≤
    decisionClock (GaussPhysical.encodeTypedMatrix B).length
  unfold decisionClock
  gcongr

theorem relation_polynomial : PolynomialBound (fun _ n => relationClock n) :=
  add (add (add GaussFinalPacketPreparation.clock_polynomial
    (mul (constant 2) GaussFinalPacketPreparation.packet_polynomial)) (constant 2))
    (mul (constant _) (power (add GaussFinalPacketPreparation.packet_polynomial (constant 1)) _))
theorem decision_polynomial : PolynomialBound (fun _ n => decisionClock n) :=
  add (add (add GaussFinalPacketPreparation.clock_polynomial
    (mul (constant 2) GaussFinalPacketPreparation.packet_polynomial)) (constant 2))
    (mul (constant _) (power (add GaussFinalPacketPreparation.packet_polynomial (constant 1)) _))

#print axioms relation_outputs
#print axioms decision_outputs
#print axioms relation_polynomial
#print axioms decision_polynomial
end
end CurrentAdditive.GaussMatrixPostloopMachines
