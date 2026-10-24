import CurrentAdditive.CodeDInnerFuelPreparation
import CurrentAdditive.OrdinaryIterationPacket

namespace CurrentAdditive.CodeDInnerMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 65536
open EthInapproximability.CurrentPaper GaussCellPolynomialClock
abbrev M := CodeDRawPass.machine
def machine := BitMachineComposition.composition CodeDInnerFuelPreparation.machine (OrdinaryIterationPacket.machine M)
def current {q : Nat} (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) (t : Nat) :=
  (CodeDCompressionIteration.onePass (CodeDRawPass.features q alphabet).size (CodeDRawPass.phi q alphabet))^[t] source
def packetLength (n k : Nat) := 2*(n+k)+2
def clock (n k L : Nat) :=
  CodeDInnerFuelPreparation.coefficient*(n+1)^CodeDInnerFuelPreparation.exponent+
  2*packetLength n k+2+5*(packetLength n k+1)+
  k*BitMachineIteration.roundBound M L (CodeDRawPass.coefficient*(L+1)^CodeDRawPass.exponent)+2

theorem packet_length (x : List Bool) (k : Nat) :
    (BitMachineBankCodec.encode ![x,List.replicate k true]).length=packetLength x.length k := by
  simp [BitMachineBankCodec.encode_length,Fin.sum_univ_two,packetLength]

/-- The program derives its own fuel from the source's actual encoded
record count. Its displayed intermediate bound is a mathematical size bound,
not an execution or callback supplier. -/
theorem outputs (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hpositive : SequentialSourceCode.SourcePositive source) (L : Nat)
    (hbound : ∀ t ≤ source.size,(CylinderRawMatrixProducer.input alphabet (current alphabet source t)).length ≤ L) :
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet (current alphabet source source.size))
      (clock (CylinderRawMatrixProducer.input alphabet source).length source.size L) := by
  let states := fun t => CylinderRawMatrixProducer.input alphabet (current alphabet source t)
  let fuel := List.replicate source.size true
  let T:=CodeDRawPass.coefficient*(L+1)^CodeDRawPass.exponent
  have hpos (t : Nat) : SequentialSourceCode.SourcePositive (current alphabet source t) :=
    CodeDCompressionIteration.iterate_positive (CodeDRawPass.features q alphabet).size (CodeDRawPass.phi q alphabet)
      (SequentialSourceCode.generatedFeatures_pos q 8192 (alphabet.map Prod.fst))
      (SequentialSourceCode.generatedFeatures_constant q 8192 (alphabet.map Prod.fst)) source hpositive t
  have hstep : ∀ j < fuel.length,M.OutputsWithin (states j) (states (j+1)) T := by
    intro j hj
    have hj' : j ≤ source.size := by dsimp only [fuel] at hj; simp only [List.length_replicate] at hj; omega
    have h:=CodeDRawPass.outputs q alphabet (current alphabet source j) (hpos j)
    have ht : CodeDRawPass.coefficient*((states j).length+1)^CodeDRawPass.exponent≤T := by
      dsimp only [T,states]
      gcongr
      exact hbound j hj'
    have hn : current alphabet source (j+1)=
        CodeDCompressionIteration.onePass (CodeDRawPass.features q alphabet).size (CodeDRawPass.phi q alphabet)
          (current alphabet source j) := by simp only [current,Function.iterate_succ_apply']
    change M.OutputsWithin (states j) (CylinderRawMatrixProducer.input alphabet (current alphabet source (j+1))) T
    rw [hn]
    exact BitMachine.outputsWithin_mono M h ht
  have hlen : ∀ j < fuel.length,(states j).length ≤ L := by
    intro j hj
    exact hbound j (by dsimp only [fuel] at hj; simp only [List.length_replicate] at hj; omega)
  have hi:=OrdinaryIterationPacket.outputsWithin M states fuel L T hstep hlen
  have hp:=CodeDInnerFuelPreparation.outputs q alphabet source
  have h:=BitMachineComposition.composition_outputsWithin CodeDInnerFuelPreparation.machine
    (OrdinaryIterationPacket.machine M) hp hi
  simpa only [states,current,Function.iterate_zero,id_eq,List.length_replicate,packet_length,
    clock,fuel,T,machine,Nat.add_assoc] using h

theorem scalar_clock_polynomial : PolynomialBound (fun _ n => clock n n n) := by
  have hprep:=mul (constant CodeDInnerFuelPreparation.coefficient)
    (power (add second (constant 1)) CodeDInnerFuelPreparation.exponent)
  have hp:=add (mul (constant 2) (add second second)) (constant 2)
  have ht:=mul (constant CodeDRawPass.coefficient) (power (add second (constant 1)) CodeDRawPass.exponent)
  have hr:=add (add (add ht (mul (constant (M.stackCount+2))
    (add second (mul ht (constant M.pushBound))))) (constant M.stackCount)) (constant 4)
  simpa only [clock,packetLength,BitMachineIteration.roundBound] using
    add (add (add (add (add hprep (mul (constant 2) hp)) (constant 2))
      (mul (constant 5) (add hp (constant 1)))) (mul second hr)) (constant 2)
def coefficient := Classical.choose scalar_clock_polynomial
def exponent := Classical.choose (Classical.choose_spec scalar_clock_polynomial)

theorem outputs_bounded (q : Nat) (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ))
    (hpositive : SequentialSourceCode.SourcePositive source) (L : Nat)
    (hbound : ∀ t ≤ source.size,(CylinderRawMatrixProducer.input alphabet (current alphabet source t)).length ≤ L) :
    machine.OutputsWithin (CylinderRawMatrixProducer.input alphabet source)
      (CylinderRawMatrixProducer.input alphabet (current alphabet source source.size))
      (coefficient*(L+1)^exponent) := by
  have hn:=hbound 0 (Nat.zero_le _)
  change (CylinderRawMatrixProducer.input alphabet source).length ≤ L at hn
  have hk:source.size ≤ L:=(CodeDInnerFuelPreparation.source_size_le_input q alphabet source).trans hn
  apply BitMachine.outputsWithin_mono machine (outputs q alphabet source hpositive L hbound)
  apply Nat.le_trans (m:=clock L L L) ?_
    (by simpa only [Nat.zero_add] using
      (Classical.choose_spec (Classical.choose_spec scalar_clock_polynomial)) 0 L)
  unfold clock packetLength
  gcongr

#print axioms outputs
#print axioms scalar_clock_polynomial
#print axioms outputs_bounded
end
end CurrentAdditive.CodeDInnerMachine
