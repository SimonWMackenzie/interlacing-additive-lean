import CurrentAdditive.GenericFeatureGeneratedIteration
import CurrentAdditive.OrdinaryIterationPacket

/-! The literal two-field feature-iteration packet for each fixed D.
The already physical ordinary iteration loader parses the initial state and
unary q, then runs the coordinate program. All local execution and length
premises are discharged by the generated-iteration supplier. -/
namespace CurrentAdditive.GenericFeatureIterationPacket
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
open EthInapproximability.CurrentPaper

abbrev M (D : Nat) := GenericFeatureCoordinateTransition.machine D

def machine (D : Nat) : BitMachine.Machine := OrdinaryIterationPacket.machine (M D)

def words (D q : Nat) (ys : List Nat) (raw : List Bool) : Fin 2 → List Bool :=
  ![GenericFeatureGeneratedIteration.states D ys raw 0,List.replicate q true]

def clock (D q : Nat) (ys : List Nat) (raw : List Bool) :=
  5*((BitMachineBankCodec.encode (words D q ys raw)).length+1)+
    GenericFeatureGeneratedIteration.clock D q ys raw+1

theorem clock_eq (D q : Nat) (ys : List Nat) (raw : List Bool) :
    clock D q ys raw=
      5*((BitMachineBankCodec.encode (words D q ys raw)).length+1)+
        q*BitMachineIteration.roundBound (M D)
          (GenericFeatureGeneratedIteration.lengthBound D q ys raw)
          (GenericFeatureGeneratedIteration.timeBound D q ys raw)+2 := by
  simp only [clock,GenericFeatureGeneratedIteration.clock,Nat.add_assoc]

/-- D fixes the physical program before q, alphabet and source bytes.
The endpoint requires only its literal initial packet; it assumes no
decoded bank, per-coordinate execution, time bound or length bound. -/
theorem outputs (D q : Nat) (ys : List Nat) (raw : List Bool) :
    (machine D).OutputsWithin (BitMachineBankCodec.encode (words D q ys raw))
      (GenericFeatureGeneratedIteration.states D ys raw q) (clock D q ys raw) := by
  have hstep (j : Nat) (hj : j<(List.replicate q true).length) :
      (M D).OutputsWithin (GenericFeatureGeneratedIteration.states D ys raw j)
        (GenericFeatureGeneratedIteration.states D ys raw (j+1))
        (GenericFeatureGeneratedIteration.timeBound D q ys raw) :=
    BitMachine.outputsWithin_mono (M D)
      (GenericFeatureGeneratedIteration.step_outputs D j ys raw)
      (GenericFeatureGeneratedIteration.step_time_le D q j ys raw (by simpa using hj))
  have hlen (j : Nat) (hj : j<(List.replicate q true).length) :
      (GenericFeatureGeneratedIteration.states D ys raw j).length ≤
        GenericFeatureGeneratedIteration.lengthBound D q ys raw :=
    GenericFeatureGeneratedIteration.state_length_le D q j ys raw (by simpa using hj)
  have h:=OrdinaryIterationPacket.outputsWithin (M D)
    (GenericFeatureGeneratedIteration.states D ys raw) (List.replicate q true)
    (GenericFeatureGeneratedIteration.lengthBound D q ys raw)
    (GenericFeatureGeneratedIteration.timeBound D q ys raw) hstep hlen
  simpa only [machine,words,clock,List.length_replicate,
    GenericFeatureGeneratedIteration.clock,Nat.add_assoc] using h

theorem outputs_zero (D : Nat) (ys : List Nat) (raw : List Bool) :
    (machine D).OutputsWithin (BitMachineBankCodec.encode (words D 0 ys raw))
      (GenericFeatureGeneratedIteration.states D ys raw 0) (clock D 0 ys raw) :=
  outputs D 0 ys raw

#print axioms clock_eq
#print axioms outputs
#print axioms outputs_zero
end
end CurrentAdditive.GenericFeatureIterationPacket
