import CurrentAdditive.V40WeightedSeedData
import CurrentAdditive.V40LawBankClock

/-! Full physical seed constructor. The first field is opaque retained context;
the second is the unary level actually selected by the outer search. -/
namespace CurrentAdditive.V40WeightedSeed
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper

def packet (context word : List Bool) := V40LawPacket.packet context word
theorem packet_eq (context word : List Bool) : packet context word=
    BitMachineBankCodec.encode ![context,word] := by
  unfold packet V40LawPacket.packet
  congr 1
  funext i
  fin_cases i <;> rfl
def machine := V40LawBankMap.liftMachine V40WeightedSeedData.machine
def clock (context : List Bool) (L : Nat) :=
  7*((packet context (List.replicate L true)).length+2)+
    (1+4*V40WeightedSeedData.machine.pushBound)*V40WeightedSeedData.clock L

theorem outputs (context : List Bool) (L : Nat) :
    machine.OutputsWithin (packet context (List.replicate L true))
      (packet context (StoredWeightedState.encode (V39GeneratedConstruction.storedLookupSeed L)))
      (clock context L) :=
  V40LawBankMap.outputs_charged V40WeightedSeedData.machine context
    (List.replicate L true) _ _ (V40WeightedSeedData.outputs L)

theorem output_context (context : List Bool) (L : Nat) :
    BitMachineBankCodec.decode 2
      (packet context (StoredWeightedState.encode (V39GeneratedConstruction.storedLookupSeed L)))=
      some ![context,StoredWeightedState.encode (V39GeneratedConstruction.storedLookupSeed L)] :=
  by
    rw [packet_eq]
    exact BitMachineBankCodec.decode_encode _

#print axioms outputs
end
end CurrentAdditive.V40WeightedSeed
