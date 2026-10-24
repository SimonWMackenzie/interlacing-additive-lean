import CurrentAdditive.GaussInitialMachine
import CurrentAdditive.GaussControlTrace

namespace CurrentAdditive.GaussInitialPacket

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

/-- The fixed initializer writes the exact four-field initial Gauss state. -/
theorem initial_state_output {m k : Nat} (A : Fin m → Fin k → ℚ) :
    GaussInitialMachine.machine.OutputsWithin (GaussPhysical.encodeTypedMatrix A)
      (GaussControlTrace.statePacket (GaussControlTrace.initial A))
      (3*(GaussPhysical.encodeTypedMatrix A).length+8) := by
  convert GaussInitialMachine.output (GaussPhysical.encodeTypedMatrix A) using 1
  simp [GaussControlTrace.statePacket, GaussControlTrace.stateBank,
    GaussControlTrace.initial, GaussControlTrace.pivotsPacket,
    BitMachineBankCodec.encode, BitMachineBankCodec.encodeFrom,
    SourceListEncoding.encode, SourceListEncoding.fields, natField,
    GaussInitialMachine.suffix, field]

#print axioms initial_state_output

end CurrentAdditive.GaussInitialPacket
