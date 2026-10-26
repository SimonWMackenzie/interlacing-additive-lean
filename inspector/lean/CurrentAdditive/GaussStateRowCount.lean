import CurrentAdditive.GaussRowCount
import CurrentAdditive.GaussControlTrace
import CurrentAdditive.GaussTypedGetterBridge
import EthInapproximability.CurrentPaper.BankFieldProjection

/-! The row-count producer started from the actual four-field Gauss state. -/

namespace CurrentAdditive.GaussStateRowCount

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussControlTrace

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BankFieldProjection.machine (0 : Fin 4)) GaussRowCount.machine

theorem matrix_field {m k : Nat} (s : State m k) :
    BankFieldProjection.result (0 : Fin 4) (statePacket s) =
      CurrentAdditive.GaussPhysical.encodeTypedMatrix s.B := by
  simp [statePacket, BankFieldProjection.result_encode, stateBank]

theorem outputs {m k : Nat} (s : State m k) :
    machine.OutputsWithin (statePacket s) (List.replicate m true)
      (12 * ((statePacket s).length + 1) +
       2 * (CurrentAdditive.GaussPhysical.encodeTypedMatrix s.B).length + 2 +
       (SourceListMachineOuter.canonicalBound GaussRowCount.oneMachine
         (GaussTypedGetterBridge.rowWords s.B)
         GaussRowCount.oneResult GaussRowCount.oneClock +
        2 * (EncodedCommunication.natField m ++ List.replicate m true).length + 2 +
        (2 * (EncodedCommunication.natField m ++ List.replicate m true).length + 3))) := by
  have hp := BankFieldProjection.outputs (0 : Fin 4) (statePacket s)
  rw [matrix_field] at hp
  have hm := GaussTypedGetterBridge.encodeTypedMatrix_eq s.B
  have hr := GaussRowCount.outputs (GaussTypedGetterBridge.rowWords s.B)
  rw [← hm] at hr
  have hlen : (GaussTypedGetterBridge.rowWords s.B).length = m := by
    simp [GaussTypedGetterBridge.rowWords]
  rw [hlen] at hr
  exact BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (0 : Fin 4)) GaussRowCount.machine hp hr

noncomputable def polynomialClock (N : Nat) : Nat :=
  14 * (N + 1) + GaussRowCount.polynomialClock N

theorem outputs_polynomial {m k : Nat} (s : State m k) :
    machine.OutputsWithin (statePacket s) (List.replicate m true)
      (polynomialClock (statePacket s).length) := by
  have hp := BankFieldProjection.outputs (0 : Fin 4) (statePacket s)
  rw [matrix_field] at hp
  have hm := GaussTypedGetterBridge.encodeTypedMatrix_eq s.B
  have hr := GaussRowCount.outputs_polynomial (GaussTypedGetterBridge.rowWords s.B)
  rw [← hm] at hr
  have hlen : (GaussTypedGetterBridge.rowWords s.B).length = m := by
    simp [GaussTypedGetterBridge.rowWords]
  rw [hlen] at hr
  have hcomp := BitMachineComposition.composition_outputsWithin
    (BankFieldProjection.machine (0 : Fin 4)) GaussRowCount.machine hp hr
  have hfield := BitMachineBankCodec.word_length_le_encode (stateBank s) (0 : Fin 4)
  have hmatrix : (CurrentAdditive.GaussPhysical.encodeTypedMatrix s.B).length ≤
      (statePacket s).length := by
    simpa [stateBank, statePacket] using hfield
  have hclock := GaussRowCount.polynomialClock_mono hmatrix
  apply BitMachine.outputsWithin_mono _ hcomp
  unfold polynomialClock
  omega

#print axioms outputs
#print axioms outputs_polynomial

end CurrentAdditive.GaussStateRowCount
