import CurrentAdditive.GaussPivotFieldsAppend
import CurrentAdditive.GaussCellSpec
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-!
Fixed physical serializers for the two packet boundaries of a Gauss step.
The cell serializer consumes a prepared twelve-word bank and writes the
literal arithmetic request packet. The state serializer consumes the four
prepared state words and writes the complete Bank4 state packet. Neither
theorem assumes serialization is free or claims that the words were prepared.
-/

namespace CurrentAdditive.GaussPacketSerialize

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussControlTrace

theorem physical_cell_packet (flag : Bool)
    (current column row pivot : CurrentAdditive.CodeDCodec.RawRat)
    (source output : List Bool) :
    ∃ (t : Nat) (S' : BitMachineBankSerialize.Bank 12),
      t ≤ 2 * (CurrentAdditive.GaussPhysical.cellPacket
        flag current column row pivot).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (CurrentAdditive.GaussPhysical.cellBank
            flag current column row pivot) source [] output) =
        BitMachineBankSerialize.cfg none none S' source []
          (CurrentAdditive.GaussPhysical.cellPacket
            flag current column row pivot ++ output) := by
  simpa only [CurrentAdditive.GaussPhysical.cellPacket,
    BitMachineBankCodec.encode_eq_list,
    BitMachineBankSerialize.encode] using
    BitMachineBankSerialize.serialize
      (CurrentAdditive.GaussPhysical.cellBank
        flag current column row pivot) source output

theorem physical_pivot_pair {m k : Nat} (p : Fin m × Fin k)
    (source output : List Bool) :
    ∃ (t : Nat) (S' : BitMachineBankSerialize.Bank 2),
      t ≤ 2 * (pivotPacket p).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (fun j : Fin 2 => if j = 0 then List.replicate p.1.val true
            else List.replicate p.2.val true) source [] output) =
        BitMachineBankSerialize.cfg none none S' source []
          (pivotPacket p ++ output) := by
  simpa only [pivotPacket, BitMachineBankCodec.encode_eq_list,
    BitMachineBankSerialize.encode] using
    BitMachineBankSerialize.serialize
      (fun j : Fin 2 => if j = 0 then List.replicate p.1.val true
        else List.replicate p.2.val true) source output

/-- The length field and pair bytes that the pivot-list append controller
expects are written by the inherited fixed framing machine. -/
theorem physical_pivot_payload {m k : Nat} (p : Fin m × Fin k) :
    (SourceListMachineWriter.framingMachine true).OutputsWithin
      (pivotPacket p) (CurrentAdditive.GaussPivotFieldsAppend.payload p)
      ((UnaryBinaryEncoding.coefficient + 7) *
        ((pivotPacket p).length + 1)^2) := by
  simpa [CurrentAdditive.GaussPivotFieldsAppend.payload,
    SourceListMachineWriter.result] using
    SourceListMachineWriter.outputs true (pivotPacket p)

theorem physical_state_packet {m k : Nat} (s : State m k)
    (source output : List Bool) :
    ∃ (t : Nat) (S' : BitMachineBankSerialize.Bank 4),
      t ≤ 2 * (statePacket s).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (stateBank s) source [] output) =
        BitMachineBankSerialize.cfg none none S' source []
          (statePacket s ++ output) := by
  simpa only [statePacket, BitMachineBankCodec.encode_eq_list,
    BitMachineBankSerialize.encode] using
    BitMachineBankSerialize.serialize (stateBank s) source output

#print axioms physical_cell_packet
#print axioms physical_pivot_pair
#print axioms physical_pivot_payload
#print axioms physical_state_packet

end CurrentAdditive.GaussPacketSerialize
