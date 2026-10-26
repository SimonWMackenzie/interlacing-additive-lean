import CurrentAdditive.GaussRequestProgram64
import CurrentAdditive.GaussCellSpec

namespace CurrentAdditive.GaussRequestTypedBridge64

open EthInapproximability.CurrentPaper

theorem packet_eq_cellPacket (flag : Bool)
    (current column row pivot : CurrentAdditive.CodeDCodec.RawRat) :
    GaussOperandSerialize64.packet flag
      (CurrentAdditive.CodeDCodec.encodeRawRat current)
      (CurrentAdditive.CodeDCodec.encodeRawRat column)
      (CurrentAdditive.CodeDCodec.encodeRawRat row)
      (CurrentAdditive.CodeDCodec.encodeRawRat pivot) =
    CurrentAdditive.GaussPhysical.cellPacket
      flag current column row pivot := by
  rw [CurrentAdditive.GaussPhysical.cellPacket,
    BitMachineBankCodec.encode_eq_list]
  rfl

#print axioms packet_eq_cellPacket

end CurrentAdditive.GaussRequestTypedBridge64
