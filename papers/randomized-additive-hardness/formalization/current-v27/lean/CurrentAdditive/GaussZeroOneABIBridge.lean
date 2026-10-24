import CurrentAdditive.GaussZeroOneCoefficient
import CurrentAdditive.GaussCertificateVectorABI

/-! Literal zero/one writer outputs are exactly the canonical RawRat records
used by the vector packet ABI. -/

namespace CurrentAdditive.GaussZeroOneABIBridge

theorem zeroWord_eq :
    GaussZeroOneCoefficient.zeroWord =
      GaussCertificateVectorABI.coefficientPacket 0 := by
  have hraw : CurrentAdditive.GaussPhysical.rawOfRat 0 =
      ⟨false, [], [true]⟩ := by
    norm_num [CurrentAdditive.GaussPhysical.rawOfRat]
  simp [GaussCertificateVectorABI.coefficientPacket, hraw,
    GaussZeroOneCoefficient.zeroWord,
    CurrentAdditive.CodeDCodec.encodeRawRat,
    CurrentAdditive.CodeDCodec.rawRatBank,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encode,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encodeFrom,
    EthInapproximability.CurrentPaper.EncodedCommunication.field]

theorem oneWord_eq :
    GaussZeroOneCoefficient.oneWord =
      GaussCertificateVectorABI.coefficientPacket 1 := by
  have hraw : CurrentAdditive.GaussPhysical.rawOfRat 1 =
      ⟨false, [true], [true]⟩ := by
    norm_num [CurrentAdditive.GaussPhysical.rawOfRat]
  simp [GaussCertificateVectorABI.coefficientPacket, hraw,
    GaussZeroOneCoefficient.oneWord,
    CurrentAdditive.CodeDCodec.encodeRawRat,
    CurrentAdditive.CodeDCodec.rawRatBank,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encode,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encodeFrom,
    EthInapproximability.CurrentPaper.EncodedCommunication.field]

theorem outputs_bit (b : Bool) :
    GaussZeroOneCoefficient.machine.OutputsWithin [b]
      (GaussCertificateVectorABI.coefficientPacket
        (if b then 1 else 0)) 1 := by
  cases b with
  | false => simpa [zeroWord_eq, oneWord_eq] using
      GaussZeroOneCoefficient.outputs_bit false
  | true => simpa [zeroWord_eq, oneWord_eq] using
      GaussZeroOneCoefficient.outputs_bit true

#print axioms outputs_bit

end CurrentAdditive.GaussZeroOneABIBridge
