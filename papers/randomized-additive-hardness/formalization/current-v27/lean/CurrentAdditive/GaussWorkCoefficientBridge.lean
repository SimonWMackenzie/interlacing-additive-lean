import CurrentAdditive.GaussActualWorkList
import CurrentAdditive.GaussCoefficientTotal

/-! The physically produced work items use exactly the admitted coefficient
program's canonical Bank3 input format. -/

namespace CurrentAdditive.GaussWorkCoefficientBridge

open EthInapproximability.CurrentPaper

theorem workPacket_eq {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) :
    GaussWorkItemContextSerialize.workPacket B f j =
      GaussCertificateWorkList.workPacket B f j := by
  rfl

theorem workPackets_eq {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f : Fin k) :
    GaussWorkListComplete.workPackets B f =
      GaussCertificateWorkList.workPackets B f := by
  simp [GaussWorkListComplete.workPackets, GaussCertificateWorkList.workPackets,
    workPacket_eq]

theorem physical_item_coefficient {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    GaussCoefficientProgram.machine.OutputsWithin
      (GaussWorkItemContextSerialize.workPacket B f j)
      (GaussCertificateVectorABI.coefficientPacket
        (GaussFirstFreeCandidate.directCandidate B f hf j))
      (GaussCoefficientProgram.polynomialCoefficient *
        ((GaussWorkItemContextSerialize.workPacket B f j).length + 1) ^
          GaussCoefficientProgram.polynomialExponent) := by
  simpa only [workPacket_eq] using
    GaussCoefficientProgram.canonical_outputs_poly B f j hf

#print axioms workPackets_eq
#print axioms physical_item_coefficient

end CurrentAdditive.GaussWorkCoefficientBridge
