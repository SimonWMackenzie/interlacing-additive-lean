import CurrentAdditive.GaussCertificatePreparedOuter
import CurrentAdditive.GaussWorkCoefficientBridge

/-! The admitted polynomial coefficient program is the concrete callback of
the checked vector writer on the exact V2 work list physically assembled
after the Gauss state. -/

namespace CurrentAdditive.GaussCoefficientOuterJoin

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussCertificateWorkList
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.GaussFirstFreeCandidate

noncomputable def itemClock (x : List Bool) : Nat :=
  GaussCoefficientProgram.polynomialCoefficient *
    (x.length + 1) ^ GaussCoefficientProgram.polynomialExponent

theorem result_eq_candidate {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    GaussCoefficientProgram.result (workPacket B f j) =
      coefficientPacket (directCandidate B f hf j) := by
  exact BitMachine.outputsWithin_unique GaussCoefficientProgram.machine
    (GaussCoefficientProgram.outputs_all (workPacket B f j))
    (GaussCoefficientProgram.canonical_outputs_poly B f j hf)

theorem outputs_physical_work_list {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) (hf : f.val ≤ m) :
    (GaussVectorOuterWriter.machine GaussCoefficientProgram.machine).OutputsWithin
      (SourceListEncoding.encode (GaussWorkListComplete.workPackets B f))
      (vectorPacket (Array.ofFn (directCandidate B f hf)))
      (SourceListMachineOuter.canonicalBound
        (GaussVectorOuterWriter.framedMachine GaussCoefficientProgram.machine)
        (workPackets B f)
        (fun x => SourceListMachineWriter.result true (GaussCoefficientProgram.result x))
        (GaussVectorOuterWriter.itemClock GaussCoefficientProgram.result itemClock)) := by
  have h := GaussCertificatePreparedOuter.outputs_prepared_direct
    B f hf GaussCoefficientProgram.machine GaussCoefficientProgram.result itemClock
    (fun j => result_eq_candidate B f j hf)
    (fun j => by
      simpa only [itemClock] using
        GaussCoefficientProgram.outputs_poly (workPacket B f j))
  simpa only [GaussWorkCoefficientBridge.workPackets_eq] using h

#print axioms outputs_physical_work_list

end CurrentAdditive.GaussCoefficientOuterJoin
