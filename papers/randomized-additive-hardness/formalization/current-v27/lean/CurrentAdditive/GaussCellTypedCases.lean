import CurrentAdditive.GaussCellSubtractCall
import CurrentAdditive.GaussCellArithmeticTarget

/-! Exact typed cell semantics of the two physical arithmetic paths. -/

namespace CurrentAdditive.GaussCellTypedCases

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical
open EthInapproximability.CurrentPaper

theorem nonpivot_case {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c j : Fin k) (hneq : i ≠ r)
    (hnum : 0 < EncodedCommunication.bitsValue
      (rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c)).numerator) :
    ∃ T, GaussCellSubtractCall.machine.OutputsWithin
      (GaussCellSourceBridge.sourceCellPacket B r pivot c i j)
      (encodeRawRat (rawOfRat
        (SequentialTotality.clearTyped
          (SequentialTotality.swapTyped B r pivot) r c i j))) T := by
  let current := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) j)
  let column := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) c)
  let row := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) j)
  let p := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c)
  obtain ⟨T,h⟩ := GaussCellSubtractCall.outputs_cell current column row p
    (rawOfRat_valid _) (rawOfRat_valid _) (rawOfRat_valid _)
    (rawOfRat_valid _) hnum
  refine ⟨T, ?_⟩
  have htarget := GaussCellArithmeticTarget.sourceCellPacket_target
    B r pivot c i j
  have htarget' : GaussCellArithmeticTarget.differenceRaw
      current column row p =
      rawOfRat (SequentialTotality.clearTyped
        (SequentialTotality.swapTyped B r pivot) r c i j) := by
    simpa only [current, column, row, p,
      decide_eq_false hneq, GaussCellArithmeticTarget.cellRaw] using htarget
  rw [← htarget']
  simpa only [GaussCellSourceBridge.sourceCellPacket,
    decide_eq_false hneq, current, column, row, p] using h

theorem pivot_case {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c j : Fin k)
    (hnum : 0 < EncodedCommunication.bitsValue
      (rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c)).numerator) :
    ∃ T, GaussCellQuotient.canonicalMachine.OutputsWithin
      (GaussCellSourceBridge.sourceCellPacket B r pivot c r j)
      (encodeRawRat (rawOfRat
        (SequentialTotality.clearTyped
          (SequentialTotality.swapTyped B r pivot) r c r j))) T := by
  let current := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) j)
  let column := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c)
  let row := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) j)
  let p := rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c)
  obtain ⟨T,h⟩ := GaussCellQuotient.canonical_outputs_cell
    true current column row p (rawOfRat_valid _) (rawOfRat_valid _) hnum
  refine ⟨T, ?_⟩
  have htarget := GaussCellArithmeticTarget.sourceCellPacket_target
    B r pivot c r j
  have htarget' : GaussCellArithmeticTarget.quotientRaw row p =
      rawOfRat (SequentialTotality.clearTyped
        (SequentialTotality.swapTyped B r pivot) r c r j) := by
    simpa only [current, column, row, p,
      decide_true, GaussCellArithmeticTarget.cellRaw] using htarget
  rw [← htarget']
  simpa only [GaussCellSourceBridge.sourceCellPacket,
    decide_true, current, column, row, p,
    GaussCellArithmeticTarget.quotientRaw,
    GaussPhysical.rawOfRat] using h

#print axioms nonpivot_case
#print axioms pivot_case

end CurrentAdditive.GaussCellTypedCases
