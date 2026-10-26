import CurrentAdditive.GaussCellQuotient
import CurrentAdditive.GaussCellSourceBridge
import CurrentAdditive.GaussNestedMatrixMap

/-!
The exact canonical bytes that the physical quotient, product and subtraction
calls must write for one materialized Gauss cell.  These definitions are an
interface between the fixed arithmetic machines and the full-matrix writer;
they are not themselves a machine.
-/

namespace CurrentAdditive.GaussCellArithmeticTarget

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical

def quotientRaw (a pivot : RawRat) : RawRat :=
  CodeDCanonicalSource.rawOfRat (a.value / pivot.value)

def productRaw (a row pivot : RawRat) : RawRat :=
  CodeDCanonicalSource.rawOfRat
    ((quotientRaw a pivot).value * row.value)

def differenceRaw (current column row pivot : RawRat) : RawRat :=
  CodeDCanonicalSource.rawOfRat
    (current.value - (productRaw column row pivot).value)

def cellRaw (flag : Bool)
    (current column row pivot : RawRat) : RawRat :=
  if flag then quotientRaw row pivot
  else differenceRaw current column row pivot

theorem quotient_valid (a pivot : RawRat) :
    (quotientRaw a pivot).Valid :=
  CodeDCanonicalSource.rawOfRat_valid _

theorem product_valid (a row pivot : RawRat) :
    (productRaw a row pivot).Valid :=
  CodeDCanonicalSource.rawOfRat_valid _

theorem difference_valid (current column row pivot : RawRat) :
    (differenceRaw current column row pivot).Valid :=
  CodeDCanonicalSource.rawOfRat_valid _

theorem cellRaw_exact (flag : Bool)
    (current column row pivot : RawRat) :
    cellRaw flag current column row pivot =
      CodeDCanonicalSource.rawOfRat
        (cellPacketValue flag current column row pivot) := by
  cases flag <;>
    simp [cellRaw, quotientRaw, productRaw, differenceRaw,
      cellPacketValue, cellFormula,
      CodeDCanonicalSource.rawOfRat_value]

theorem cellRaw_valid (flag : Bool)
    (current column row pivot : RawRat) :
    (cellRaw flag current column row pivot).Valid := by
  rw [cellRaw_exact]
  exact CodeDCanonicalSource.rawOfRat_valid _

theorem sourceCellPacket_target {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (i : Fin m) (j : Fin k) :
    cellRaw (decide (i = r))
      (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) j))
      (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot i) c))
      (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) j))
      (GaussPhysical.rawOfRat (B (GaussCellSourceBridge.sourceRow r pivot r) c)) =
    GaussPhysical.rawOfRat
      (CurrentAdditive.SequentialTotality.clearTyped
        (CurrentAdditive.SequentialTotality.swapTyped B r pivot) r c i j) := by
  rw [cellRaw_exact, GaussCellSourceBridge.sourceCellPacket_value]
  rfl

theorem preparedCell_swap_eq_sourceCellPacket {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (i : Fin m) (j : Fin k) :
    GaussNestedMatrixMap.preparedCell
      (CurrentAdditive.SequentialTotality.swapTyped B r pivot) r c i j =
    GaussCellSourceBridge.sourceCellPacket B r pivot c i j := rfl

theorem preparedMatrix_swap_eq_sourceRequests {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k) :
    GaussNestedMatrixMap.preparedMatrix
      (CurrentAdditive.SequentialTotality.swapTyped B r pivot) r c =
    (List.finRange m).map (fun i =>
      (List.finRange k).map
        (GaussCellSourceBridge.sourceCellPacket B r pivot c i)) := by
  simp [GaussNestedMatrixMap.preparedMatrix,
    preparedCell_swap_eq_sourceCellPacket]

#print axioms cellRaw_exact
#print axioms cellRaw_valid
#print axioms sourceCellPacket_target
#print axioms preparedCell_swap_eq_sourceCellPacket
#print axioms preparedMatrix_swap_eq_sourceRequests

end CurrentAdditive.GaussCellArithmeticTarget
