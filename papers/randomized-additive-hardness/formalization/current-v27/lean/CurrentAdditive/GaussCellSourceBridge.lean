import CurrentAdditive.GaussTypedGetterBridge
import CurrentAdditive.GaussCellSpec

/-!
The four getter coordinates for a Gauss cell can all address the original
stored matrix.  A row-index swap in the request producer has exactly the
semantics of `swapTyped`, so the full-matrix writer need not mutate source
rows in place.
-/

namespace CurrentAdditive.GaussCellSourceBridge

open CurrentAdditive.GaussPhysical
open CurrentAdditive.SequentialTotality

def sourceRow {m : Nat} (r pivot i : Fin m) : Fin m :=
  Equiv.swap r pivot i

theorem swapped_cell {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (j : Fin k) :
    swapTyped B r pivot i j = B (sourceRow r pivot i) j := rfl

def sourceCellPacket {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) : List Bool :=
  cellPacket (decide (i = r))
    (rawOfRat (B (sourceRow r pivot i) j))
    (rawOfRat (B (sourceRow r pivot i) c))
    (rawOfRat (B (sourceRow r pivot r) j))
    (rawOfRat (B (sourceRow r pivot r) c))

theorem sourceCellPacket_value {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) :
    cellPacketValue (decide (i = r))
      (rawOfRat (B (sourceRow r pivot i) j))
      (rawOfRat (B (sourceRow r pivot i) c))
      (rawOfRat (B (sourceRow r pivot r) j))
      (rawOfRat (B (sourceRow r pivot r) c)) =
    clearTyped (swapTyped B r pivot) r c i j := by
  rw [cellPacketValue_canonical]
  simpa only [← swapped_cell] using
    (clearTyped_cellFormula (swapTyped B r pivot) r c i j).symm

#print axioms swapped_cell
#print axioms sourceCellPacket_value

end CurrentAdditive.GaussCellSourceBridge
