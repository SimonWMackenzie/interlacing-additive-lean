import CurrentAdditive.GaussCellSourceBridge
import CurrentAdditive.GaussCellClock

/-! Uniform request size before the physical row-swap-on-access getter. -/

namespace CurrentAdditive.GaussSourceCellClock

open CurrentAdditive.GaussPhysical
open CurrentAdditive.GaussCellSourceBridge

theorem actual_source_cell_packet_length {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t ≤ k)
    (r pivot i : Fin m) (c j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
    (sourceCellPacket B r pivot c i j).length ≤
      32 * ((m + 3) * (m + 1)^2 + 1) + 54 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
  let S := (m+3)*(m+1)^2+1
  have hentry (u : Fin m) (v : Fin k) :
      Nat.size (B u v).den ≤ S ∧
      Nat.size (B u v).num.natAbs ≤ S :=
    CurrentAdditive.EliminationEntryBounds.every_actual_step_entry_bits
      A h01 t ht u v
  apply canonicalCellPacket_length (decide (i = r)) _ _ _ _ S
  · exact (hentry (sourceRow r pivot i) j).2
  · exact (hentry (sourceRow r pivot i) j).1
  · exact (hentry (sourceRow r pivot i) c).2
  · exact (hentry (sourceRow r pivot i) c).1
  · exact (hentry (sourceRow r pivot r) j).2
  · exact (hentry (sourceRow r pivot r) j).1
  · exact (hentry (sourceRow r pivot r) c).2
  · exact (hentry (sourceRow r pivot r) c).1

#print axioms actual_source_cell_packet_length

end CurrentAdditive.GaussSourceCellClock
