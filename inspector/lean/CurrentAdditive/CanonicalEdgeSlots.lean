import CurrentAdditive.CanonicalSelector
import Paper2.YaoLookupEvaluation

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup

/-- Real edges occupy their numerical slots; the remaining public
addresses are empty. No classical choice is involved in this evaluator. -/
def edgeSlots {v e K H : ℕ} (he : e ≤ H)
    (edges : Fin e → Fin K ↪ Fin v) :
    Fin H → Option (Fin K ↪ Fin v) :=
  fun α => if h : α.val < e then some (edges ⟨α.val, h⟩) else none

theorem edgeSlots_eq_placeEdges {v e K H : ℕ} (he : e ≤ H)
    (edges : Fin e → Fin K ↪ Fin v) :
    edgeSlots he edges = placeEdges edges (Fin.castLEEmb he) := by
  funext α
  by_cases h : α.val < e
  · let j : Fin e := ⟨α.val, h⟩
    have hj : (Fin.castLEEmb he) j = α := Fin.ext rfl
    have hp := placeEdges_real edges (Fin.castLEEmb he) j
    rw [hj] at hp
    simpa only [edgeSlots, dif_pos h] using hp.symm
  · rw [edgeSlots, dif_neg h]
    symm
    apply placeEdges_unused
    intro j hj
    have hv : j.val = α.val := congrArg Fin.val hj
    exact h (hv ▸ j.isLt)

/-- Literal finite scan for the position of a vertex in a chosen edge. -/
def position {v e K H : ℕ} (he : e ≤ H)
    (edges : Fin e → Fin K ↪ Fin v)
    (α : Fin H) (vertex : Fin v) : Fin (K + 1) :=
  positionEval (edgeSlots he edges) α vertex

theorem position_eq_source {v e K H : ℕ} (he : e ≤ H)
    (edges : Fin e → Fin K ↪ Fin v)
    (α : Fin H) (vertex : Fin v) :
    position he edges α vertex =
      Paper2.YaoLookup.position (placeEdges edges (Fin.castLEEmb he)) α vertex := by
  rw [position, positionEval_eq, edgeSlots_eq_placeEdges]

#print axioms edgeSlots_eq_placeEdges
#print axioms position_eq_source

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
