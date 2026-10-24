import CurrentAdditive.CanonicalWriterLookupRun

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup

/-- The physical coordinate callback's selector-plus-incidence value is the
exact address needed by the packed-field lookup, at the source's least
power-of-two edge padding. -/
theorem canonical_coord_value {v e : ℕ} (t d : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    (selector (2 ^ (t - 1)) (paddedEdgeCount e)
        ((rowIndex v (paddedEdgeBits e) t).symm i).2
        ((columnIndex (paddedEdgeBits e) t d).symm j).1).val *
      (2 ^ t * 2 ^ t + 1) +
      (position (le_paddedEdgeCount e) edges
        ((columnIndex (paddedEdgeBits e) t d).symm j).2.1
        ((rowIndex v (paddedEdgeBits e) t).symm i).1).val =
      (numericPayloadCoord (paddedEdgeBits e) t d
        (le_paddedEdgeCount e) edges i j).val := by
  rfl

#print axioms canonical_coord_value

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
