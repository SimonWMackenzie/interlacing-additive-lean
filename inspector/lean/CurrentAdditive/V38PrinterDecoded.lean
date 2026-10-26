import CurrentAdditive.V38PrinterIndex

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.UnaryFieldListParserScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def canonicalDecodedBank {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    CanonicalCell → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (canonicalReady b t d modulus edges i.val j.val)
      (canonicalIndexPlace 8)
      (List.replicate (((rowIndex v b t).symm i).1.val) true))
    (canonicalIndexPlace 9)
      (List.replicate (((rowIndex v b t).symm i).2.val) true))
    (canonicalIndexPlace 10)
      (List.replicate (((columnIndex b t d).symm j).1.val) true))
    (canonicalIndexPlace 11)
      (List.replicate (((columnIndex b t d).symm j).2.1.val) true))
    (canonicalIndexPlace 12)
      (List.replicate (((columnIndex b t d).symm j).2.2.val) true)

/-- The fixed coordinate program receives exactly the decoded row and
column coordinates, source incidence stream, and public unary constants. -/
theorem canonicalDecoded_coord_inputs {v e : ℕ} (b t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    let S := canonicalDecodedBank b t d modulus edges i j
    S (canonicalCoordPlace 0) =
      List.replicate (((rowIndex v b t).symm i).2.val) true ∧
    S (canonicalCoordPlace 1) =
      List.replicate (((columnIndex b t d).symm j).1.val) true ∧
    S (canonicalCoordPlace 2) = List.replicate (2 ^ b) true ∧
    S (canonicalCoordPlace 3) =
      List.replicate (((columnIndex b t d).symm j).2.1.val) true ∧
    S (canonicalCoordPlace 4) =
      List.replicate (((rowIndex v b t).symm i).1.val) true ∧
    S (canonicalCoordPlace 5) = tokens (List.ofFn (flatten edges)) ∧
    S (canonicalCoordPlace 6) = List.replicate (2 ^ t * 2 ^ t) true ∧
    (∀ k : Fin 40, 7 ≤ k.val → S (canonicalCoordPlace k) = []) := by
  dsimp only
  dsimp only [canonicalDecodedBank]
  refine ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, by rfl, ?_⟩
  intro k hk
  fin_cases k <;> (try simp at hk) <;> rfl

#print axioms canonicalDecoded_coord_inputs

end CurrentAdditive.V38TablePrinter
