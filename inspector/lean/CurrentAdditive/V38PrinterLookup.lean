import CurrentAdditive.V38PrinterLift

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def canonicalCoordinateBank {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    CanonicalCell → List Bool :=
  Function.update (canonicalDecodedBank b t d modulus edges i j)
    (canonicalCoordPlace 7)
    (List.replicate (numericPayloadCoord b t d he edges i j).val true)

/-- After the numeric coordinate has been physically prepared in cell 12,
the inherited packed-array reader runs on the writer bank and writes the
exact entry in the writer's answer cell. All static cells are preserved. -/
theorem canonical_writer_lookup_run {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    ∃ steps ≤ canonicalLookupClock b t d,
      ((advance (canonicalLookupProgramOn canonicalLookupPlace))^[steps])
        (⟨some MatrixTableLookup.start, MatrixTableLookup.initial,
          canonicalCoordinateBank b t d modulus he edges i j⟩ :
          TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
        ⟨none, MatrixTableLookup.initial,
          Function.update (canonicalCoordinateBank b t d modulus he edges i j)
            (.inr 2) [numericEntry b t d modulus he edges i j]⟩ := by
  have h0 : (canonicalCoordinateBank b t d modulus he edges i j)
      (canonicalLookupPlace 0) =
      List.replicate (((columnIndex b t d).symm j).2.2).val true := by rfl
  have h1 : (canonicalCoordinateBank b t d modulus he edges i j)
      (canonicalLookupPlace 1) =
      List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true := by rfl
  have h2 : (canonicalCoordinateBank b t d modulus he edges i j)
      (canonicalLookupPlace 2) =
      List.replicate (numericPayloadCoord b t d he edges i j).val true := by rfl
  have h6 : (canonicalCoordinateBank b t d modulus he edges i j)
      (canonicalLookupPlace 6) =
      bankBits b t d modulus := by rfl
  have hs : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 6 →
      (canonicalCoordinateBank b t d modulus he edges i j)
        (canonicalLookupPlace k) = [] := by
    intro k h0' h1' h2' h6'
    fin_cases k <;> (try contradiction) <;> rfl
  obtain ⟨steps, ht, hr⟩ := physical_canonical_entry_lift
    canonicalLookupPlace
    (canonicalCoordinateBank b t d modulus he edges i j)
    b t d modulus he edges i j h0 h1 h2 h6 hs
  exact ⟨steps, ht, by simpa [canonicalLookupPlace] using hr⟩

#print axioms canonical_writer_lookup_run

end CurrentAdditive.V38TablePrinter
