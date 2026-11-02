import CurrentAdditive.CanonicalPackedEntry

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias
open EthInapproximability.CurrentPaper

/-- With its pair label, payload coordinate, and packed source array prepared,
the old fixed lookup program emits the exact canonical matrix entry. -/
theorem physical_canonical_entry_bit {v e : ℕ}
    (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d))
    (out : List Bool) :
    ∃ steps ≤ 32 *
      ((((columnIndex b t d).symm j).2.2).val +
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (numericPayloadCoord b t d he edges i j).val +
        (packedFieldBits d modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1))).length + 1) ^ 2,
      MatrixTableLookup.run steps
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial
          (List.replicate (((columnIndex b t d).symm j).2.2).val true)
          (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
          (List.replicate (numericPayloadCoord b t d he edges i j).val true)
          [] (packedFieldBits d modulus
            (2 ^ b * (2 ^ t * 2 ^ t + 1))) out) =
      MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate (((columnIndex b t d).symm j).2.2).val true)
        (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
        (List.replicate (numericPayloadCoord b t d he edges i j).val true)
        [] (packedFieldBits d modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1)))
        (numericEntry b t d modulus he edges i j :: out) := by
  let ℓ := ((columnIndex b t d).symm j).2.2
  let coord := numericPayloadCoord b t d he edges i j
  obtain ⟨steps, ht, hr⟩ := physical_packed_field_bit d modulus
    (2 ^ b * (2 ^ t * 2 ^ t + 1)) ℓ coord out
  have hentry := numericEntry_eq_packedFieldBits b t d modulus he edges i j
  rw [packedFieldBits_get] at hentry
  refine ⟨steps, ht, ?_⟩
  simpa only [ℓ, coord, hentry] using hr

#print axioms physical_canonical_entry_bit

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
