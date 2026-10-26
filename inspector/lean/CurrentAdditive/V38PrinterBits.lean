import CurrentAdditive.V38PaddedBank
import CurrentAdditive.CanonicalEncodedHeader

/-! A new, private adaptation of the old physical canonical renderer.
The mathematical array has exactly H*K bits. Only its internal callback
bank contains one constant-false sentinel before each address block. -/

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open CurrentAdditive.V38Machine
open CurrentAdditive.V38Executable
open EthInapproximability.CurrentPaper

abbrev bankBits (b t d modulus : ℕ) : List Bool :=
  paddedBits b t d modulus

abbrev entry := @CurrentAdditive.V38Executable.entry
abbrev table := @CurrentAdditive.V38Executable.table
abbrev instanceOfTable := @CurrentAdditive.V38Executable.instanceOfTable
abbrev numericEntry := @CurrentAdditive.V38Executable.entry

theorem entry_eq_numericEntry {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b) (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    entry b t d modulus he edges i j =
      numericEntry b t d modulus he edges i j := rfl

theorem bankBits_length (b t d modulus : ℕ) :
    (bankBits b t d modulus).length =
      ((2 ^ d) ^ 2) * (2 ^ b * (2 ^ t * 2 ^ t + 1)) :=
  paddedBits_length b t d modulus

theorem bankBits_getD (b t d modulus : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) (a : Fin (2 ^ b))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    (bankBits b t d modulus)[(paddedIndex b t d ℓ a p).val]?.getD false =
      wordAtPosition (CurrentAdditive.SmallBias.v38PrintedPairWord b t d modulus)
        ℓ a p := by
  have h := paddedBits_get b t d modulus ℓ a p
  have hi : (paddedIndex b t d ℓ a p).val <
      (paddedBits b t d modulus).length := by
    rw [paddedBits_length]
    exact (paddedIndex b t d ℓ a p).isLt
  simpa only [bankBits, List.getElem?_eq_getElem hi, Option.getD_some,
    List.get_eq_getElem] using h

/-- The selected zero-off-edge entry is the exact bit addressed by the
existing physical coordinate calculation in the new padded data bank. -/
theorem numericEntry_eq_bankBits {v e : ℕ}
    (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    numericEntry b t d modulus he edges i j =
      (bankBits b t d modulus)[
        (((columnIndex b t d).symm j).2.2).val *
          (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (numericPayloadCoord b t d he edges i j).val]?.getD false := by
  let row := (rowIndex v b t).symm i
  let col := (columnIndex b t d).symm j
  let a := selector (2 ^ (t - 1)) (2 ^ b) row.2 col.1
  let p := position he edges col.2.1 row.1
  have hidx : (paddedIndex b t d col.2.2 a p).val =
      col.2.2.val * (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (numericPayloadCoord b t d he edges i j).val := by
    change p.val + (2 ^ t * 2 ^ t + 1) * a.val +
        paddedPositionCount b t * col.2.2.val =
      col.2.2.val * (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (a.val * (2 ^ t * 2 ^ t + 1) + p.val)
    unfold paddedPositionCount
    ring
  have h := bankBits_getD b t d modulus col.2.2 a p
  rw [hidx] at h
  exact h.symm

theorem physical_canonical_entry_bit {v e : ℕ}
    (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d))
    (out : List Bool) :
    ∃ steps ≤ 32 *
      ((((columnIndex b t d).symm j).2.2).val +
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (numericPayloadCoord b t d he edges i j).val +
        (bankBits b t d modulus).length + 1) ^ 2,
      MatrixTableLookup.run steps
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial
          (List.replicate (((columnIndex b t d).symm j).2.2).val true)
          (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
          (List.replicate (numericPayloadCoord b t d he edges i j).val true)
          [] (bankBits b t d modulus) out) =
      MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate (((columnIndex b t d).symm j).2.2).val true)
        (List.replicate (2 ^ b * (2 ^ t * 2 ^ t + 1)) true)
        (List.replicate (numericPayloadCoord b t d he edges i j).val true)
        [] (bankBits b t d modulus)
        (numericEntry b t d modulus he edges i j :: out) := by
  obtain ⟨steps, hs, hr⟩ := MatrixTableLookup.lookup_run
    (((columnIndex b t d).symm j).2.2).val
    (2 ^ b * (2 ^ t * 2 ^ t + 1))
    (numericPayloadCoord b t d he edges i j).val
    (bankBits b t d modulus) out
  exact ⟨steps, hs, by
    simpa only [numericEntry_eq_bankBits] using hr⟩

#print axioms numericEntry_eq_bankBits
#print axioms physical_canonical_entry_bit

end CurrentAdditive.V38TablePrinter
