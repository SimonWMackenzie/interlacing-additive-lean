import CurrentAdditive.CanonicalPrintedTable

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias

/-- Row-major row decoding uses quotient and remainder by the number of
selector tuples. -/
theorem row_decode_numeric (v b t : ℕ)
    (i : Fin (rowCount v b t)) :
    ((rowIndex v b t).symm i).1.val =
        i.val / (2 ^ b) ^ (2 ^ (t - 1)) ∧
      ((rowIndex v b t).symm i).2.val =
        i.val % (2 ^ b) ^ (2 ^ (t - 1)) := by
  constructor <;> rfl

/-- A column decodes first into query and address, then into a pair-seed
label; the seed label is the fastest-changing coordinate. -/
theorem column_decode_numeric (b t d : ℕ)
    (j : Fin (columnCount b t d)) :
    (((columnIndex b t d).symm j).1).val =
        (j.val / (2 ^ d) ^ 2) / 2 ^ b ∧
      (((columnIndex b t d).symm j).2.1).val =
        (j.val / (2 ^ d) ^ 2) % 2 ^ b ∧
      (((columnIndex b t d).symm j).2.2).val =
        j.val % (2 ^ d) ^ 2 := by
  constructor
  · rfl
  constructor <;> rfl

/-- The computational selector equivalence reads the selected base-`H`
digit of the row label. -/
theorem selector_digit_numeric (q H : ℕ) (z : Fin (H ^ q))
    (g : Fin q) :
    (selector q H z g).val = z.val / H ^ g.val % H := by
  rfl

/-- The finite-field seed pair is the quotient and remainder of its
row-major label by `R=2^d`. -/
theorem seed_pair_decode_numeric (d : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2)) :
    (((printerPairLabel d).symm ℓ).1).val = ℓ.val / 2 ^ d ∧
      (((printerPairLabel d).symm ℓ).2).val = ℓ.val % 2 ^ d := by
  constructor <;> rfl

/-- The callback's entry value with all selector, seed, and payload
coordinates exposed as integer operations. -/
def numericEntry {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) : Bool :=
  let row := (rowIndex v b t).symm i
  let col := (columnIndex b t d).symm j
  let H := 2 ^ b
  let R := 2 ^ d
  let α : Fin H := ⟨row.2.val / H ^ col.1.val % H,
    Nat.mod_lt _ (by positivity)⟩
  let p := position he edges col.2.1 row.1
  BitPrinter.bit d modulus (col.2.2.val / R) (col.2.2.val % R)
    (α.val * (2 ^ t * 2 ^ t + 1) + p.val)

theorem entry_eq_numericEntry {v e : ℕ} (b t d modulus : ℕ)
    (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    entry b t d modulus he edges i j =
      numericEntry b t d modulus he edges i j := by
  simp only [entry, numericEntry, printedPairFieldWord]
  rw [show selector (2 ^ (t - 1)) (2 ^ b)
      ((rowIndex v b t).symm i).2 ((columnIndex b t d).symm j).1 =
      ⟨((rowIndex v b t).symm i).2.val /
        (2 ^ b) ^ (((columnIndex b t d).symm j).1).val % (2 ^ b),
        Nat.mod_lt _ (by positivity)⟩ from
      Fin.ext (selector_digit_numeric _ _ _ _)]
  have hseed := seed_pair_decode_numeric d
    ((columnIndex b t d).symm j).2.2
  rw [hseed.1, hseed.2]
  simp [finProdFinEquiv]
  ring_nf

#print axioms row_decode_numeric
#print axioms column_decode_numeric
#print axioms selector_digit_numeric
#print axioms seed_pair_decode_numeric
#print axioms entry_eq_numericEntry

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
