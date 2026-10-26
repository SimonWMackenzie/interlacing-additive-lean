import CurrentAdditive.IndexedRationalQuarticController
import Paper2.YaoMaterializationTable
import Paper2.CodedEntryEvaluator

/-! An explicit Boolean table, its row-major bit-list lookup, and a
bit-list parser for row and column indices. Indices, not values, are labels. -/

namespace Paper2.IndexedBaseLookup

open Paper2.YaoMaterialization
open Paper2.RecursiveLabelCodecScratch
open Paper2.CodedEntryEvaluatorScratch

/-- The table and both positive integer-mass arrays are concrete input data. -/
structure BasePacket (rows cols : ℕ) where
  table : SerializedTable rows cols
  rowMass : Fin rows → ℕ
  colMass : Fin cols → ℕ
  rowPositive : ∀ i, 0 < rowMass i
  colPositive : ∀ j, 0 < colMass j

/-- Decode both canonical index words and read one actual table bit. -/
def lookup {rows cols : ℕ} (B : BasePacket rows cols)
    (rowBits colBits : List Bool) : Option Bool := do
  let i ← decodeExact (finCodec rows) rowBits
  let j ← decodeExact (finCodec cols) colBits
  pure (B.table.matrix i j)

theorem lookup_encoded {rows cols : ℕ} (B : BasePacket rows cols)
    (i : Fin rows) (j : Fin cols) :
    lookup B ((finCodec rows).encode i) ((finCodec cols).encode j) =
      some (B.table.matrix i j) := by
  simp [lookup, decodeExact_encode]

/-- A row-major packet compiled from an arbitrary Boolean matrix has exactly
that matrix's entries at the queried indexed positions. -/
def ofMatrix {rows cols : ℕ}
    (F : Fin rows → Fin cols → Bool)
    (rowMass : Fin rows → ℕ) (colMass : Fin cols → ℕ)
    (hr : ∀ i, 0 < rowMass i) (hc : ∀ j, 0 < colMass j) :
    BasePacket rows cols where
  table := tabulate F
  rowMass := rowMass
  colMass := colMass
  rowPositive := hr
  colPositive := hc

theorem ofMatrix_lookup {rows cols : ℕ}
    (F : Fin rows → Fin cols → Bool)
    (rowMass : Fin rows → ℕ) (colMass : Fin cols → ℕ)
    (hr : ∀ i, 0 < rowMass i) (hc : ∀ j, 0 < colMass j)
    (i : Fin rows) (j : Fin cols) :
    lookup (ofMatrix F rowMass colMass hr hc)
      ((finCodec rows).encode i) ((finCodec cols).encode j) = some (F i j) := by
  rw [lookup_encoded]
  exact congrArg some (tabulate_matrix F i j)

/-- The same packet supplies the arbitrary-base row and column codes. -/
def rowCode {rows cols : ℕ} (B : BasePacket rows cols) :
    Paper2.GeneratorCode.Code :=
  Paper2.IndexedRationalFinCode.code rows B.rowMass

def colCode {rows cols : ℕ} (B : BasePacket rows cols) :
    Paper2.GeneratorCode.Code :=
  Paper2.IndexedRationalFinCode.code cols B.colMass

#print axioms ofMatrix_lookup

end Paper2.IndexedBaseLookup
