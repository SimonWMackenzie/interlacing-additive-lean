import Paper2.YaoMaterializationTape
import Paper2.YaoMaterializationTable

/-!
# The serialized Yao matrix generator

Frozen v12 Appendix B, `yao:dimensions`, `yao:random-bits`, and
`yao:materialization`. Vertices have canonical labels `Fin vertexCount`;
edges are indexed embeddings. A literal Boolean input list of the fixed
public length is decoded and every matrix entry is printed in row-major
order. The construction never asks for a colouring or tests a sampling event.

The output getter is proved to be exactly the matrix already used in the
communication and probability proofs. The explicit output-loop counters
charge entry evaluations and list cells only. They are not an encoded-machine
time bound: costs of entry evaluation, list access, arithmetic, source
encoding, and its external reduction remain separate obligations.
-/

namespace Paper2.YaoMaterialization

open Paper2.Yao Paper2.YaoLookup Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization

/-- Number of indexed output rows; duplicate selector values retain labels. -/
def rowCount (vertexCount t b lambda : ℕ) : ℕ :=
  vertexCount * selectorCount t b lambda

/-- Number of indexed columns, ordered by query, edge address, then payload. -/
def columnCount (t b lambda : ℕ) : ℕ :=
  2 ^ (t - 1) * 2 ^ b * payloadCount t b lambda

/-- Computational row numbering; the selector label changes fastest. -/
def rowIndex (vertexCount t b lambda : ℕ) :
    (Fin vertexCount × Fin (selectorCount t b lambda)) ≃
      Fin (rowCount vertexCount t b lambda) :=
  finProdFinEquiv

/-- Computational column numbering; the payload label changes fastest. -/
def columnIndex (t b lambda : ℕ) :
    (Fin (2 ^ (t - 1)) × Fin (2 ^ b) × Fin (payloadCount t b lambda)) ≃
      Fin (columnCount t b lambda) :=
  tripleIndex _ _ _

@[simp] theorem rowIndex_val (vertexCount t b lambda : ℕ)
    (v : Fin vertexCount) (z : Fin (selectorCount t b lambda)) :
    (rowIndex vertexCount t b lambda (v, z)).val =
      v.val * selectorCount t b lambda + z.val := by
  change z.val + selectorCount t b lambda * v.val = _
  ring

@[simp] theorem columnIndex_val (t b lambda : ℕ)
    (g : Fin (2 ^ (t - 1))) (a : Fin (2 ^ b))
    (l : Fin (payloadCount t b lambda)) :
    (columnIndex t b lambda (g, a, l)).val =
      (g.val * 2 ^ b + a.val) * payloadCount t b lambda + l.val :=
  tripleIndex_val _ _ _ g a l

/-- Decode the actual list, then use the executable incidence evaluator on
the original indexed source. These are the entries printed by the loop. -/
def indexedMatrix {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    Fin (rowCount vertexCount t (paddedEdgeBits edgeCount) lambda) →
      Fin (columnCount t (paddedEdgeBits edgeCount) lambda) → Bool :=
  fun i j => matrixFromTape t lambda edges
    (readTape t (paddedEdgeBits edgeCount) lambda bits)
    ((rowIndex vertexCount t (paddedEdgeBits edgeCount) lambda).symm i)
    ((columnIndex t (paddedEdgeBits edgeCount) lambda).symm j)

/-- Actual finite Boolean-list output, with its exact public dimensions. -/
def materialize {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    SerializedTable (rowCount vertexCount t (paddedEdgeBits edgeCount) lambda)
      (columnCount t (paddedEdgeBits edgeCount) lambda) :=
  tabulate (indexedMatrix t lambda edges bits)

@[simp] theorem materialize_length {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    (materialize t lambda edges bits).bits.length =
      vertexCount * selectorCount t (paddedEdgeBits edgeCount) lambda *
        2 ^ (t - 1) * paddedEdgeCount edgeCount *
          payloadCount t (paddedEdgeBits edgeCount) lambda := by
  rw [show (materialize t lambda edges bits).bits.length =
    rowCount vertexCount t (paddedEdgeBits edgeCount) lambda *
      columnCount t (paddedEdgeBits edgeCount) lambda from (materialize _ _ _ _).length]
  simp only [rowCount, columnCount, paddedEdgeCount, Nat.mul_assoc]

@[simp] theorem materialize_matrix {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    (materialize t lambda edges bits).matrix = indexedMatrix t lambda edges bits := by
  funext i j
  exact tabulate_matrix _ i j

/-- Reading the printed table at the announced row and column indices
returns the exact entry of the original fair-tape construction. -/
theorem materialize_entry {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda)
    (v : Fin vertexCount) (z : Fin (selectorCount t (paddedEdgeBits edgeCount) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount edgeCount))
    (l : Fin (payloadCount t (paddedEdgeBits edgeCount) lambda)) :
    (materialize t lambda edges bits).matrix
      (rowIndex vertexCount t (paddedEdgeBits edgeCount) lambda (v, z))
      (columnIndex t (paddedEdgeBits edgeCount) lambda (g, a, l)) =
    matrixFromTape t lambda edges
      (readTape t (paddedEdgeBits edgeCount) lambda bits) (v, z) (g, a, l) := by
  simp only [materialize_matrix, indexedMatrix, Equiv.symm_apply_apply]
  rfl

/-- The serialized output has exactly the communication complexity of the
already-proved fair-tape matrix, with no reindexing overhead. -/
theorem materialize_Dalt {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) (s : Turn) :
    Dalt s (materialize t lambda edges bits).matrix =
      Dalt s (matrixFromTape t lambda edges
        (readTape t (paddedEdgeBits edgeCount) lambda bits)) := by
  rw [materialize_matrix]
  exact Dalt_comap_equiv s _
    (rowIndex vertexCount t (paddedEdgeBits edgeCount) lambda).symm
    (columnIndex t (paddedEdgeBits edgeCount) lambda).symm

/-- A total parser for ordinary bit lists. Rejection checks only the public
length, never any source or sampling promise. -/
def materializeList {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : List Bool) :
    Option (SerializedTable (rowCount vertexCount t (paddedEdgeBits edgeCount) lambda)
      (columnCount t (paddedEdgeBits edgeCount) lambda)) :=
  if h : bits.length = tapeBitCount t (paddedEdgeBits edgeCount) lambda then
    some (materialize t lambda edges ⟨bits, h⟩)
  else none

@[simp] theorem materializeList_valid {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    materializeList t lambda edges bits.val = some (materialize t lambda edges bits) := by
  simp [materializeList, bits.property]

theorem materializeList_invalid {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : List Bool)
    (h : bits.length ≠ tapeBitCount t (paddedEdgeBits edgeCount) lambda) :
    materializeList t lambda edges bits = none := by
  simp [materializeList, h]

/-- A concrete three-field output packet. Binary encoding of these natural
number headers is deliberately not asserted by this definition. -/
def materializePacket {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) : ℕ × ℕ × List Bool :=
  (rowCount vertexCount t (paddedEdgeBits edgeCount) lambda,
    columnCount t (paddedEdgeBits edgeCount) lambda, (materialize t lambda edges bits).bits)

/-- The same output loop with explicit evaluation-call and list-cell counters. -/
def countedMaterialize {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) : CountedOutput :=
  countedTabulate (indexedMatrix t lambda edges bits)

theorem countedMaterialize_bits {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    (countedMaterialize t lambda edges bits).bits = (materialize t lambda edges bits).bits :=
  countedTabulate_bits _

theorem countedMaterialize_counts {vertexCount edgeCount : ℕ} (t lambda : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    (countedMaterialize t lambda edges bits).entryCalls =
      rowCount vertexCount t (paddedEdgeBits edgeCount) lambda *
        columnCount t (paddedEdgeBits edgeCount) lambda ∧
    (countedMaterialize t lambda edges bits).consCells =
      rowCount vertexCount t (paddedEdgeBits edgeCount) lambda *
        columnCount t (paddedEdgeBits edgeCount) lambda :=
  ⟨countedTabulate_entryCalls _, countedTabulate_consCells _⟩

/-- Every correctly sized tape prints a YES table with the stated budget. -/
theorem materialize_yes_bound {vertexCount edgeCount : ℕ} (t lambda : ℕ) (ht : 1 ≤ t)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (colour : Fin vertexCount → Fin (2 ^ t))
    (hbalanced : ∀ e c, 2 ^ t - 1 ≤ colourFiberCard (fun i => colour (edges e i)) c)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    Dalt .alice (materialize t lambda edges bits).matrix ≤
      2 * paddedEdgeBits edgeCount + 4 * t + 2 := by
  rw [materialize_Dalt]
  exact every_tape_yes_bound t lambda ht edges colour hbalanced _

theorem materialize_universal_bound {vertexCount edgeCount : ℕ}
    (t lambda : ℕ) (ht : 1 ≤ t)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (bits : SerializedTape t (paddedEdgeBits edgeCount) lambda) :
    Dalt .alice (materialize t lambda edges bits).matrix ≤
      (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t := by
  rw [materialize_Dalt]
  exact every_tape_universal_bound t lambda ht edges _

/-- The success probability concerns the getter of the actual printed list
under uniform lists of the exact input length, not a replacement matrix. -/
theorem materialize_no_success {vertexCount edgeCount : ℕ}
    (t lambda : ℕ) (ht : 4 ≤ t) (hlambda : 0 < lambda)
    (edges : Fin edgeCount → Fin (2 ^ t * 2 ^ t) ↪ Fin vertexCount)
    (hno : ∀ colour : Fin vertexCount → Fin (2 ^ (2 ^ t - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    1 - 2 * (1 / 2 : ℝ) ^ lambda ≤
      (serializedTapeLaw t (paddedEdgeBits edgeCount) lambda).prob (fun bits =>
        (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t - 6 ≤
          Dalt .alice (materialize t lambda edges bits).matrix) := by
  simp_rw [materialize_Dalt]
  exact (fair_tape_no_success t lambda ht hlambda edges hno).trans_eq
    (serializedTapeLaw_flat_prob t (paddedEdgeBits edgeCount) lambda (fun tape =>
      (2 * paddedEdgeBits edgeCount + 4 * t + 2) + 2 * t - 6 ≤
        Dalt .alice (matrixFromTape t lambda edges tape))).symm

/-- The fixed-gap guarantee is preserved by actual bit-list/table-list
materialization. It is still conditional on the explicit source NO promise. -/
theorem materialize_fixed_gap_success {vertexCount edgeCount : ℕ}
    (g : ℕ)
    (edges : Fin edgeCount → Fin (2 ^ gapParameter g * 2 ^ gapParameter g) ↪ Fin vertexCount)
    (hno : ∀ colour : Fin vertexCount → Fin (2 ^ (2 ^ gapParameter g - 1)),
      ∃ e c, ∀ i, colour (edges e i) = c) :
    (511 / 512 : ℝ) ≤
      (serializedTapeLaw (gapParameter g) (paddedEdgeBits edgeCount) 10).prob (fun bits =>
        (2 * paddedEdgeBits edgeCount + 4 * gapParameter g + 2) + g ≤
          Dalt .alice (materialize (gapParameter g) 10 edges bits).matrix) := by
  simp_rw [materialize_Dalt]
  exact (fair_tape_fixed_gap_success g edges hno).trans_eq
    (serializedTapeLaw_flat_prob (gapParameter g) (paddedEdgeBits edgeCount) 10 (fun tape =>
      (2 * paddedEdgeBits edgeCount + 4 * gapParameter g + 2) + g ≤
        Dalt .alice (matrixFromTape (gapParameter g) 10 edges tape))).symm

end Paper2.YaoMaterialization
