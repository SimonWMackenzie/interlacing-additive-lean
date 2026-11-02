import CurrentAdditive.V38PrinterTable

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup

/-- The row and column values supplied to the physical index decoder are
bounded by the dimensions of the actual printed table. The empty-table case
needs no special assumption: there is no entry index to inspect. -/
theorem canonical_index_clock_at_cell {v e : ℕ} (t d : ℕ)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    canonicalIndexClock (paddedEdgeBits e) t d i.val j.val ≤
      32 * (rowCount v (paddedEdgeBits e) t +
        columnCount (paddedEdgeBits e) t d + 1) := by
  have hv : 0 < v := by
    by_contra h
    have hz : v = 0 := Nat.eq_zero_of_not_pos h
    have hi := i.isLt
    simp [rowCount, hz] at hi
  exact canonicalIndexClock_linear v (paddedEdgeBits e) t d i.val j.val
    hv i.isLt j.isLt

/-- The finite maximum used by the row-major writer inherits any common
pointwise transition bound. This is the exact supremum boundary to which the
polynomial clock estimate will be applied. -/
theorem canonical_uniform_clock_le_of_pointwise {v e : ℕ}
    (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (B : ℕ)
    (hB : ∀ (i : Fin (rowCount v (paddedEdgeBits e) t))
        (j : Fin (columnCount (paddedEdgeBits e) t d)),
      canonicalEntryClock t d modulus edges i j ≤ B) :
    canonicalUniformEntryClock t d modulus edges ≤ B := by
  unfold canonicalUniformEntryClock
  apply Finset.sup_le
  intro ij _
  exact hB ij.1 ij.2

/-- The cleanup phase pops precisely the five decoded indices and the
selected payload coordinate. In particular its clock does not depend on
any hidden workspace left by the arithmetic subroutines. -/
theorem canonical_cleanup_time_exact {v e : ℕ}
    (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    canonicalCleanupTime
      (Function.update
        (canonicalCoordinateBank (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j)
        (.inr 2)
        [numericEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j]) =
      (((rowIndex v (paddedEdgeBits e) t).symm i).1.val +
        ((rowIndex v (paddedEdgeBits e) t).symm i).2.val +
        ((columnIndex (paddedEdgeBits e) t d).symm j).1.val +
        ((columnIndex (paddedEdgeBits e) t d).symm j).2.1.val +
        ((columnIndex (paddedEdgeBits e) t d).symm j).2.2.val +
        (numericPayloadCoord (paddedEdgeBits e) t d
          (le_paddedEdgeCount e) edges i j).val) + 8 := by
  let A : CanonicalCell → List Bool :=
    Function.update
      (canonicalCoordinateBank (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges i j)
      (.inr 2)
      [numericEntry (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges i j]
  have h0 : A (canonicalCleanupSlots 0) =
      List.replicate (((rowIndex v (paddedEdgeBits e) t).symm i).1.val) true := by rfl
  have h1 : A (canonicalCleanupSlots 1) =
      List.replicate (((rowIndex v (paddedEdgeBits e) t).symm i).2.val) true := by rfl
  have h2 : A (canonicalCleanupSlots 2) =
      List.replicate (((columnIndex (paddedEdgeBits e) t d).symm j).1.val) true := by rfl
  have h3 : A (canonicalCleanupSlots 3) =
      List.replicate (((columnIndex (paddedEdgeBits e) t d).symm j).2.1.val) true := by rfl
  have h4 : A (canonicalCleanupSlots 4) =
      List.replicate (((columnIndex (paddedEdgeBits e) t d).symm j).2.2.val) true := by rfl
  have h5 : A (canonicalCleanupSlots 5) =
      List.replicate (numericPayloadCoord (paddedEdgeBits e) t d
        (le_paddedEdgeCount e) edges i j).val true := by rfl
  change canonicalCleanupTime A = _
  simp only [canonicalCleanupTime, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (A (canonicalCleanupSlots 0)).length +
      ((A (canonicalCleanupSlots 1)).length +
      ((A (canonicalCleanupSlots 2)).length +
      ((A (canonicalCleanupSlots 3)).length +
      ((A (canonicalCleanupSlots 4)).length +
        (A (canonicalCleanupSlots 5)).length)))) + 8 = _
  rw [h0, h1, h2, h3, h4, h5]
  simp only [List.length_replicate]
  omega

/-- The cleanup clock is linear in the dimensions and the width of one
packed-field word. This charges all six restored scratch cells explicitly. -/
theorem canonical_cleanup_time_bound {v e : ℕ}
    (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    canonicalCleanupTime
      (Function.update
        (canonicalCoordinateBank (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j)
        (.inr 2)
        [numericEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j]) ≤
      2 * rowCount v (paddedEdgeBits e) t +
        3 * columnCount (paddedEdgeBits e) t d +
        2 ^ (paddedEdgeBits e) * (2 ^ t * 2 ^ t + 1) + 8 := by
  let b := paddedEdgeBits e
  let R := rowCount v b t
  let C := columnCount b t d
  let H := 2 ^ b
  let q := 2 ^ (t - 1)
  let R2 := (2 ^ d) ^ 2
  let row := (rowIndex v b t).symm i
  let col := (columnIndex b t d).symm j
  have hv : 0 < v := by
    by_contra h
    have hz : v = 0 := Nat.eq_zero_of_not_pos h
    have hi := i.isLt
    simp [R, rowCount, hz] at hi
  have hq : 0 < q := by dsimp [q]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hR2 : 0 < R2 := by dsimp [R2]; positivity
  have hHq : 0 < H ^ q := by positivity
  have hvR : v ≤ R := by
    dsimp [R, rowCount]
    have hh : 1 ≤ H ^ q := by omega
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left v hh
  have hHqR : H ^ q ≤ R := by
    dsimp [R, rowCount]
    have hh : 1 ≤ v := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (H ^ q) hh
  have hqC : q ≤ C := by
    dsimp [C, columnCount]
    have hh : 1 ≤ H * R2 := by nlinarith
    simpa only [Nat.mul_one, mul_assoc] using Nat.mul_le_mul_left q hh
  have hHC : H ≤ C := by
    dsimp [C, columnCount]
    have hh : 1 ≤ q * R2 := by nlinarith
    calc
      H = 1 * H := by ring
      _ ≤ (q * R2) * H := Nat.mul_le_mul_right H hh
      _ = q * H * R2 := by ring
  have hR2C : R2 ≤ C := by
    dsimp [C, columnCount]
    have hh : 1 ≤ q * H := by nlinarith
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right R2 hh
  have hr0 : row.1.val < R := row.1.isLt.trans_le hvR
  have hr1 : row.2.val < R := row.2.isLt.trans_le hHqR
  have hc0 : col.1.val < C := col.1.isLt.trans_le hqC
  have hc1 : col.2.1.val < C := col.2.1.isLt.trans_le hHC
  have hc2 : col.2.2.val < C := col.2.2.isLt.trans_le hR2C
  have hp := (numericPayloadCoord b t d (le_paddedEdgeCount e) edges i j).isLt
  rw [canonical_cleanup_time_exact]
  dsimp only [row, col, R, C, b] at *
  omega

#print axioms canonical_index_clock_at_cell
#print axioms canonical_uniform_clock_le_of_pointwise
#print axioms canonical_cleanup_time_exact
#print axioms canonical_cleanup_time_bound

end CurrentAdditive.V38TablePrinter
