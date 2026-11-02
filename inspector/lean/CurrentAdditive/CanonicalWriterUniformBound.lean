import CurrentAdditive.CanonicalCoordinateClockBudget

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.UnaryFieldListParserScratch
open CurrentAdditive.FiniteFieldCoordinate

set_option maxHeartbeats 2000000

/-- A public size parameter for one cell calculation. It includes both
printed dimensions, the literal encoded edge body, the incidence arity, and
the least edge-address capacity. -/
def canonicalCellSize {v e : ℕ} (t d : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) : ℕ :=
  rowCount v (paddedEdgeBits e) t +
    columnCount (paddedEdgeBits e) t d +
    (tokens (List.ofFn (flatten edges))).length +
    2 ^ (paddedEdgeBits e) * (2 ^ t * 2 ^ t + 1) +
    (2 ^ t * 2 ^ t) + 2 ^ (paddedEdgeBits e) + 1

/-- The actual coordinate clock, with its finite-control push constants,
has one uniform cubic bound over every row and column. -/
theorem canonicalCoordClock_le_cellSize {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    canonicalCoordClock t d modulus edges i j ≤
      10000 * (canonicalCellSize t d edges + 1) ^ 3 *
        coordinateProgramCoefficient := by
  let b := paddedEdgeBits e
  let H := 2 ^ b
  let q := 2 ^ (t - 1)
  let K := 2 ^ t * 2 ^ t
  let R := rowCount v b t
  let C := columnCount b t d
  let body := tokens (List.ofFn (flatten edges))
  let B := canonicalCellSize t d edges
  let row := (rowIndex v b t).symm i
  let col := (columnIndex b t d).symm j
  let α := selector q H row.2 col.1
  let p := position (le_paddedEdgeCount e) edges col.2.1 row.1
  let S : Stack → List Bool :=
    fun k => (canonicalDecodedBank b t d modulus edges i j)
      (canonicalCoordPlace k)
  have hv : 0 < v := by
    by_contra h
    have hz : v = 0 := Nat.eq_zero_of_not_pos h
    have hi := i.isLt
    simp [rowCount, hz] at hi
  have hH : 0 < H := by dsimp [H]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hR : H ^ q ≤ R := by
    dsimp [R, rowCount]
    have h : 1 ≤ v := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (H ^ q) h
  have hvR : v ≤ R := by
    dsimp [R, rowCount]
    have h : 1 ≤ H ^ q := by
      have h' : 0 < H ^ q := pow_pos hH _
      omega
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left v h
  have hqC : q ≤ C := by
    dsimp [C, columnCount]
    have hdpos : 0 < (2 ^ d) ^ 2 := by positivity
    have h : 1 ≤ H * (2 ^ d) ^ 2 := by nlinarith
    simpa only [Nat.mul_one, mul_assoc] using Nat.mul_le_mul_left q h
  have hHC : H ≤ C := by
    dsimp [C, columnCount]
    have hdpos : 0 < (2 ^ d) ^ 2 := by positivity
    have h : 1 ≤ q * (2 ^ d) ^ 2 := by nlinarith
    calc
      H = 1 * H := by ring
      _ ≤ (q * (2 ^ d) ^ 2) * H := Nat.mul_le_mul_right H h
      _ = q * H * (2 ^ d) ^ 2 := by ring
  have hR_B : R ≤ B := by
    change R ≤ R + C + body.length + H * (K + 1) + K + H + 1
    omega
  have hC_B : C ≤ B := by
    change C ≤ R + C + body.length + H * (K + 1) + K + H + 1
    omega
  have hH_B : H ≤ B := by
    change H ≤ R + C + body.length + H * (K + 1) + K + H + 1
    omega
  have hK_B : K ≤ B := by
    change K ≤ R + C + body.length + H * (K + 1) + K + H + 1
    omega
  have hbody_B : body.length ≤ B := by
    change body.length ≤ R + C + body.length + H * (K + 1) + K + H + 1
    omega
  have hz_B : row.2.val ≤ B := by
    have h := row.2.isLt
    change row.2.val < H ^ q at h
    omega
  have hg_B : col.1.val ≤ B := by
    have h := col.1.isLt
    omega
  have ha_B : col.2.1.val ≤ B := by
    have h := col.2.1.isLt
    omega
  have hv_B : row.1.val ≤ B := by
    have h := row.1.isLt
    omega
  have hα_B : α.val ≤ B := by
    have h := α.isLt
    omega
  have hp_B : p.val ≤ B := by
    have h := p.isLt
    change p.val < K + 1 at h
    omega
  have hpow_B : H ^ col.1.val ≤ B := by
    have hmono : H ^ col.1.val ≤ H ^ q :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt col.1.isLt)
    omega
  have ht_B : t ≤ B := by
    have ht2 : t < 2 ^ t := Nat.lt_two_pow_self
    have h2K : 2 ^ t ≤ K := by
      dsimp [K]
      have h : 1 ≤ 2 ^ t := by
        have hp : 0 < 2 ^ t := by positivity
        omega
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ t) h
    omega
  have hinputs := canonicalDecoded_coord_inputs b t d modulus edges i j
  dsimp only at hinputs
  obtain ⟨hz0, hg0, hH0, ha0, hv0, hbody0, hK0, hblank⟩ := hinputs
  have hS : ∀ k : Fin 7, (S ⟨k.val, by omega⟩).length ≤ B := by
    intro k
    fin_cases k
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 0)).length ≤ B
      rw [hz0, List.length_replicate]
      exact hz_B
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 1)).length ≤ B
      rw [hg0, List.length_replicate]
      exact hg_B
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 2)).length ≤ B
      rw [hH0, List.length_replicate]
      exact hH_B
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 3)).length ≤ B
      rw [ha0, List.length_replicate]
      exact ha_B
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 4)).length ≤ B
      rw [hv0, List.length_replicate]
      exact hv_B
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 5)).length ≤ B
      rw [hbody0]
      exact hbody_B
    · change (canonicalDecodedBank b t d modulus edges i j
        (canonicalCoordPlace 6)).length ≤ B
      rw [hK0, List.length_replicate]
      exact hK_B
  have hblankS : ∀ k : Stack, 7 ≤ k.val → S k = [] := by
    intro k hk
    exact hblank k hk
  have hbound := coordinateStageClock_le B q H K row.2.val col.1.val
    t col.2.1.val row.1.val α.val p.val body S
    hS hblankS hH_B hK_B
    (by simpa [Paper2.YaoSourceCodec.arity, K] using hK_B)
    hz_B hg_B hpow_B ht_B ha_B hv_B hbody_B hα_B hp_B
  simpa only [canonicalCoordClock, coordinateStageClock,
    canonicalCellSize, B, b, H, q, K, R, C, body, row, col, α, p, S]
    using hbound

/-- The literal four-stage callback clock has a fixed quartic bound in
the size of its public bank. No maximum over entries remains in this bound. -/
theorem canonicalEntryClock_le_cellSize {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    canonicalEntryClock t d modulus edges i j ≤
      (10000 * coordinateProgramCoefficient + 1000) *
        (canonicalCellSize t d edges + 1) ^ 4 := by
  let b := paddedEdgeBits e
  let H := 2 ^ b
  let K := 2 ^ t * 2 ^ t
  let R := rowCount v b t
  let C := columnCount b t d
  let body := tokens (List.ofFn (flatten edges))
  let B := canonicalCellSize t d edges
  let P := coordinateProgramCoefficient
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hR : R ≤ B := by
    change R ≤ R + C + body.length + H * (K + 1) + K + H + 1
    have : 0 ≤ H * (K + 1) := Nat.zero_le _
    omega
  have hC : C ≤ B := by
    change C ≤ R + C + body.length + H * (K + 1) + K + H + 1
    have : 0 ≤ H * (K + 1) := Nat.zero_le _
    omega
  have hHn : H * (K + 1) ≤ B := by
    change H * (K + 1) ≤ R + C + body.length + H * (K + 1) + K + H + 1
    omega
  have hK : K ≤ B := by
    change K ≤ R + C + body.length + H * (K + 1) + K + H + 1
    have : 0 ≤ H * (K + 1) := Nat.zero_le _
    omega
  have hindex := canonical_index_clock_at_cell t d i j
  have hcoord := canonicalCoordClock_le_cellSize t d modulus edges i j
  have hclean := canonical_cleanup_time_bound t d modulus edges i j
  have hprod : (K + 1) * C ≤ (B + 1) ^ 2 := by
    have hk : K + 1 ≤ B + 1 := by omega
    have hc : C ≤ B + 1 := by omega
    simpa only [pow_two] using Nat.mul_le_mul hk hc
  have hlookup : canonicalLookupClock b t d ≤ 800 * (B + 1) ^ 4 := by
    have harg : 4 * (K + 1) * C + 1 ≤ 5 * (B + 1) ^ 2 := by
      have hsq : 1 ≤ (B + 1) ^ 2 := by
        simpa using Nat.pow_le_pow_left (show 1 ≤ B + 1 by omega) 2
      nlinarith
    calc
      canonicalLookupClock b t d = 32 * (4 * (K + 1) * C + 1) ^ 2 := rfl
      _ ≤ 32 * (5 * (B + 1) ^ 2) ^ 2 := by gcongr
      _ = 800 * (B + 1) ^ 4 := by ring
  have hB1 : B + 1 ≤ (B + 1) ^ 4 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 0 < B + 1 by omega) (show 1 ≤ 4 by omega))
  have hB3 : (B + 1) ^ 3 ≤ (B + 1) ^ 4 :=
    Nat.pow_le_pow_right (show 0 < B + 1 by omega) (by omega)
  have hindex' : canonicalIndexClock b t d i.val j.val ≤
      32 * (B + 1) ^ 4 := by
    calc
      _ ≤ 32 * (R + C + 1) := hindex
      _ ≤ 32 * (2 * B + 1) := by omega
      _ ≤ 32 * (B + 1) ^ 4 := by
        have hsq : 2 * B + 1 ≤ (B + 1) ^ 2 := by nlinarith
        have hp : (B + 1) ^ 2 ≤ (B + 1) ^ 4 :=
          Nat.pow_le_pow_right (show 0 < B + 1 by omega) (by omega)
        nlinarith
  have hcoord' : canonicalCoordClock t d modulus edges i j ≤
      10000 * P * (B + 1) ^ 4 := by
    calc
      _ ≤ 10000 * (B + 1) ^ 3 * P := hcoord
      _ ≤ 10000 * P * (B + 1) ^ 4 := by
        have h := Nat.mul_le_mul_left (10000 * P) hB3
        nlinarith
  have hclean' : canonicalCleanupTime
      (Function.update
        (canonicalCoordinateBank b t d modulus (le_paddedEdgeCount e) edges i j)
        (.inr 2)
        [numericEntry b t d modulus (le_paddedEdgeCount e) edges i j]) ≤
      20 * (B + 1) ^ 4 := by
    calc
      _ ≤ 2 * R + 3 * C + H * (K + 1) + 8 := hclean
      _ ≤ 6 * B + 8 := by omega
      _ ≤ 20 * (B + 1) ^ 4 := by nlinarith
  unfold canonicalEntryClock
  change canonicalIndexClock b t d i.val j.val +
      canonicalCoordClock t d modulus edges i j +
      canonicalLookupClock b t d +
      canonicalCleanupTime
        (Function.update
          (canonicalCoordinateBank b t d modulus (le_paddedEdgeCount e) edges i j)
          (.inr 2)
          [numericEntry b t d modulus (le_paddedEdgeCount e) edges i j]) + 3 ≤
      (10000 * P + 1000) * (B + 1) ^ 4
  nlinarith [hindex', hcoord', hlookup, hclean', hB1]

/-- This removes the noncomputable finite maximum from the writer clock:
every cell has the same public, fixed-degree bound. -/
theorem canonicalUniformEntryClock_le_cellSize {v e : ℕ}
    (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    canonicalUniformEntryClock t d modulus edges ≤
      (10000 * coordinateProgramCoefficient + 1000) *
        (canonicalCellSize t d edges + 1) ^ 4 := by
  apply canonical_uniform_clock_le_of_pointwise
  intro i j
  exact canonicalEntryClock_le_cellSize t d modulus edges i j

/-- The size parameter is exactly the combined lengths of the two unary
dimension cells and four particular literal prepared-bank cells, plus one.
Thus the degree bound is genuinely in the physical prepared configuration
length, not merely in an unrelated numerical surrogate. -/
theorem canonicalCellSize_eq_prepared_lengths {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    canonicalCellSize t d edges =
      (List.replicate (rowCount v (paddedEdgeBits e) t) true).length +
      (List.replicate (columnCount (paddedEdgeBits e) t d) true).length +
      (canonicalWriterBank (paddedEdgeBits e) t d modulus edges 3).length +
      (canonicalWriterBank (paddedEdgeBits e) t d modulus edges 6).length +
      (canonicalWriterBank (paddedEdgeBits e) t d modulus edges 4).length +
      (canonicalWriterBank (paddedEdgeBits e) t d modulus edges 2).length + 1 := by
  simp [canonicalCellSize, canonicalWriterBank, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

#print axioms canonicalCoordClock_le_cellSize
#print axioms canonicalEntryClock_le_cellSize
#print axioms canonicalUniformEntryClock_le_cellSize
#print axioms canonicalCellSize_eq_prepared_lengths

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
