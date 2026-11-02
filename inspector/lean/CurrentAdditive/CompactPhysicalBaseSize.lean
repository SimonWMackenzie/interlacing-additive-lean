import CurrentAdditive.CompactPhysicalBaseLookup

/-! The actual physical base program receives three compact binary address
fields followed by the literal table.  Their prefix size is linear in the
logarithmic bound on the base dimensions. -/

namespace Paper2.CompactPhysicalBaseSize

open Paper2.CompactRationalPacket
open Paper2.CompactPhysicalBaseLookup
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing Turing.TM2.Stmt

def addressPrefix {rows cols : ℕ} (i : Fin rows) (j : Fin cols) : List Bool :=
  EncodedCommunication.field i.val.bits ++
    EncodedCommunication.field cols.bits ++
    EncodedCommunication.field j.val.bits

theorem input_split {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    input P i j = addressPrefix i j ++ P.table.bits := by
  simp [input, addressPrefix, EncodedCommunication.encodeInstance,
    EncodedCommunication.natField, List.append_assoc]

theorem addressPrefix_length {rows cols L : ℕ}
    (hr : rows ≤ 2 ^ L) (hc : cols ≤ 2 ^ L)
    (i : Fin rows) (j : Fin cols) :
    (addressPrefix i j).length ≤ 6 * (L + 1) + 3 := by
  have hir : i.val < 2 ^ L := lt_of_lt_of_le i.isLt hr
  have hjc : j.val < 2 ^ L := lt_of_lt_of_le j.isLt hc
  have hi : i.val.bits.length ≤ L := by
    simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr hir)
  have hj : j.val.bits.length ≤ L := by
    simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr hjc)
  have hnext : cols < 2 ^ (L + 1) := by
    have hpos : 0 < 2 ^ L := pow_pos (by omega) _
    rw [pow_succ]
    omega
  have hw : cols.bits.length ≤ L + 1 := by
    simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr hnext)
  simp only [addressPrefix, List.length_append,
    EncodedCommunication.field_length]
  omega

def physicalBound {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) : ℕ :=
  Paper2.ASquare.Post.parseBound i.val cols j.val +
    MatrixBinaryAddress.workFrom 0 j.val.bits.reverse +
    32 * (i.val + cols + j.val + P.table.bits.length + 1) ^ 2 + 2

theorem physicalBound_quadratic {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    physicalBound P i j ≤
      256 * (rows + cols + P.table.bits.length + 1) ^ 2 := by
  let S := rows + cols + P.table.bits.length + 1
  let A := i.val + cols + j.val + P.table.bits.length + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hA : A ≤ 2 * S := by dsimp [A, S]; omega
  have hAsq : A ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left hA 2
  have hbi : i.val.bits.length ≤ i.val := by
    simpa only [Nat.size_eq_bits_len] using
      (Nat.size_le.mpr (Nat.lt_two_pow_self : i.val < 2 ^ i.val))
  have hbc : cols.bits.length ≤ cols := by
    simpa only [Nat.size_eq_bits_len] using
      (Nat.size_le.mpr (Nat.lt_two_pow_self : cols < 2 ^ cols))
  have hbj : j.val.bits.length ≤ j.val := by
    simpa only [Nat.size_eq_bits_len] using
      (Nat.size_le.mpr (Nat.lt_two_pow_self : j.val < 2 ^ j.val))
  have hw := Paper2.ASquare.Post.workFrom_le j.val
  have hlinear :
      Paper2.ASquare.Post.parseBound i.val cols j.val +
        MatrixBinaryAddress.workFrom 0 j.val.bits.reverse + 2 ≤ 40 * S := by
    unfold Paper2.ASquare.Post.parseBound
    dsimp [S]
    omega
  have hclock : physicalBound P i j ≤ 40 * S + 32 * A ^ 2 := by
    dsimp [physicalBound, A]
    omega
  have hquad : 32 * A ^ 2 ≤ 128 * S ^ 2 := by
    nlinarith [hAsq]
  have hSsq : S ≤ S ^ 2 := by nlinarith
  calc
    physicalBound P i j ≤ 40 * S + 32 * A ^ 2 := hclock
    _ ≤ 40 * S + 128 * S ^ 2 := Nat.add_le_add_left hquad _
    _ ≤ 256 * S ^ 2 := by nlinarith

theorem physicalBound_exponential {rows cols L : ℕ}
    (P : Packet rows cols) (hr : rows ≤ 2 ^ L)
    (hc : cols ≤ 2 ^ L) (i : Fin rows) (j : Fin cols) :
    physicalBound P i j ≤ 2 ^ (4 * L + 12) := by
  let M := 2 ^ L
  let S := rows + cols + P.table.bits.length + 1
  have hM : 1 ≤ M := by
    dsimp [M]
    have hh : 0 < (2 : ℕ) ^ L := pow_pos (by norm_num) _
    omega
  have hrM : rows ≤ M := hr
  have hcM : cols ≤ M := hc
  have hMsq : M ≤ M ^ 2 := by nlinarith
  have hone : 1 ≤ M ^ 2 := by nlinarith
  have hproduct : rows * cols ≤ M ^ 2 := by
    dsimp [M] at *
    nlinarith [Nat.mul_le_mul hr hc]
  have hS : S ≤ 4 * M ^ 2 := by
    dsimp [S]
    rw [P.table.length]
    omega
  have hSsquare : S ^ 2 ≤ (4 * M ^ 2) ^ 2 := Nat.pow_le_pow_left hS 2
  calc
    physicalBound P i j ≤ 256 * S ^ 2 := physicalBound_quadratic P i j
    _ ≤ 256 * (4 * M ^ 2) ^ 2 := Nat.mul_le_mul_left 256 hSsquare
    _ = 2 ^ (4 * L + 12) := by
      dsimp [M]
      rw [pow_add]
      have he : (2 ^ L) ^ 4 = 2 ^ (4 * L) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [← he]
      norm_num
      ring

theorem lookup_run_exponential {rows cols L : ℕ}
    (P : Packet rows cols) (hr : rows ≤ 2 ^ L)
    (hc : cols ≤ 2 ^ L) (i : Fin rows) (j : Fin cols) :
    ∃ t ≤ 2 ^ (4 * L + 12),
      ((advance program)^[t])
        ⟨some start, initial,
          Paper2.ASquare.Post.pbank [] [] (input P i j)
            Paper2.ASquare.Post.ext0⟩ =
      ⟨none, (Paper2.ASquare.Post.pinit,
          ((false, false), MatrixTableLookup.initial)),
        Paper2.ASquare.Post.pbank
          (List.replicate i.val true) (List.replicate cols true)
          P.table.bits
          (Paper2.ASquare.Post.ext (List.replicate j.val true) [] []
            [P.table.matrix i j] [] [] [] [])⟩ := by
  obtain ⟨t, ht, h⟩ := lookup_run P i j
  exact ⟨t, ht.trans (physicalBound_exponential P hr hc i j), h⟩

#print axioms input_split
#print axioms addressPrefix_length
#print axioms physicalBound_quadratic
#print axioms physicalBound_exponential
#print axioms lookup_run_exponential

end Paper2.CompactPhysicalBaseSize
