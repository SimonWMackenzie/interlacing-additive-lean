import CurrentAdditive.GenericBitvectorPrep

/-! A single fixed TM2 program prepares the two level-zero code words and
reads a supplied base table in its explicit big-endian padded order. -/

namespace Paper2.GenericBitvectorPhysicalEntry

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def program := BitMachineRawSequence.program
  GenericBitvectorPrep.program GenericBitvectorPaddedLookup.program
  MatrixTableLookup.start GenericBitvectorPrep.initial MatrixTableLookup.initial

def start := BitMachineRawSequence.leftLabel
  (LB := MatrixTableLookup.Label) GenericBitvectorPrep.start
def initial := (GenericBitvectorPrep.initial, MatrixTableLookup.initial)

theorem entry_run (S : Fin 14 → List Bool) (row col : List Bool)
    (width : ℕ) (bits : List Bool)
    (h0 : S 0 = row) (h1 : S 1 = []) (h2 : S 2 = [])
    (h3 : S 3 = []) (h4 : S 4 = [])
    (h5 : S 5 = col) (h6 : S 6 = List.replicate width true)
    (h7 : S 7 = bits) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = [])
    (h12 : S 12 = []) (h13 : S 13 = []) :
    ∃ t ≤ 2 * row.length + 2 + MatrixBinaryAddress.workFrom 0 row + 1 +
        (2 * col.length + 2) + 1 +
        32 * (MatrixBinaryAddress.valueFrom 0 row + width + col.length +
          bits.length + 1) ^ 2 + 1,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      ⟨none, initial,
        Function.update
          (Function.update
            (Function.update S 1
              (List.replicate (MatrixBinaryAddress.valueFrom 0 row) true))
            8 (List.replicate col.length true))
          11 [bits[MatrixBinaryAddress.valueFrom 0 row * width + col.length]?.getD false]⟩ := by
  obtain ⟨tp, htp, hp⟩ := GenericBitvectorPrep.prep_run S row col
    h0 h1 h2 h3 h4 h5 h8 h9
  let P := Function.update (Function.update S 1
    (List.replicate (MatrixBinaryAddress.valueFrom 0 row) true)) 8
    (List.replicate col.length true)
  have hl := GenericBitvectorPaddedLookup.lookup_run P
    (MatrixBinaryAddress.valueFrom 0 row) width col.length bits
    (by simp [P]) (by simp [P, h6]) (by simp [P])
    (by simp [P, h7]) (by simp [P, h11])
    (by simp [P, h10]) (by simp [P, h12]) (by simp [P, h13])
    (by simp [P, h4]) (by simp [P, h3])
  obtain ⟨tl, htl, hrun⟩ := hl
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    GenericBitvectorPrep.program GenericBitvectorPaddedLookup.program
    GenericBitvectorPrep.start MatrixTableLookup.start
    GenericBitvectorPrep.initial GenericBitvectorPrep.initial
    MatrixTableLookup.initial MatrixTableLookup.initial
    S P _ tp tl hp hrun
  exact ⟨t, by omega, by simpa only [program, start, initial] using h⟩

theorem supplied_entry (p : ℕ)
    (F : (Fin p → Bool) → Fin p → Bool)
    (x : Fin p → Bool) (j : Fin p) :
    let row := List.ofFn x
    let col := (RecursiveLabelCodecScratch.finCodec p).encode j
    let bits := GenericBitvectorPaddedTable.paddedBits p F
    let S : Fin 14 → List Bool :=
      ![row, [], [], [], [], col, List.replicate (p + 1) true,
        bits, [], [], [], [], [], []]
    ∃ t ≤ 2 * row.length + 2 + MatrixBinaryAddress.workFrom 0 row + 1 +
        (2 * col.length + 2) + 1 +
        32 * (MatrixBinaryAddress.valueFrom 0 row + (p + 1) + col.length +
          bits.length + 1) ^ 2 + 1,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      ⟨none, initial,
        Function.update
          (Function.update
            (Function.update S 1
              (List.replicate (MatrixBinaryAddress.valueFrom 0 row) true))
            8 (List.replicate col.length true))
          11 [F x j]⟩ := by
  intro row col bits S
  obtain ⟨t, ht, h⟩ := entry_run S row col (p + 1) bits
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl)
  refine ⟨t, ht, ?_⟩
  simpa only [row, col, bits, GenericBitvectorPaddedTable.paddedBits_entry]
    using h

#print axioms entry_run
#print axioms supplied_entry

end Paper2.GenericBitvectorPhysicalEntry
