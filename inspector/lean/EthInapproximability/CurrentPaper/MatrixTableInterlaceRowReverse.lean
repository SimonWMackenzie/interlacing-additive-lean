import EthInapproximability.CurrentPaper.MatrixTableInterlaceNumbering
import EthInapproximability.CurrentPaper.MatrixTableTranspose
import EthInapproximability.CurrentPaper.SamplerMachineBlockReverse

/-!
# Physical reversal of interlace row blocks

Frozen v8 `def:paper-interlace` and `eq:one-level-exact-carriers`.
The paper's tuple numbering is the reverse of the numerical digit order used
by the literal interlace writer.  The following fixed Boolean-stack program
reverses the order of complete row blocks while retaining the order of all
bits inside each block.  Its final state is the checkpoint just before the
sampler reversal program's optional bitwise finishing pass.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceRowReverse

open MatrixMaterialization MatrixTableInterlaceCodes

def blocksOf (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool) : List (List Bool) :=
  List.ofFn fun i : Fin blocks =>
    List.ofFn fun z : Fin (rows*cols) =>
      f (rowCode blocks rows (i,(finProdFinEquiv.symm z).1))
        (finProdFinEquiv.symm z).2

theorem blocksOf_length (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool) :
    (blocksOf blocks rows cols f).length = blocks := by
  simp [blocksOf]

theorem blocksOf_width (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (b : List Bool) (hb : b ∈ blocksOf blocks rows cols f) :
    b.length = rows*cols := by
  simp only [blocksOf, List.mem_ofFn] at hb
  obtain ⟨i,rfl⟩ := hb
  simp

private theorem split_cell (blocks rows cols : ℕ)
    (i : Fin blocks) (z : Fin (rows*cols)) :
    (finProdFinEquiv.symm
      (Fin.cast (Nat.mul_assoc blocks rows cols).symm
        (finProdFinEquiv (i,z)))).1 =
      rowCode blocks rows (i,(finProdFinEquiv.symm z).1) ∧
    (finProdFinEquiv.symm
      (Fin.cast (Nat.mul_assoc blocks rows cols).symm
        (finProdFinEquiv (i,z)))).2 =
      (finProdFinEquiv.symm z).2 := by
  have hc : 0 < cols := by
    by_contra h
    have hz : cols = 0 := by omega
    have hz' : z.val < 0 := by simpa [hz] using z.isLt
    omega
  constructor
  · apply Fin.ext
    dsimp [MatrixTableInterlaceCodes.rowCode, finProdFinEquiv, Fin.divNat]
    calc
      (z.val + (rows*cols)*i.val)/cols =
          (z.val + cols*(rows*i.val))/cols := by congr 1; ring
      _ = z.val/cols + rows*i.val := Nat.add_mul_div_left _ _ hc
  · apply Fin.ext
    dsimp [MatrixTableInterlaceCodes.rowCode, finProdFinEquiv, Fin.modNat]
    calc
      (z.val + (rows*cols)*i.val)%cols =
          (z.val + cols*(rows*i.val))%cols := by congr 1; ring
      _ = z.val%cols := Nat.add_mul_mod_self_left _ _ _

private def blockCellIndex {blocks rows cols : ℕ}
    (i : Fin blocks) (z : Fin (rows*cols)) : Fin (blocks*(rows*cols)) :=
  ⟨i.val*(rows*cols)+z.val, by
    have h := (finProdFinEquiv (i,z)).isLt
    simpa [finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm] using h⟩

private theorem blockCellIndex_eq {blocks rows cols : ℕ}
    (i : Fin blocks) (z : Fin (rows*cols)) :
    blockCellIndex i z = finProdFinEquiv (i,z) := by
  apply Fin.ext
  simp [blockCellIndex, finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm]

theorem blocksOf_flatten (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool) :
    (blocksOf blocks rows cols f).flatten = rowMajor f := by
  unfold blocksOf rowMajor
  conv_rhs => rw [List.ofFn_congr (Nat.mul_assoc blocks rows cols), List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext z
  change f (rowCode blocks rows (i,(finProdFinEquiv.symm z).1))
      (finProdFinEquiv.symm z).2 =
    f (finProdFinEquiv.symm
      (Fin.cast (Nat.mul_assoc blocks rows cols).symm (blockCellIndex i z))).1
      (finProdFinEquiv.symm
      (Fin.cast (Nat.mul_assoc blocks rows cols).symm (blockCellIndex i z))).2
  rw [blockCellIndex_eq]
  have hs := split_cell blocks rows cols i z
  rcases hs with ⟨hr,hc⟩
  rw [hr,hc]

private theorem reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun i : Fin n => f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega

theorem blocksOf_reverse_flatten (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool) :
    (blocksOf blocks rows cols f).reverse.flatten =
      rowMajor (fun r c => f (MatrixTableInterlaceNumbering.reverseBlockRow
        blocks rows r) c) := by
  unfold blocksOf
  rw [reverse_ofFn]
  unfold rowMajor
  conv_rhs => rw [List.ofFn_congr (Nat.mul_assoc blocks rows cols), List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext z
  change f (rowCode blocks rows (i.rev,(finProdFinEquiv.symm z).1))
      (finProdFinEquiv.symm z).2 =
    f (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows
      (finProdFinEquiv.symm
      (Fin.cast (Nat.mul_assoc blocks rows cols).symm (blockCellIndex i z))).1)
      (finProdFinEquiv.symm
      (Fin.cast (Nat.mul_assoc blocks rows cols).symm (blockCellIndex i z))).2
  rw [blockCellIndex_eq]
  have hs := split_cell blocks rows cols i z
  rcases hs with ⟨hr,hc⟩
  rw [hr,hc]
  unfold MatrixTableInterlaceNumbering.reverseBlockRow
  simp

/-- A physical run of the fixed sampler controller reaches the exact
block-reversed word in stack 4.  A zero-width table is already empty and
requires no permutation run. -/
theorem rowBlock_run (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (hwidth : 0 < rows*cols) :
    SamplerMachineBlockReverse.run
      (blocks * SamplerMachineBlockReverse.blockStep (rows*cols))
      (SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial (rowMajor f)
        (List.replicate (rows*cols) true) [] [] [] []) =
      SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial []
        (List.replicate (rows*cols) true) [] []
        (rowMajor (fun r c => f
          (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c)) [] := by
  have h := SamplerMachineBlockReverse.blocks_run (rows*cols) hwidth
    (blocksOf blocks rows cols f) (blocksOf_width blocks rows cols f) [] []
  simp only [List.append_nil, blocksOf_length, blocksOf_flatten,
    blocksOf_reverse_flatten] at h
  exact h

theorem zero_width (blocks rows cols : ℕ)
    (f : Fin (blocks*rows) → Fin cols → Bool)
    (hwidth : rows*cols = 0) :
    rowMajor f = [] ∧
      rowMajor (fun r c => f
        (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c) = [] := by
  have hn : blocks*rows*cols = 0 := by
    rcases Nat.mul_eq_zero.mp hwidth with hr | hc
    · simp [hr]
    · simp [hc]
  constructor <;> apply List.length_eq_zero_iff.mp <;>
    simp [rowMajor_length, hn]

/-- The checkpoint time is linear in the literal table length and the number
of blocks, hence polynomial in the fully written output scale. -/
theorem rowBlock_bound_polynomial (blocks rows cols : ℕ) :
    blocks * SamplerMachineBlockReverse.blockStep (rows*cols) ≤
      5*(blocks+rows+cols+blocks*rows*cols+1)^2 := by
  let n := blocks+rows+cols+blocks*rows*cols+1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hb : blocks ≤ n := by dsimp [n]; omega
  have hl : blocks*(rows*cols) ≤ n := by dsimp [n]; nlinarith
  have hnn : n ≤ n^2 := by nlinarith [Nat.mul_le_mul (le_refl n) hn]
  change blocks*(2*(rows*cols)+3) ≤ 5*n^2
  calc
    blocks*(2*(rows*cols)+3) = 2*(blocks*(rows*cols))+3*blocks := by ring
    _ ≤ 5*n := by omega
    _ ≤ 5*n^2 := by omega

def numberedInterlace (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    Fin (blocks*rows) → Fin (cols^blocks) → Bool :=
  fun r c => Workspace.Types.Interlace.interlaceFun f blocks
    (((Iteration.Numbering.fin blocks).prod
      (Iteration.Numbering.fin rows)).equiv r)
    (((Iteration.Numbering.fin cols).tuple blocks).equiv c)

theorem numberedInterlace_eq (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    numberedInterlace blocks rows cols f =
      fun r c => MatrixTableInterlace.interlaced (blocks := blocks) f
        (MatrixTableInterlaceNumbering.reverseBlockRow blocks rows r) c := by
  funext r c
  exact MatrixTableInterlaceNumbering.numbered_interlace blocks rows cols f r c

/-- The physical checkpoint following the literal interlace writer has
exactly the paper-numbered interlace bit word. -/
theorem numberedInterlace_run (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    SamplerMachineBlockReverse.run
      (blocks * SamplerMachineBlockReverse.blockStep (rows*(cols^blocks)))
      (SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial
        (rowMajor (MatrixTableInterlace.interlaced (blocks := blocks) f))
        (List.replicate (rows*(cols^blocks)) true) [] [] [] []) =
      SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial []
        (List.replicate (rows*(cols^blocks)) true) [] []
        (rowMajor (numberedInterlace blocks rows cols f)) [] := by
  rw [numberedInterlace_eq]
  exact rowBlock_run blocks rows (cols^blocks)
    (MatrixTableInterlace.interlaced (blocks := blocks) f) hwidth

def numberedRestoration (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    Fin (cols^(2^r)) → Fin ((2^r)*rows) → Bool :=
  fun c row => Restoration.output f r
    (((Iteration.Numbering.fin cols).tuple (2^r)).equiv c)
    (((Iteration.Numbering.fin (2^r)).prod
      (Iteration.Numbering.fin rows)).equiv row)

theorem numberedRestoration_eq (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    numberedRestoration r rows cols f =
      fun c row => numberedInterlace (2^r) rows cols f row c := by
  funext c row
  rw [numberedInterlace_eq]
  exact MatrixTableInterlaceNumbering.restoration_numeric f
    (Iteration.Numbering.fin rows) (Iteration.Numbering.fin cols) r c row

/-- The reviewed physical transpose writer consumes the exact checkpoint
word and emits the numeric `Restoration.output` table, in the paper's tuple
numbering.  This is a prepared-bank invocation; the transfer from the
checkpoint into that bank is not hidden in this theorem. -/
theorem numberedRestoration_transpose (r rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (cols^(2^r)) ((2^r)*rows)
      (MatrixTableTranspose.callbackBound ((2^r)*rows) (cols^(2^r))
        (rowMajor (numberedInterlace (2^r) rows cols f)).length),
      ∃ v,
        MatrixTableWriter.run MatrixTableTranspose.entryProgram
          MatrixTableLookup.start MatrixTableLookup.initial t
          (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
            (MatrixTableLookup.initial,none)
            (MatrixTableWriter.ready
              (MatrixTableTranspose.persistentBank (cols^(2^r))
                (rowMajor (numberedInterlace (2^r) rows cols f)))
              (cols^(2^r)) ((2^r)*rows) 0 0 0 0 [] output)) =
        MatrixTableWriter.cfg none v
          (MatrixTableWriter.ready
            (MatrixTableTranspose.persistentBank (cols^(2^r))
              (rowMajor (numberedInterlace (2^r) rows cols f)))
            (cols^(2^r)) ((2^r)*rows) 0 0 0 0 []
            (rowMajor (numberedRestoration r rows cols f) ++ output)) := by
  obtain ⟨t,ht,v,he⟩ := MatrixTableTranspose.transpose_rowMajor
    ((2^r)*rows) (cols^(2^r))
    (numberedInterlace (2^r) rows cols f) output
  refine ⟨t,ht,v,?_⟩
  simpa only [numberedRestoration_eq] using he

theorem numberedInterlace_zero_width (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : rows*(cols^blocks) = 0) :
    rowMajor (MatrixTableInterlace.interlaced (blocks := blocks) f) = [] ∧
      rowMajor (numberedInterlace blocks rows cols f) = [] := by
  simpa only [numberedInterlace_eq] using
    zero_width blocks rows (cols^blocks)
      (MatrixTableInterlace.interlaced (blocks := blocks) f) hwidth

end EthInapproximability.CurrentPaper.MatrixTableInterlaceRowReverse
