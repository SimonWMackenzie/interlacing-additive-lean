import Paper2.YaoOneEntry
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-! Unit 5 segment Y7 (lane a-yao-owner-2): the `EntryRuns` instance for the
Yao table and the admitted row-major writer.

Consumer: Y9.  The writer's foreign bank is `Fin K`, `K = Fintype.card (Static t lambda)`,
`Static t lambda = InputStack t lambda ⊕ Fin 20` (R-Y6: the controller region and the twenty
static/scratch cells of the callback).  The callback cells are placed by `writerPlace`:
`x, y, answer` go to the writer's own cells `inr 0, 1, 2`; everything else to the bank
through `Fintype.equivFin`.  The static bank `yaoBank` holds the raw tape (controller region),
the prelude outputs `sel, pay, pow, K, e` and the body stream; every other cell is empty.

`yao_entry_runs` is `MatrixTableWriter.EntryRuns` for the fixed program `entryProgram`
with the uniform `T = entryClock … r c`; `yao_write_rowMajor` applies the admitted
`write_rowMajor` and identifies the printed list with `(materialize …).bits`. -/

noncomputable section

namespace Paper2.YaoEntryRuns

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoEntryControllerJoin
open Paper2.YaoCtrlBlock
open Paper2.YaoMaterialization
open Paper2.UnaryFieldListParserScratch
open Paper2.YaoSourceCodec
open Paper2.YaoOneEntry

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

abbrev Static (t lambda : ℕ) := InputStack t lambda ⊕ Fin 20
abbrev WK (t lambda : ℕ) : ℕ := Fintype.card (Static t lambda)

/-- Placement of the callback cells in the writer's stacks. -/
def writerFun (t lambda : ℕ) :
    InputStack t lambda ⊕ Fin 23 → MatrixTableWriter.CellStack (WK t lambda)
  | .inl k => .inl (Fintype.equivFin (Static t lambda) (.inl k))
  | .inr i => if h : i.val < 3 then .inr ⟨i.val, h⟩ else
      .inl (Fintype.equivFin (Static t lambda) (.inr ⟨i.val - 3, by omega⟩))

theorem writerFun_injective (t lambda : ℕ) : Function.Injective (writerFun t lambda) := by
  intro a b h
  rcases a with k | i <;> rcases b with k' | j <;> simp only [writerFun] at h
  all_goals ((try split_ifs at h) <;>
    simp_all [(Fintype.equivFin (Static t lambda)).injective.eq_iff, Fin.ext_iff] <;> omega)

def writerPlace (t lambda : ℕ) :
    InputStack t lambda ⊕ Fin 23 ↪ MatrixTableWriter.CellStack (WK t lambda) :=
  ⟨writerFun t lambda, writerFun_injective t lambda⟩

/-- The static contents of the writer's foreign bank. -/
def staticVal {v e : ℕ} (t lambda : ℕ) (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) : Static t lambda → List Bool
  | .inl k => tapeOnly bits.val k
  | .inr j => if h : j.val < 6 then
      (![List.replicate (selectorCount t (paddedEdgeBits e) lambda) true,
        List.replicate (payloadCount t (paddedEdgeBits e) lambda) true,
        List.replicate (paddedEdgeCount e) true, List.replicate (arity t) true,
        List.replicate e true, tokens (List.ofFn (flatten edges))] : Fin 6 → List Bool)
        ⟨j.val, h⟩
      else []

/-- The writer's foreign bank for the Yao table. -/
def yaoBank {v e : ℕ} (t lambda : ℕ) (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) : Fin (WK t lambda) → List Bool :=
  fun n => staticVal t lambda edges bits ((Fintype.equivFin (Static t lambda)).symm n)

/-- The printed entry function. -/
def yaoEntry {v e : ℕ} (t lambda : ℕ) (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) (x y : ℕ) : Bool :=
  if h : x < rowCount v t (paddedEdgeBits e) lambda ∧ y < columnCount t (paddedEdgeBits e) lambda
  then (materialize t lambda edges bits).matrix ⟨x, h.1⟩ ⟨y, h.2⟩ else false

/-- The uniform per-entry clock. -/
def yaoT {v e : ℕ} (t lambda : ℕ) (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) : ℕ :=
  entryClock t lambda e (tokens (List.ofFn (flatten edges))).length
    (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)

theorem bank_static {v e : ℕ} (t lambda : ℕ) (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) (s : Static t lambda) :
    yaoBank t lambda edges bits (Fintype.equivFin (Static t lambda) s) =
      staticVal t lambda edges bits s := by
  simp [yaoBank]

/-- Y7: the `EntryRuns` instance for the Yao table. -/
theorem yao_entry_runs {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) :
    MatrixTableWriter.EntryRuns (entryProgram (writerPlace t lambda))
      (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
      (entryControl t lambda) (yaoBank t lambda edges bits)
      (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
      (yaoT t lambda edges) (yaoEntry t lambda edges bits) := by
  classical
  intro x hx y hy
  set B : MatrixTableWriter.CellStack (WK t lambda) → List Bool :=
    Sum.elim (yaoBank t lambda edges bits)
      (![List.replicate x true, List.replicate y true, []] : Fin 3 → List Bool) with hB
  have hbs := bank_static t lambda edges bits
  obtain ⟨n, hn, c', hr⟩ := physical_one_entry t lambda edges bits (writerPlace t lambda) B x y
    hx hy (by simp [hB, writerPlace, writerFun]) (by simp [hB, writerPlace, writerFun])
    (by simp [hB, writerPlace, writerFun])
    (by simp [hB, writerPlace, writerFun, hbs, staticVal])
    (by simp [hB, writerPlace, writerFun, hbs, staticVal])
    (by simp [hB, writerPlace, writerFun, hbs, staticVal])
    (by simp [hB, writerPlace, writerFun, hbs, staticVal])
    (by simp [hB, writerPlace, writerFun, hbs, staticVal])
    (by simp [hB, writerPlace, writerFun, hbs, staticVal])
    (by
      intro i hi
      have h3 : ¬ i.val < 3 := by omega
      have h6 : ¬ i.val - 3 < 6 := by omega
      simp [hB, writerPlace, writerFun, h3, hbs, staticVal, h6])
    (by intro k; simp [hB, writerPlace, writerFun, hbs, staticVal])
  refine ⟨n, hn.trans (entryClock_mono _ _ _ _ hx.le hy.le), c', ?_⟩
  refine hr.trans ?_
  unfold MatrixTableWriter.cellCfg
  congr 1
  have hent : yaoEntry t lambda edges bits x y =
      (materialize t lambda edges bits).matrix ⟨x, hx⟩ ⟨y, hy⟩ := by
    simp [yaoEntry, hx, hy]
  rw [hent]
  funext j
  rcases j with n' | i
  · simp [hB, writerPlace, writerFun]
  · fin_cases i <;> simp [hB, writerPlace, writerFun]

/-- The printed list is the admitted materialized list. -/
theorem rowMajor_materialize {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) :
    MatrixMaterialization.rowMajor (materialize t lambda edges bits).matrix =
      (materialize t lambda edges bits).bits := by
  rw [materialize_matrix]
  rfl

/-- Y7: the admitted row-major writer prints exactly `(materialize …).bits`. -/
theorem yao_write_rowMajor {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) (output : List Bool) :
    ∃ n ≤ MatrixTableWriter.writerBound (rowCount v t (paddedEdgeBits e) lambda)
        (columnCount t (paddedEdgeBits e) lambda) (yaoT t lambda edges), ∃ w,
      MatrixTableWriter.run (entryProgram (writerPlace t lambda))
        (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
        (entryControl t lambda) n
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (entryControl t lambda, none)
          (MatrixTableWriter.ready (yaoBank t lambda edges bits)
            (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
            0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none w
        (MatrixTableWriter.ready (yaoBank t lambda edges bits)
          (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
          0 0 0 0 [] ((materialize t lambda edges bits).bits ++ output)) := by
  have h := MatrixTableWriter.write_rowMajor (entryProgram (writerPlace t lambda))
    (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
    (entryControl t lambda) (yaoBank t lambda edges bits)
    (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
    (yaoT t lambda edges) (yaoEntry t lambda edges bits)
    (materialize t lambda edges bits).matrix
    (by intro X Y; simp [yaoEntry, X.isLt, Y.isLt])
    (yao_entry_runs t lambda edges bits) output
  rwa [rowMajor_materialize] at h

#print axioms writerFun_injective
#print axioms yao_entry_runs
#print axioms rowMajor_materialize
#print axioms yao_write_rowMajor

end Paper2.YaoEntryRuns

end
