import CurrentAdditive.V38PrinterBoundary

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoLookup Paper2.YaoIndexDecoder
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldCoordinate

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

noncomputable def canonicalEntryClockOn {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (ij : Fin (rowCount v (paddedEdgeBits e) t) ×
      Fin (columnCount (paddedEdgeBits e) t d)) : ℕ :=
  canonicalEntryClock t d modulus edges ij.1 ij.2

/-- A uniform finite maximum of the explicit per-entry transition count.
Polynomial domination of this maximum is a separate arithmetic theorem. -/
noncomputable def canonicalUniformEntryClock {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) : ℕ :=
  (Finset.univ : Finset
    (Fin (rowCount v (paddedEdgeBits e) t) ×
      Fin (columnCount (paddedEdgeBits e) t d))).sup
    (canonicalEntryClockOn t d modulus edges)

theorem canonicalEntryClock_le_uniform {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    canonicalEntryClockOn t d modulus edges (i, j) ≤
      canonicalUniformEntryClock t d modulus edges := by
  unfold canonicalUniformEntryClock
  exact Finset.le_sup (s := Finset.univ)
    (f := canonicalEntryClockOn t d modulus edges)
    (Finset.mem_univ (i, j))

/-- The concrete callback satisfies the generic writer's full local-run
contract for every valid row and column, including empty dimensions. -/
theorem canonical_entry_runs {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    MatrixTableWriter.EntryRuns canonicalEntryProgram
      (BitMachineRawSequence.leftLabel startLabel)
      (startControl, (payloadControl,
        (MatrixTableLookup.initial, ((), (none : Option Bool)))))
      (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
      (rowCount v (paddedEdgeBits e) t)
      (columnCount (paddedEdgeBits e) t d)
      (canonicalUniformEntryClock t d modulus edges)
      (natEntry (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges) := by
  intro x hx y hy
  let i : Fin (rowCount v (paddedEdgeBits e) t) := ⟨x, hx⟩
  let j : Fin (columnCount (paddedEdgeBits e) t d) := ⟨y, hy⟩
  obtain ⟨steps, ht, hr⟩ := canonical_writer_entry_run t d modulus edges i j
  have hvalue : numericEntry (paddedEdgeBits e) t d modulus
      (le_paddedEdgeCount e) edges i j =
      natEntry (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges x y := by
    calc
      _ = entry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j :=
        (entry_eq_numericEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j).symm
      _ = natEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges x y :=
        (natEntry_fin (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j).symm
  have huniform : canonicalEntryClock t d modulus edges i j ≤
      canonicalUniformEntryClock t d modulus edges := by
    simpa only [canonicalEntryClockOn] using
      canonicalEntryClock_le_uniform t d modulus edges i j
  refine ⟨steps, ht.trans huniform,
    (startControl, (payloadControl,
      (MatrixTableLookup.initial, ((), (none : Option Bool))))), ?_⟩
  have hbank : Function.update
      (canonicalReady (paddedEdgeBits e) t d modulus edges x y)
      (.inr 2) [natEntry (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges x y] =
      Sum.elim (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
        (![List.replicate x true, List.replicate y true,
          [natEntry (paddedEdgeBits e) t d modulus
            (le_paddedEdgeCount e) edges x y]] : Fin 3 → List Bool) := by
    funext k
    rcases k with k | k
    · rfl
    · fin_cases k <;> rfl
  rw [hvalue, hbank] at hr
  simpa only [MatrixTableWriter.cellCfg, canonicalReady, i, j] using hr

/-- The generic physical row-major writer, instantiated with the concrete
four-stage entry callback, emits exactly the computable canonical table bits. -/
theorem canonical_writer_table_run {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (output : List Bool) :
    ∃ steps ≤ MatrixTableWriter.writerBound
        (rowCount v (paddedEdgeBits e) t)
        (columnCount (paddedEdgeBits e) t d)
        (canonicalUniformEntryClock t d modulus edges),
      ∃ control,
        MatrixTableWriter.run canonicalEntryProgram
          (BitMachineRawSequence.leftLabel startLabel)
          (startControl, (payloadControl,
            (MatrixTableLookup.initial, ((), (none : Option Bool))))) steps
          (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
            ((startControl, (payloadControl,
              (MatrixTableLookup.initial, ((), (none : Option Bool))))), none)
            (MatrixTableWriter.ready
              (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
              (rowCount v (paddedEdgeBits e) t)
              (columnCount (paddedEdgeBits e) t d)
              0 0 0 0 [] output)) =
          MatrixTableWriter.cfg none control
            (MatrixTableWriter.ready
              (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
              (rowCount v (paddedEdgeBits e) t)
              (columnCount (paddedEdgeBits e) t d)
              0 0 0 0 []
              ((table (paddedEdgeBits e) t d modulus
                (le_paddedEdgeCount e) edges).bits ++ output)) := by
  have hcell := canonical_entry_runs t d modulus edges
  obtain ⟨steps, hsteps, control, hr⟩ := MatrixTableWriter.write_table
    canonicalEntryProgram
    (BitMachineRawSequence.leftLabel startLabel)
    (startControl, (payloadControl,
      (MatrixTableLookup.initial, ((), (none : Option Bool)))))
    (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
    (rowCount v (paddedEdgeBits e) t)
    (columnCount (paddedEdgeBits e) t d)
    (canonicalUniformEntryClock t d modulus edges)
    (natEntry (paddedEdgeBits e) t d modulus
      (le_paddedEdgeCount e) edges) hcell output
  refine ⟨steps, hsteps, control, ?_⟩
  simpa only [tableWord_eq_canonical_bits] using hr

#print axioms canonical_entry_runs
#print axioms canonical_writer_table_run

end CurrentAdditive.V38TablePrinter
