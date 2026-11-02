import CurrentAdditive.CanonicalAmbientWriterHeaderFull
import CurrentAdditive.V38PrinterHeader

/-! One fixed nine-job physical copy program prepares all seven static writer
cells and its two dimension cells from public ambient source words. -/

noncomputable section

namespace CurrentAdditive.V38TablePrinter.Ambient

open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff
open Paper2.YaoMachine
open Paper2.YaoLookup Paper2.YaoSourceCodec Paper2.UnaryFieldListParserScratch
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

def writerJobs (t N : ℕ) : List (Cell t N × List (Cell t N)) :=
  [(.selector 1, [.writer (.inl (.inl 0))]),
   (.square 3, [.writer (.inl (.inl 1))]),
   (.source (sN 6), [.writer (.inl (.inl 2))]),
   (.source (sN 1), [.writer (.inl (.inl 3))]),
   (.source (sN 9), [.writer (.inl (.inl 4))]),
   (.field (printerSlots CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output),
      [.writer (.inl (.inl 5))]),
   (.width 3, [.writer (.inl (.inl 6))]),
   (.dimensions 5, [.writer (.inr .rows)]),
   (.dimensions 7, [.writer (.inr .cols)])]

def writerPrepProgram (t N : ℕ) :=
  MultiMove.program ((writerJobs t N).map CopyFill.toJob) (.copyScratch 0)

theorem writerJobs_good (t N : ℕ) :
    CopyFill.Good (.copyScratch 0) (writerJobs t N) := by
  constructor
  · intro j hj i hi
    simp [writerJobs] at hj hi
    rcases hj with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
      rcases hi with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp
  · simp [writerJobs]
  · intro j hj
    simp [writerJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp
  · intro j hj
    simp [writerJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp

theorem physical_writer_prep_jobs (t N : ℕ) (S : Cell t N → List Bool)
    (hscratch : S (.copyScratch 0) = [])
    (hblank : ∀ j ∈ writerJobs t N, ∀ d ∈ j.2, S d = []) :
    ((advance (writerPrepProgram t N))^[CopyFill.fillCost (writerJobs t N) S + 1])
      (⟨some (MultiMove.startLabel ((writerJobs t N).map CopyFill.toJob)),
        MultiMove.initial, S⟩ :
          TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, MultiMove.initial, CopyFill.fill (writerJobs t N) S⟩ := by
  exact CopyFill.run (.copyScratch 0) (writerJobs t N) (writerJobs_good t N)
    S hscratch hblank

theorem writerPrep_ready {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hwriter : ∀ k : MatrixTableWriter.Stack 60, S (.writer k) = [])
    (hcap : S (.selector 1) =
      List.replicate ((2 ^ (paddedEdgeBits e)) ^ (2 ^ (t - 1))) true)
    (hR2 : S (.square 3) = List.replicate ((2 ^ d) ^ 2) true)
    (hH : S (.source (sN 6)) = List.replicate (2 ^ (paddedEdgeBits e)) true)
    (hbody : S (.source (sN 1)) = tokens (List.ofFn (flatten edges)))
    (hK : S (.source (sN 9)) = List.replicate (2 ^ t * 2 ^ t) true)
    (hfield : S (.field (printerSlots
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
        bankBits (paddedEdgeBits e) t d modulus)
    (hn : S (.width 3) =
      List.replicate (2 ^ (paddedEdgeBits e) * (2 ^ t * 2 ^ t + 1)) true)
    (hrows : S (.dimensions 5) =
      List.replicate (rowCount v (paddedEdgeBits e) t) true)
    (hcols : S (.dimensions 7) =
      List.replicate (columnCount (paddedEdgeBits e) t d) true) :
    ∀ k : MatrixTableWriter.Stack 60,
      CopyFill.fill (writerJobs t N) S (.writer k) =
        (MatrixTableWriter.ready
          (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
          (rowCount v (paddedEdgeBits e) t)
          (columnCount (paddedEdgeBits e) t d)
          0 0 0 0 [] []).contents k := by
  intro k
  rcases k with k | z
  · rcases k with i | j
    · fin_cases i <;>
        simp [CopyFill.fill, writerJobs, canonicalWriterBank,
          MatrixTableWriter.ready,
          MatrixTableWriter.Data.contents, MatrixTableWriter.Data.cell,
          hcap, hR2, hH, hbody, hK, hfield, hn, hwriter]
    · fin_cases j <;>
        simp [CopyFill.fill, writerJobs, MatrixTableWriter.ready,
          MatrixTableWriter.Data.contents,
          MatrixTableWriter.Data.cell, hwriter]
  · cases z <;>
      simp [CopyFill.fill, writerJobs, MatrixTableWriter.ready,
        MatrixTableWriter.Data.contents,
        MatrixTableWriter.Data.foreign, hrows, hcols, hwriter]

#print axioms writerJobs_good
#print axioms physical_writer_prep_jobs
#print axioms writerPrep_ready

end CurrentAdditive.V38TablePrinter.Ambient
