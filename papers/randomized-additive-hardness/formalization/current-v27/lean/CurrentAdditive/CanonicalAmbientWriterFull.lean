import CurrentAdditive.CanonicalAmbientSourceDegreeWidth
import CurrentAdditive.CanonicalAmbientDimensionsFull

/-! Charged nine-word preparation and the exact row-major table writer are
one literal ambient program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoSourceCodec Paper2.YaoMachine
open Paper2.UnaryFieldListParserScratch

def writerTableControl :=
  ((Paper2.YaoIndexDecoder.startControl,
    (FiniteFieldCoordinate.payloadControl,
      (MatrixTableLookup.initial, ((), (none : Option Bool))))),
    (none : Option Bool))

def writerFullProgram (t N : ℕ) :=
  BitMachineRawSequence.program (writerPrepProgram t N) (tableStage t N)
    (.inr (.copy .rows)) MultiMove.initial writerTableControl

theorem physical_writer_full {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hscratch : S (.copyScratch 0) = [])
    (hwriter : ∀ k : MatrixTableWriter.Stack 60, S (.writer k) = [])
    (hcap : S (.selector 1) =
      List.replicate ((2 ^ (paddedEdgeBits e)) ^ (2 ^ (t - 1))) true)
    (hR2 : S (.square 3) = List.replicate ((2 ^ d) ^ 2) true)
    (hH : S (.source (sN 6)) = List.replicate (2 ^ (paddedEdgeBits e)) true)
    (hbody : S (.source (sN 1)) = tokens (List.ofFn (flatten edges)))
    (hK : S (.source (sN 9)) = List.replicate (2 ^ t * 2 ^ t) true)
    (hfield : S (.field (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
        packedFieldBits d modulus
          (2 ^ (paddedEdgeBits e) * (2 ^ t * 2 ^ t + 1)))
    (hn : S (.width 3) =
      List.replicate (2 ^ (paddedEdgeBits e) * (2 ^ t * 2 ^ t + 1)) true)
    (hrows : S (.dimensions 5) =
      List.replicate (rowCount v (paddedEdgeBits e) t) true)
    (hcols : S (.dimensions 7) =
      List.replicate (columnCount (paddedEdgeBits e) t d) true) :
    ∃ steps ≤ CopyFill.fillCost (writerJobs t N) S + 1 +
        canonicalTableClockCoefficient *
          (canonicalCellSize t d edges + 1)^12 + 1,
      ∃ control,
        ((advance (writerFullProgram t N))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
              (MultiMove.startLabel ((writerJobs t N).map CopyFill.toJob))),
            (MultiMove.initial, writerTableControl), S⟩ :
              TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
          ⟨none, (MultiMove.initial, control),
            bank (writerEmbed t N) (CopyFill.fill (writerJobs t N) S)
              (MatrixTableWriter.ready
                (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
                (rowCount v (paddedEdgeBits e) t)
                (columnCount (paddedEdgeBits e) t d)
                0 0 0 0 []
                (table (paddedEdgeBits e) t d modulus
                  (le_paddedEdgeCount e) edges).bits).contents⟩ := by
  let S1 := CopyFill.fill (writerJobs t N) S
  have hblank : ∀ j ∈ writerJobs t N, ∀ dst ∈ j.2, S dst = [] := by
    intro j hj dst hd
    simp [writerJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
      simp_all [hwriter]
  have hprep := physical_writer_prep_jobs t N S hscratch hblank
  have hlocal := writerPrep_ready t N d modulus edges S hwriter
    hcap hR2 hH hbody hK hfield hn hrows hcols
  obtain ⟨u, hu, control, htable⟩ := physical_ambient_table
    t N d modulus edges S1 (by intro k; exact hlocal k)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (writerPrepProgram t N) (tableStage t N)
    (MultiMove.startLabel ((writerJobs t N).map CopyFill.toJob))
    (.inr (.copy .rows))
    MultiMove.initial MultiMove.initial writerTableControl control
    S S1 _ (CopyFill.fillCost (writerJobs t N) S+1) u
    (by simpa [S1] using hprep)
    (by simpa [S1, writerTableControl, stackCfg] using htable)
  exact ⟨steps, by omega, control,
    by simpa [writerFullProgram, writerTableControl, S1, stackCfg]
      using hrun⟩

#print axioms physical_writer_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
