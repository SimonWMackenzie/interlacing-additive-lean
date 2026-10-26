import CurrentAdditive.CanonicalAmbientWriterHeaderFull
import CurrentAdditive.V38AmbientPrep

/-! The exact bounded canonical table writer, embedded as a literal program
in the shared ambient stack namespace. -/

noncomputable section

namespace CurrentAdditive.V38TablePrinter.Ambient

open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup

def tableStage (t N : ℕ) :=
  fun l => stackStmt (writerEmbed t N)
    (MatrixTableWriter.program canonicalEntryProgram
      (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
      (Paper2.YaoIndexDecoder.startControl, (FiniteFieldCoordinate.payloadControl,
        (MatrixTableLookup.initial, ((), (none : Option Bool))))) l)

theorem physical_ambient_table {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hlocal : ∀ k : MatrixTableWriter.Stack 60,
      S (.writer k) =
        (MatrixTableWriter.ready
          (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
          (rowCount v (paddedEdgeBits e) t)
          (columnCount (paddedEdgeBits e) t d)
          0 0 0 0 [] []).contents k) :
    ∃ steps ≤ canonicalTableClockCoefficient *
        (canonicalCellSize t d edges + 1) ^ 12,
      ∃ control,
        ((advance (tableStage t N))^[steps])
          (⟨some (.inr (.copy .rows)),
            ((Paper2.YaoIndexDecoder.startControl, (FiniteFieldCoordinate.payloadControl,
              (MatrixTableLookup.initial, ((), (none : Option Bool))))), none),
            S⟩ : TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
          stackCfg (writerEmbed t N) S
            (MatrixTableWriter.cfg none control
              (MatrixTableWriter.ready
                (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
                (rowCount v (paddedEdgeBits e) t)
                (columnCount (paddedEdgeBits e) t d)
                0 0 0 0 []
                (table (paddedEdgeBits e) t d modulus
                  (le_paddedEdgeCount e) edges).bits)) := by
  obtain ⟨steps, hsteps, control, hrun⟩ :=
    canonical_writer_table_run_polynomial t d modulus edges []
  refine ⟨steps, hsteps, control, ?_⟩
  have hbank := bank_eq_self (writerEmbed t N) S _
    (by intro k; exact (hlocal k).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (writerEmbed t N) S
    (MatrixTableWriter.program canonicalEntryProgram
      (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
      (Paper2.YaoIndexDecoder.startControl, (FiniteFieldCoordinate.payloadControl,
        (MatrixTableLookup.initial, ((), (none : Option Bool))))))
    (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
      ((Paper2.YaoIndexDecoder.startControl,
        (FiniteFieldCoordinate.payloadControl,
          (MatrixTableLookup.initial, ((), (none : Option Bool))))), none)
      (MatrixTableWriter.ready
        (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
        (rowCount v (paddedEdgeBits e) t)
        (columnCount (paddedEdgeBits e) t d)
        0 0 0 0 [] [])) steps
  have hr := congrArg (stackCfg (writerEmbed t N) S) hrun
  have hcombined := he.trans (by simpa [MatrixTableWriter.run] using hr)
  simpa [tableStage, stackCfg, MatrixTableWriter.cfg, hbank] using hcombined

#print axioms physical_ambient_table

end CurrentAdditive.V38TablePrinter.Ambient
