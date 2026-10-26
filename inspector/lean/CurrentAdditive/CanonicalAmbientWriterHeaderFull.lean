import CurrentAdditive.CanonicalAmbientWriterHeaderBridge

/-! From nine available public words, one ambient TM2 program physically
copies the writer bank, prints the whole table, copies the framing words, and
emits the exact encoded canonical instance. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoSourceCodec Paper2.YaoMachine
open Paper2.YaoFrame Paper2.HeaderA Paper2.UnaryFieldListParserScratch

def writerHeaderProgram (t N : ℕ) :=
  BitMachineRawSequence.program (writerFullProgram t N)
    (headerFullProgram t N)
    (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((headerJobs t N).map CopyFill.toJob)))
    (MultiMove.initial, writerTableControl)
    (MultiMove.initial, progCtl)

theorem physical_writer_header {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hscratch : S (.copyScratch 0) = [])
    (hwriter : ∀ k : MatrixTableWriter.Stack 60, S (.writer k) = [])
    (hheader : ∀ k : HB, S (.header k) = [])
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
      List.replicate (columnCount (paddedEdgeBits e) t d) true)
    (hthr : S (.threshold 1) =
      List.replicate (2*paddedEdgeBits e+4*t+2) true) :
    let W := writerOutputBank t N d modulus edges S
    ∃ steps ≤
      (CopyFill.fillCost (writerJobs t N) S + 1 +
        canonicalTableClockCoefficient *
          (canonicalCellSize t d edges + 1)^12 + 1) +
      (CopyFill.fillCost (headerJobs t N) W + 1 +
        (UnaryBinaryEncoding.coefficient *
          (rowCount v (paddedEdgeBits e) t + 1)^2 +
         UnaryBinaryEncoding.coefficient *
          (columnCount (paddedEdgeBits e) t d + 1)^2 +
         UnaryBinaryEncoding.coefficient *
          (2*paddedEdgeBits e+4*t+2+1)^2 +
         (2*(natField (rowCount v (paddedEdgeBits e) t) ++
           natField (columnCount (paddedEdgeBits e) t d) ++
           natField (2*paddedEdgeBits e+4*t+2)).length+2)+3) + 1) + 1,
      ∃ control,
        ((advance (writerHeaderProgram t N))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (MultiMove.startLabel ((writerJobs t N).map CopyFill.toJob)))),
            ((MultiMove.initial, writerTableControl),
              (MultiMove.initial, progCtl)), S⟩ :
                TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
          ⟨none, ((MultiMove.initial, control),
              (MultiMove.initial, progCtl)),
            bank (headerEmbed t N) (CopyFill.fill (headerJobs t N) W)
              (fun k => if k = outH then
                encodeInstance
                  (instanceOfTable (paddedEdgeBits e) t d modulus
                    (le_paddedEdgeCount e) edges)
                else [])⟩ := by
  dsimp only
  let W := writerOutputBank t N d modulus edges S
  obtain ⟨u, hu, control, hwriterRun⟩ := physical_writer_full
    t N d modulus edges S hscratch hwriter hcap hR2 hH hbody hK
      hfield hn hrows hcols
  obtain ⟨hh, hs, hr, hc, ht⟩ :=
    writerOutputBank_header_inputs t N d modulus edges S
  have hblank : ∀ k : HB, W (.header k) = [] := by
    intro k
    rw [show W (.header k) = S (.header k) from hh k]
    exact hheader k
  obtain ⟨vsteps, hv, hheaderRun⟩ := physical_header_full
    t N d modulus edges W (by exact hs.trans hscratch) hblank
    (by simpa [W] using hr.trans hrows)
    (by simpa [W] using hc.trans hcols)
    (by simpa [W] using ht.trans hthr)
    (by exact writerOutputBank_bits t N d modulus edges S)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (writerFullProgram t N) (headerFullProgram t N)
    (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((writerJobs t N).map CopyFill.toJob)))
    (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((headerJobs t N).map CopyFill.toJob)))
    (MultiMove.initial, writerTableControl)
    (MultiMove.initial, control)
    (MultiMove.initial, progCtl) (MultiMove.initial, progCtl)
    S W _ u vsteps
    (by simpa [W, writerOutputBank] using hwriterRun)
    (by simpa [W] using hheaderRun)
  dsimp [W] at hv
  exact ⟨steps, by omega, writerTableControl,
    by simpa [writerHeaderProgram, W] using hrun⟩

#print axioms physical_writer_header

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
