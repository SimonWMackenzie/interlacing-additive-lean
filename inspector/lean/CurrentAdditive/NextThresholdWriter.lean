import CurrentAdditive.NextWriterAfterThreshold

/-! The physical threshold constructor followed by the complete canonical
table/header renderer, starting from the source-derived dimensions bank. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.YaoFrame Paper2.HeaderA

def writerAfterThresholdClock {t : ℕ} (x : YaoSource t)
    (u c : ℕ) : ℕ :=
  let b := paddedEdgeBits x.2.1
  let d := publicFieldDegree b t
  let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c
  let S := sourceThresholdOutput x u
  let W := writerOutputBank t 16 d modulus x.2.2 S
  (CopyFill.fillCost (writerJobs t 16) S + 1 +
    canonicalTableClockCoefficient *
      (canonicalCellSize t d x.2.2 + 1)^12 + 1) +
  (CopyFill.fillCost (headerJobs t 16) W + 1 +
    (UnaryBinaryEncoding.coefficient *
      (rowCount x.1 b t + 1)^2 +
     UnaryBinaryEncoding.coefficient *
      (columnCount b t d + 1)^2 +
     UnaryBinaryEncoding.coefficient *
      (2*b+4*t+2+1)^2 +
     (2*(natField (rowCount x.1 b t) ++
       natField (columnCount b t d) ++
       natField (2*b+4*t+2)).length+2)+3) + 1) + 1

def thresholdWriterProgram (t : ℕ) :=
  BitMachineRawSequence.program (thresholdFullProgram t 16)
    (writerHeaderProgram t 16)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel ((writerJobs t 16).map CopyFill.toJob))))
    (none, (none, (none, ())))
    ((MultiMove.initial, writerTableControl), (MultiMove.initial, progCtl))

theorem physical_threshold_writer (t : ℕ) (x : YaoSource t)
    (u c : ℕ)
    (hpacked : sourceFieldOutput x u
      (.field (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1))) :
    let b := paddedEdgeBits x.2.1
    let d := publicFieldDegree b t
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c
    let W := writerOutputBank t 16 d modulus x.2.2
      (sourceThresholdOutput x u)
    ∃ steps ≤
        ((2*b+2)+(2*(2*b+2)+(4*t+3)+2)+1) +
        writerAfterThresholdClock x u c + 1,
      ∃ control,
        ((advance (thresholdWriterProgram t))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            ((none, (none, (none, ()))),
              ((MultiMove.initial, writerTableControl),
                (MultiMove.initial, progCtl))),
            sourceDimensionsOutput x u⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
          ⟨none,
            ((none, (none, (none, ()))),
              ((MultiMove.initial, control),
                (MultiMove.initial, progCtl))),
            bank (headerEmbed t 16) (CopyFill.fill (headerJobs t 16) W)
              (fun k => if k = outH then
                encodeInstance (instanceOfTable b t d modulus
                  (le_paddedEdgeCount x.2.1) x.2.2)
                else [])⟩ := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let d := publicFieldDegree b t
  let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c
  let W := writerOutputBank t 16 d modulus x.2.2
    (sourceThresholdOutput x u)
  obtain ⟨a, ha, hthr⟩ := physical_threshold_after_dimensions t x u
  obtain ⟨w, hw, control, hwriter⟩ :=
    physical_writer_after_threshold t x u c hpacked
  change w ≤ writerAfterThresholdClock x u c at hw
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (thresholdFullProgram t 16) (writerHeaderProgram t 16)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel ((writerJobs t 16).map CopyFill.toJob))))
    (none, (none, (none, ()))) (none, (none, (none, ())))
    ((MultiMove.initial, writerTableControl), (MultiMove.initial, progCtl))
    ((MultiMove.initial, control), (MultiMove.initial, progCtl))
    (sourceDimensionsOutput x u) (sourceThresholdOutput x u) _ a w
    hthr (by simpa [W] using hwriter)
  refine ⟨steps, by omega, control, ?_⟩
  simpa [thresholdWriterProgram, W] using hrun

#print axioms physical_threshold_writer

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
