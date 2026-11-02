import CurrentAdditive.NextSourceThresholdBridge

/-! The physically constructed source/field/dimension/threshold bank satisfies
every exact input condition of the complete table-and-header renderer. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.YaoFrame Paper2.HeaderA Paper2.UnaryFieldListParserScratch

theorem sourceThresholdOutput_field {t : ℕ} (x : YaoSource t)
    (u : ℕ) :
    sourceThresholdOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
    sourceFieldOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) := by
  rw [sourceThresholdOutput_foreign x u _
      (by intro ⟨i, hi⟩; cases hi),
    sourceDimensionsOutput_foreign x u _
      (by intro ⟨i, hi⟩; cases hi)]

theorem physical_writer_after_threshold (t : ℕ)
    (x : YaoSource t) (u c : ℕ)
    (hpacked : sourceFieldOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1))) :
    let b := paddedEdgeBits x.2.1
    let d := publicFieldDegree b t
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c
    let S := sourceThresholdOutput x u
    let W := writerOutputBank t 16 d modulus x.2.2 S
    ∃ steps ≤
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
           natField (2*b+4*t+2)).length+2)+3) + 1) + 1,
      ∃ control,
        ((advance (writerHeaderProgram t 16))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (MultiMove.startLabel
                  ((writerJobs t 16).map CopyFill.toJob)))),
            ((MultiMove.initial, writerTableControl),
              (MultiMove.initial, progCtl)), S⟩ :
                TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
          ⟨none, ((MultiMove.initial, control),
              (MultiMove.initial, progCtl)),
            bank (headerEmbed t 16) (CopyFill.fill (headerJobs t 16) W)
              (fun k => if k = outH then
                encodeInstance (instanceOfTable b t d modulus
                  (le_paddedEdgeCount x.2.1) x.2.2)
                else [])⟩ := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let d := publicFieldDegree b t
  let n := H*(arity t+1)
  let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c
  let S := sourceThresholdOutput x u
  obtain ⟨hcap, hR2, hH, hbody, hK, hn, hrows, hcols⟩ :=
    sourceThresholdOutput_writer_inputs x u
  obtain ⟨hwriter, hheader, hscratch⟩ :=
    sourceThresholdOutput_writer_blank x u
  have hthr := sourceThresholdOutput_thr x u
  have hfield : S (.field (printerSlots
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      packedFieldBits d modulus (2^b*(2^t*2^t+1)) := by
    rw [show S (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      sourceFieldOutput x u (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) from
      sourceThresholdOutput_field x u]
    simpa [CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits,
      b, d, n, H, modulus, paddedEdgeCount, arity] using hpacked
  obtain ⟨steps, hsteps, control, hrun⟩ :=
    physical_writer_header t 16 d modulus x.2.2 S
      (by simpa [S] using hscratch)
      (by simpa [S] using hwriter)
      (by simpa [S] using hheader)
      (by simpa [S, b, H, paddedEdgeCount] using hcap)
      (by simpa [S, d] using hR2)
      (by simpa [S, b, H, paddedEdgeCount] using hH)
      (by simpa [S] using hbody)
      (by simpa [S, arity] using hK)
      hfield
      (by simpa [S, b, H, n, paddedEdgeCount, arity] using hn)
      (by simpa [S, b] using hrows)
      (by simpa [S, b, d] using hcols)
      (by simpa [S, b] using hthr)
  exact ⟨steps, hsteps, control,
    by simpa [S, b, d, modulus, writerOutputBank] using hrun⟩

#print axioms sourceThresholdOutput_field
#print axioms physical_writer_after_threshold

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
