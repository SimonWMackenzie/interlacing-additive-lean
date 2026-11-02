import CurrentAdditive.CanonicalWriterCoordClock

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoIndexDecoder Paper2.YaoLookup
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldCoordinate

noncomputable def canonicalLookupCleanupProgram :=
  BitMachineRawSequence.program
    (canonicalLookupProgramOn canonicalLookupPlace)
    canonicalCleanupProgram CanonicalCleanupLabel.c0
    MatrixTableLookup.initial ((), none)

noncomputable def canonicalCoordLookupCleanupProgram :=
  BitMachineRawSequence.program canonicalCoordProgramOn
    canonicalLookupCleanupProgram
    (BitMachineRawSequence.leftLabel MatrixTableLookup.start)
    payloadControl (MatrixTableLookup.initial, ((), none))

/-- One fixed finite-control entry program: decode row/column, compute the
selected incidence coordinate, read the packed field bit, and clear scratch. -/
noncomputable def canonicalEntryProgram :=
  BitMachineRawSequence.program (program canonicalIndexPlace)
    canonicalCoordLookupCleanupProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel stageStart))
    startControl (payloadControl, (MatrixTableLookup.initial, ((), none)))

noncomputable def canonicalEntryClock {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) : ℕ :=
  canonicalIndexClock (paddedEdgeBits e) t d i.val j.val +
    canonicalCoordClock t d modulus edges i j +
    canonicalLookupClock (paddedEdgeBits e) t d +
    canonicalCleanupTime
      (Function.update
        (canonicalCoordinateBank (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j)
        (.inr 2)
        [numericEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j]) + 3

/-- The actual four-stage entry program returns the exact canonical matrix
bit and restores the prepared bank for the generic row-major writer. -/
theorem canonical_writer_entry_run {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    ∃ steps ≤ canonicalEntryClock t d modulus edges i j,
      ((advance canonicalEntryProgram)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel startLabel),
          (startControl, (payloadControl,
            (MatrixTableLookup.initial, ((), (none : Option Bool))))),
          canonicalReady (paddedEdgeBits e) t d modulus edges i.val j.val⟩ :
          TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
        ⟨none, (startControl, (payloadControl,
            (MatrixTableLookup.initial, ((), (none : Option Bool))))),
          Function.update
            (canonicalReady (paddedEdgeBits e) t d modulus edges i.val j.val)
            (.inr 2)
            [numericEntry (paddedEdgeBits e) t d modulus
              (le_paddedEdgeCount e) edges i j]⟩ := by
  let ready := canonicalReady (paddedEdgeBits e) t d modulus edges i.val j.val
  let decoded := canonicalDecodedBank (paddedEdgeBits e) t d modulus edges i j
  let coordinated := canonicalCoordinateBank (paddedEdgeBits e) t d modulus
    (le_paddedEdgeCount e) edges i j
  let answered := Function.update coordinated (.inr 2)
    [numericEntry (paddedEdgeBits e) t d modulus
      (le_paddedEdgeCount e) edges i j]
  let restored := Function.update ready (.inr 2)
    [numericEntry (paddedEdgeBits e) t d modulus
      (le_paddedEdgeCount e) edges i j]
  obtain ⟨si, hsi, hri⟩ := canonical_writer_index_run
    (paddedEdgeBits e) t d modulus edges i j
  obtain ⟨sc, hsc, hrc⟩ := canonical_writer_coord_run_clock
    t d modulus edges i j
  obtain ⟨sl, hsl, hrl⟩ := canonical_writer_lookup_run
    (paddedEdgeBits e) t d modulus (le_paddedEdgeCount e) edges i j
  have hclean :
      ((advance canonicalCleanupProgram)^[canonicalCleanupTime answered])
        (⟨some .c0, ((), none), answered⟩ :
          TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
        ⟨none, ((), none), restored⟩ := by
    have hbank : BitMachineClearBank.cleared canonicalCleanupSlots answered =
        restored := by
      simpa only [answered, restored, coordinated, ready] using
        canonical_cleanup_bank t d modulus edges i j
    simpa only [hbank] using canonical_cleanup_run answered
  obtain ⟨slc, hslc, hrlc⟩ := BitMachineRawSequence.runs
    (canonicalLookupProgramOn canonicalLookupPlace)
    canonicalCleanupProgram
    MatrixTableLookup.start CanonicalCleanupLabel.c0
    MatrixTableLookup.initial MatrixTableLookup.initial
    ((), none) ((), none)
    coordinated answered restored sl (canonicalCleanupTime answered)
    (by simpa only [coordinated, answered] using hrl) hclean
  obtain ⟨sclc, hsclc, hrclc⟩ := BitMachineRawSequence.runs
    canonicalCoordProgramOn canonicalLookupCleanupProgram
    (BitMachineRawSequence.leftLabel stageStart)
    (BitMachineRawSequence.leftLabel MatrixTableLookup.start)
    payloadControl payloadControl
    (MatrixTableLookup.initial, ((), none))
    (MatrixTableLookup.initial, ((), none))
    decoded coordinated restored sc slc
    (by simpa only [decoded, coordinated] using hrc)
    (by simpa only [canonicalLookupCleanupProgram] using hrlc)
  obtain ⟨sentry, hsentry, hrentry⟩ := BitMachineRawSequence.runs
    (program canonicalIndexPlace) canonicalCoordLookupCleanupProgram
    startLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel stageStart))
    startControl startControl
    (payloadControl, (MatrixTableLookup.initial, ((), none)))
    (payloadControl, (MatrixTableLookup.initial, ((), none)))
    ready decoded restored si sclc
    (by simpa only [ready, decoded, canonicalDecodedBank] using hri)
    (by simpa only [canonicalCoordLookupCleanupProgram] using hrclc)
  refine ⟨sentry, ?_, ?_⟩
  · change sentry ≤
      canonicalIndexClock (paddedEdgeBits e) t d i.val j.val +
        canonicalCoordClock t d modulus edges i j +
        canonicalLookupClock (paddedEdgeBits e) t d +
        canonicalCleanupTime answered + 3
    omega
  · simpa only [canonicalEntryProgram, ready, restored] using hrentry

#print axioms canonical_writer_entry_run

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
