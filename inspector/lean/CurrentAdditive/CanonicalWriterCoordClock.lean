import CurrentAdditive.CanonicalWriterCoordRun

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.UnaryFieldListParserScratch
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldCoordinate

noncomputable def canonicalCoordClock {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) : ℕ :=
  let S : CurrentAdditive.FiniteFieldCoordinate.Stack → List Bool :=
    fun k => (canonicalDecodedBank (paddedEdgeBits e) t d modulus edges i j)
      (canonicalCoordPlace k)
  let row := (rowIndex v (paddedEdgeBits e) t).symm i
  let col := (columnIndex (paddedEdgeBits e) t d).symm j
  let q := 2 ^ (t - 1)
  let H := paddedEdgeCount e
  let K := 2 ^ t * 2 ^ t
  let α := selector q H row.2 col.1
  let p := position (le_paddedEdgeCount e) edges col.2.1 row.1
  CopyFill.fillCost jobs S + 1 +
    selectorClock q H row.2.val col.1.val +
    positionClock t col.2.1.val row.1.val
      (tokens (List.ofFn (flatten edges))) +
    1 + payloadClock K α.val p.val +
    (32 * preclearBound q H K row.2.val col.1.val t
      col.2.1.val row.1.val α.val p.val
      (tokens (List.ofFn (flatten edges))) S + 34) + 5

/-- The actual lifted coordinate run has an explicit count depending only
on the prepared input bank and its public numeric labels. -/
theorem canonical_writer_coord_run_clock {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    ∃ steps ≤ canonicalCoordClock t d modulus edges i j,
      ((advance canonicalCoordProgramOn)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel stageStart), payloadControl,
          canonicalDecodedBank (paddedEdgeBits e) t d modulus edges i j⟩ :
          TM2.Cfg (fun _ : CanonicalCell => Bool) _ _) =
        ⟨none, payloadControl,
          canonicalCoordinateBank (paddedEdgeBits e) t d modulus
            (le_paddedEdgeCount e) edges i j⟩ := by
  let S := canonicalDecodedBank (paddedEdgeBits e) t d modulus edges i j
  let localS : CurrentAdditive.FiniteFieldCoordinate.Stack → List Bool :=
    fun k => S (canonicalCoordPlace k)
  let row := (rowIndex v (paddedEdgeBits e) t).symm i
  let col := (columnIndex (paddedEdgeBits e) t d).symm j
  obtain ⟨hz, hg, hH, ha, hv, hbody, hK, hblank⟩ :=
    canonicalDecoded_coord_inputs (paddedEdgeBits e) t d modulus edges i j
  obtain ⟨steps, hsteps, hrun⟩ := physical_payload_coord edges
    row.2 col.1 col.2.1 row.1 localS
    hz hg hH ha hv hbody hK hblank
  have hvalue := canonical_coord_value t d edges i j
  rw [hvalue] at hrun
  have hlift := BitMachineStackRun.run canonicalCoordPlace S payloadCoordProgram
    (⟨some (BitMachineRawSequence.leftLabel stageStart), payloadControl, localS⟩ :
      TM2.Cfg (fun _ : CurrentAdditive.FiniteFieldCoordinate.Stack => Bool) _ _)
    steps
  rw [hrun] at hlift
  have hbank : bank canonicalCoordPlace S localS = S := by
    simpa only [localS] using bank_restrict canonicalCoordPlace S
  refine ⟨steps, ?_, ?_⟩
  · simpa only [canonicalCoordClock, S, localS, row, col] using hsteps
  · simpa only [canonicalCoordProgramOn, stackCfg, hbank, bank_update,
      canonicalCoordinateBank, S] using hlift

#print axioms canonical_writer_coord_run_clock

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
