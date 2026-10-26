import CurrentAdditive.CanonicalWriterCleanupBank
import CurrentAdditive.CoordinateFull
import EthInapproximability.CurrentPaper.BitMachineStackRun

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoLookup Paper2.YaoSourceCodec
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldCoordinate

noncomputable def canonicalCoordProgramOn :=
  fun l => stackStmt canonicalCoordPlace (payloadCoordProgram l)

/-- The fixed forty-stack coordinate callback runs inside the writer bank.
Its terminal address is exactly the packed-field payload coordinate, and no
other writer cell changes. -/
theorem canonical_writer_coord_run {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    ∃ steps,
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
  obtain ⟨steps, _, hrun⟩ := physical_payload_coord edges
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
  refine ⟨steps, ?_⟩
  simpa only [canonicalCoordProgramOn, stackCfg, hbank, bank_update,
    canonicalCoordinateBank, S] using hlift

#print axioms canonical_writer_coord_run

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
