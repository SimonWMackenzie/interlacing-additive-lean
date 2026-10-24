import CurrentAdditive.V38PrinterUniform

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLookup Paper2.YaoIndexDecoder
open CurrentAdditive.FiniteFieldCoordinate

set_option maxHeartbeats 1000000

noncomputable def canonicalTableClockCoefficient : ℕ :=
  20 * (10000 * CurrentAdditive.FiniteFieldCoordinate.coordinateProgramCoefficient +
    1003) ^ 3

/-- The actual row-major writer bound, with the physical four-stage callback,
is polynomial in the public size of the prepared canonical bank. It charges
every table entry and the writer's row/column control overhead. -/
theorem canonical_writerBound_le_cellSize {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    MatrixTableWriter.writerBound
      (rowCount v (paddedEdgeBits e) t)
      (columnCount (paddedEdgeBits e) t d)
      (canonicalUniformEntryClock t d modulus edges) ≤
        canonicalTableClockCoefficient *
          (canonicalCellSize t d edges + 1) ^ 12 := by
  let b := paddedEdgeBits e
  let H := 2 ^ b
  let K := 2 ^ t * 2 ^ t
  let R := rowCount v b t
  let C := columnCount b t d
  let body := Paper2.UnaryFieldListParserScratch.tokens
    (List.ofFn (Paper2.YaoSourceCodec.flatten edges))
  let B := canonicalCellSize t d edges
  let T := canonicalUniformEntryClock t d modulus edges
  let A := 10000 * CurrentAdditive.FiniteFieldCoordinate.coordinateProgramCoefficient + 1000
  let X := (B + 1) ^ 4
  have hR : R ≤ B := by
    change R ≤ R + C + body.length + H * (K + 1) + K + H + 1
    have hH : 0 < H := by dsimp [H]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    omega
  have hC : C ≤ B := by
    change C ≤ R + C + body.length + H * (K + 1) + K + H + 1
    have hH : 0 < H := by dsimp [H]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    omega
  have hT : T ≤ A * X := canonicalUniformEntryClock_le_cellSize t d modulus edges
  have hBX : B + 1 ≤ X := by
    dsimp [X]
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (show 0 < B + 1 by omega) (show 1 ≤ 4 by omega))
  have hRC : R + C + 1 ≤ 3 * X := by omega
  have hinner : R + C + T + 1 ≤ (A + 3) * X := by
    calc
      R + C + T + 1 ≤ 3 * X + A * X := by omega
      _ = (A + 3) * X := by ring
  have hpoly := MatrixTableWriter.writerBound_polynomial R C T
  calc
    MatrixTableWriter.writerBound R C T ≤
        20 * (R + C + T + 1) ^ 3 := hpoly
    _ ≤ 20 * ((A + 3) * X) ^ 3 := by gcongr
    _ = canonicalTableClockCoefficient * (B + 1) ^ 12 := by
      dsimp [canonicalTableClockCoefficient, A, X]
      ring

/-- Physical table run with an explicit fixed-degree clock and exact
row-major Boolean output. The seven static input cells remain prepared. -/
theorem canonical_writer_table_run_polynomial {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (output : List Bool) :
    ∃ steps ≤ canonicalTableClockCoefficient *
        (canonicalCellSize t d edges + 1) ^ 12,
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
  obtain ⟨steps, hsteps, control, hr⟩ :=
    canonical_writer_table_run t d modulus edges output
  exact ⟨steps, hsteps.trans
    (canonical_writerBound_le_cellSize t d modulus edges), control, hr⟩

#print axioms canonical_writerBound_le_cellSize
#print axioms canonical_writer_table_run_polynomial

end CurrentAdditive.V38TablePrinter
