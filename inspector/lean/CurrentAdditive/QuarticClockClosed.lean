import CurrentAdditive.QuarticClockHA3
import CurrentAdditive.QuarticPreludeClock
import Paper2.A3H3ClockS

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticClockClosed

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters
open CurrentAdditive.RandomizedSchedule

/-! ## (S) the success chain, closed -/

/-- The success-branch consumer bound with the prelude clock plugged in (no remaining premise). -/
theorem success_clock_closed (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (hL : L = Nat.clog 2 g.vertices) :
    SamplerFallbackJoin.clock g.vertices (LookupSeed.width L) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K
        (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
        (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) +
      Paper2.SuccessClock2Pre.preClock g (LookupSeed.width L) (width L) (width L - 2) (outerWidth L)
        (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K
        (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
        (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
        (SourceRecursiveNoSampling.sourceBudget L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
        ((WEntry.colWords g K _ ys).flatten ++ (WEntry.rowWords g K _ xs).flatten).length
        (SuccessXfer.xLmax g K _ _ xs ys) +
      MatrixTableWriter.writerBound
        (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
        (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
        (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys) ≤
      1 * (g.vertices + 2) ^ ((2 * (FallbackNoPreloadRun.noPreloadExponent +
        Paper2.SuccessClock2Pre.preExponent + Paper2.SuccessClock.entryExponent 2601 + 65)) * (K + 1)) :=
  QuarticClockHA3.success_clock_HA3_27 L Δ γ g hg hc r hq ξ K xs ys _
    Paper2.SuccessClock2Pre.preExponent
    (QuarticPreludeClock.pre_sched27 g hg Δ γ K L hL hc xs ys) hL

/-- **(S)** The LITERAL clock of the admitted one-program success endpoint
`ThrJoin.success_run_full` (its bound, summand shape of `ThrMain.lean` l.91-97, with the sampler
clock and writer clock in place), in H_A3 shape `1·(n+2)^(ES(k+1))`,
`ES = 2(noPreloadExponent + preExponent + entryExponent 2601 + 65)`. -/
theorem success_full_clock_HA3 (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (hL : L = Nat.clog 2 g.vertices) :
    ThrJoin.joinBd (LookupSeed.width L) (width L) (outerWidth L) (width27 L)
        (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K +
      (((1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
        103 * ((EncodedGraph.encode g).length + 1) ^ 3 + 1 +
        (1 * (2 * g.edges.length + 3) + 1) + 1) +
      (SuccessInstall.instBd (width L) (width L - 2) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)
          (LookupSeed.width L) (width27 L) K +
        (SamplerFallbackJoin.clock g.vertices (LookupSeed.width L) (width L) (width L - 2)
            (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K
            (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
              ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
            (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
              ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) +
          (3 * ((WEntry.colWords g K _ ys).flatten ++ (WEntry.rowWords g K _ xs).flatten).length + 4) +
          (6 * (2 * SuccessXfer.xLmax g K _ _ xs ys + 3) + 1 +
            (MatrixTableWriter.writerBound
              (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
                ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
              (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
                ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
              (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys) +
              WEntry.hdrBd
                (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
                  ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
                (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
                  ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
                (SourceRecursiveNoSampling.sourceBudget L ((4 * RestorationWidthScheduleScratch.ell L))
                  ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K) + 1) + 1) + 1) + 1) + 1) + 1 ≤
      1 * (g.vertices + 2) ^ ((2 * (FallbackNoPreloadRun.noPreloadExponent +
        Paper2.SuccessClock2Pre.preExponent + Paper2.SuccessClock.entryExponent 2601 + 65)) * (K + 1)) := by
  have h1 := Paper2.SuccessClock2Pre.full_split g (LookupSeed.width L) (width L) (width L - 2)
    (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K
    (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
      ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
    (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
      ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
    (SourceRecursiveNoSampling.sourceBudget L ((4 * RestorationWidthScheduleScratch.ell L))
      ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
    ((WEntry.colWords g K _ ys).flatten ++ (WEntry.rowWords g K _ xs).flatten).length
    (SuccessXfer.xLmax g K _ _ xs ys)
    (SamplerFallbackJoin.clock g.vertices (LookupSeed.width L) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K
      (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
      (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K))
    (MatrixTableWriter.writerBound
      (SourceRecursiveNoSampling.sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
      (SourceRecursiveNoSampling.sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)) K)
      (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys))
  have h2 := success_clock_closed L Δ γ g hg hc r hq ξ K xs ys hL
  exact le_trans h1 h2


end Paper2.CurrentAdditive.QuarticClockClosed

#print axioms Paper2.CurrentAdditive.QuarticClockClosed.success_clock_closed
#print axioms Paper2.CurrentAdditive.QuarticClockClosed.success_full_clock_HA3
