import CurrentAdditive.QuarticPreludeClock
import Paper2.SC2Close

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticClockHA3

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters Paper2.SuccessClock2
open CurrentAdditive.RandomizedSchedule

theorem success_clock_HA3_27 (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (width27 L)] [NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
    (pre cP : ℕ) (hpre : pre ≤ 2 ^ (cP * (K + 1) * L))
    (hL : L = Nat.clog 2 g.vertices) :
    SamplerFallbackJoin.clock g.vertices (LookupSeed.width L) (width L) (width L - 2)
        (outerWidth L) (width27 L) (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K
        (SourceRecursiveNoSampling.sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
        (SourceRecursiveNoSampling.sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K) + pre +
      MatrixTableWriter.writerBound
        (SourceRecursiveNoSampling.sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
        (SourceRecursiveNoSampling.sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ) K)
        (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys) ≤
      1 * (g.vertices + 2) ^ ((2 * (FallbackNoPreloadRun.noPreloadExponent + cP +
        Paper2.SuccessClock.entryExponent 2601 + 65)) * (K + 1)) := by
  have h := QuarticClockFinal.success_clock_uncond27 L Δ γ g hg hc r hq ξ K xs ys pre cP hpre
  subst hL
  exact h.trans (clock_conv _ K g.vertices)


end Paper2.CurrentAdditive.QuarticClockHA3

#print axioms Paper2.CurrentAdditive.QuarticClockHA3.success_clock_HA3_27
