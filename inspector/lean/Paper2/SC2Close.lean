import Paper2.SC2Final
import Paper2.SC2Conv

/-! Lane a-success-clock-owner-2, segment (5): the success-branch consumer bound of
`success_clock_uncond` at `L = clog₂ n`, converted into the H-A3 clock shape
`CA * (g.vertices + 2) ^ (EA * (K + 1))` with `CA = 1`,
`EA = 2 * (FallbackNoPreloadRun.noPreloadExponent + cP + SuccessClock.entryExponent 2601 + 65)`;
the prelude premise `hpre` is the only remaining premise. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters

theorem success_clock_HA3 (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (restorationWidth L)] [NeZero (coverWidth g.vertices g.edges.length L Δ γ)]
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) L Δ γ)
    (r : ℕ) (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ))
    (K : ℕ)
    (xs : Fin (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
        (coverDepth g.vertices g.edges.length L Δ γ) K) →
      Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K)
    (ys : Fin (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
        (coverDepth g.vertices g.edges.length L Δ γ) K) →
      Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K)
    (pre cP : ℕ) (hpre : pre ≤ 2 ^ (cP * (K + 1) * L))
    (hL : L = Nat.clog 2 g.vertices) :
    SamplerFallbackJoin.clock g.vertices (LookupSeed.width L) (width L) (width L - 2)
        (outerWidth L) (restorationWidth L) (coverWidth g.vertices g.edges.length L Δ γ) K
        (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K)
        (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K) + pre +
      MatrixTableWriter.writerBound
        (SourceRecursiveNoSampling.sourceRows L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K)
        (SourceRecursiveNoSampling.sourceCols L (restorationDepth L)
          (coverDepth g.vertices g.edges.length L Δ γ) K)
        (WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys) ≤
      1 * (g.vertices + 2) ^ ((2 * (FallbackNoPreloadRun.noPreloadExponent + cP +
        Paper2.SuccessClock.entryExponent 2601 + 65)) * (K + 1)) := by
  have h := success_clock_uncond L Δ γ g hg hc r hq ξ K xs ys pre cP hpre
  subst hL
  exact h.trans (clock_conv _ K g.vertices)

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.success_clock_HA3
