import Paper2.SC2Bank

/-! Lane a-success-clock-owner-2, segment (5), first half: the per-entry clock
`WEntry.Tent` at the public schedule WITHOUT premises (the four component
premises of the admitted `SuccessClock.Tent_sched` discharged with `a = 2601`),
and the admitted consumer `SuccessPremiseComposition.composed_all_tape_clock_le`
applied to it with the prelude clock `pre` as its only remaining premise `hpre`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters

/-- The success-branch per-entry clock, unconditional at the public schedule. -/
theorem Tent_uncond (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
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
 :
    WEntry.Tent g hg (SourceProfiles.width_ge_four L) r hq ξ K _ _ xs ys ≤
      2 ^ (Paper2.SuccessClock.entryExponent 2601 * (K + 1) * L) :=
  Paper2.SuccessClock.Tent_sched L Δ γ g hg hc r hq ξ K xs ys 2601
    (Hstep_sched L Δ γ g hg hc r hq ξ K) (Hjoin_sched L Δ γ g hg hc r hq K)
    (Hmaster_sched L Δ γ g hg hc r hq K) (Hbank_sched L Δ γ g hg hc r hq K)

/-- The admitted success-branch consumer with only the prelude premise `hpre` left. -/
theorem success_clock_uncond (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
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
    (pre cP : ℕ) (hpre : pre ≤ 2 ^ (cP * (K + 1) * L)) :
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
      2 ^ ((FallbackNoPreloadRun.noPreloadExponent + cP + Paper2.SuccessClock.entryExponent 2601 + 65) * (K + 1) * L) :=
  Paper2.SuccessClock.success_clock_composed L Δ γ g hg hc r hq ξ K xs ys 2601 pre cP hpre
    (Hstep_sched L Δ γ g hg hc r hq ξ K) (Hjoin_sched L Δ γ g hg hc r hq K)
    (Hmaster_sched L Δ γ g hg hc r hq K) (Hbank_sched L Δ γ g hg hc r hq K)

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.Tent_uncond
#print axioms Paper2.SuccessClock2.success_clock_uncond
