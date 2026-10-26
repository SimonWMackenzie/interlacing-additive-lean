import Paper2.SeedJoin
import Paper2.StepXCanon

/-! Unit 3, segments (2) and (3) at the canonical instance of
`CodedEntryEvaluatorScratch.codedCanonicalEntry`: widths `p = LookupSeed.width L`,
`s = width L`, `q₁ = width L - 2`, `q₂ = outerWidth L`, the canonical default tails
`CanonicalDefaultSource.canonicalDefaultTails` and the activity `scanAtCanonical`;
the fixed-tail premise is discharged by `StepXCanon.canonical_hfix`. No premise on
the tails remains. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RLoop

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix SourceProfileParameters

theorem request_loop_canonical (L w Q r : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)] [NeZero w] [NeZero Q]
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q K)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q K)
    (c : Option Bool × type_of% bodyCtl) :
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn hw hQ
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by have := SourceProfiles.width_ge_four L; omega) hq
    let sd := RecursiveEntries.seedRequest activity ξ K x y
    ∃ t ≤ K * (loopBd g hg (SourceProfiles.width_ge_four L) r hq ξ K x y + 2) + 1, ∃ c',
      ((advance rloop)^[t])
        (⟨some (.inl ()), c, bankL g r K x y⟩ : TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, c', bankL (n := g.vertices) (p := LookupSeed.width L) (s := width L)
          (q₁ := width L - 2) (q₂ := outerWidth L) (w := w) (Q := Q) g r 0 sd.1 sd.2⟩ :=
  request_loop g hg (by unfold LookupSeed.width; positivity) (SourceProfiles.width_ge_four L) r hq
    (CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn hw hQ)
    (fun k i => StepXCanon.canonical_hfix L w Q r g hg hn hw hQ hq k i) K x y c

theorem seed_join_canonical (L w Q r : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)] [NeZero w] [NeZero Q]
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (K : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q K)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q K) :
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn hw hQ
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by have := SourceProfiles.width_ge_four L; omega) hq
    let sd := RecursiveEntries.seedRequest activity ξ K x y
    ∃ t ≤ K * (loopBd g hg (SourceProfiles.width_ge_four L) r hq ξ K x y + 2) + 1 +
        (9 * LookupSeed.width L + 13) + 1, ∃ v,
      ((advance entryProg)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl ())),
          (((none : Option Bool), bodyCtl), (SeedEntryMachine.readInitial, (none : Option Bool))),
          bankL g r K x y⟩ : TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, v, Function.update
          (bankL (n := g.vertices) (p := LookupSeed.width L) (s := width L)
            (q₁ := width L - 2) (q₂ := outerWidth L) (w := w) (Q := Q) g r 0 sd.1 sd.2) ansC
          [RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L)) activity ξ K x y]⟩ :=
  seed_join g hg (by unfold LookupSeed.width; positivity) (SourceProfiles.width_ge_four L) r hq
    (CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn hw hQ)
    (fun k i => StepXCanon.canonical_hfix L w Q r g hg hn hw hQ hq k i) K x y

end

#print axioms request_loop_canonical
#print axioms seed_join_canonical

end Paper2.RLoop
