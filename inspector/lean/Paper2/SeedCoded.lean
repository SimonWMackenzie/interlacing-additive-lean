import Paper2.RLoopCanon
import Paper2.CodedEntryEvaluator

/-! Unit 3, segment (4), first part: the answer of the ONE program `entryProg`
(k-fold request loop, then seed lookup) at the public schedule of
`CodedEntryEvaluatorScratch.codedCanonicalEntry` (edge map `graphEdge g hg`,
`m = g.edges.length`, `r = rep L m`, `w = restorationWidth L`,
`Q = coverWidth n m L Δ γ`) IS `codedCanonicalEntry` of the two words the loop reads
(the scheduled encodings of the pair, in `r1 Xc`, `r1 Yc`): the production
`codedCanonicalEntry_encoded` identifies them; the activity is `scanAtCanonical`
(never `coordinateEquiv`). -/

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
open Paper2.TemplateStep (r1)

/-- The loop bank carries the scheduled encodings of the pair. -/
theorem bankL_pair (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (r K : ℕ)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (ParameterizedCanonicalSource.restorationWidth L)]
    [NeZero (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ)]
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ) K)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ) K) :
    bankL g r K x y (jC (r1 RequestSelect.Xc)) =
      (scheduledCarrierCodecs g.vertices g.edges.length L Δ γ K).1.encode x ∧
    bankL g r K x y (jC (r1 RequestSelect.Yc)) =
      (scheduledCarrierCodecs g.vertices g.edges.length L Δ γ K).2.encode y := ⟨rfl, rfl⟩

theorem seed_join_coded (L Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)]
    [NeZero (ParameterizedCanonicalSource.restorationWidth L)]
    [NeZero (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ)]
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) *
      ParameterizedCanonicalSource.rep L g.edges.length)
    (K : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ) K)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ) K) :
    let w := ParameterizedCanonicalSource.restorationWidth L
    let Q := ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ
    let r := ParameterizedCanonicalSource.rep L g.edges.length
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn
      (NeZero.pos w) (NeZero.pos Q)
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by have := SourceProfiles.width_ge_four L; omega) hq
    let sd := RecursiveEntries.seedRequest activity ξ K x y
    ∃ t ≤ K * (loopBd g hg (SourceProfiles.width_ge_four L) r hq ξ K x y + 2) + 1 +
        (9 * LookupSeed.width L + 13) + 1, ∃ v, ∃ b : Bool,
      ((advance entryProg)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl ())),
          (((none : Option Bool), bodyCtl), (SeedEntryMachine.readInitial, (none : Option Bool))),
          bankL g r K x y⟩ : TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, v, Function.update
          (bankL (n := g.vertices) (p := LookupSeed.width L) (s := width L)
            (q₁ := width L - 2) (q₂ := outerWidth L) (w := w) (Q := Q) g r 0 sd.1 sd.2) ansC [b]⟩ ∧
      CodedEntryEvaluatorScratch.codedCanonicalEntry L Δ γ (CanonicalEdgeTape.graphEdge g hg) hn hq K
        ((scheduledCarrierCodecs g.vertices g.edges.length L Δ γ K).1.encode x)
        ((scheduledCarrierCodecs g.vertices g.edges.length L Δ γ K).2.encode y) = some b := by
  intro w Q r ξ activity sd
  obtain ⟨t, ht, v, hrun⟩ := seed_join_canonical L w Q r g hg hn (NeZero.pos w) (NeZero.pos Q) hq
    K x y
  exact ⟨t, ht, v, _, hrun,
    CodedEntryEvaluatorScratch.codedCanonicalEntry_encoded L Δ γ (CanonicalEdgeTape.graphEdge g hg)
      hn hq K x y⟩

end

#print axioms bankL_pair
#print axioms seed_join_coded

end Paper2.RLoop
