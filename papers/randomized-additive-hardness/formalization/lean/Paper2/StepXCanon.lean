import Paper2.TemplateStepX

/-! Unit 3, segment (1): discharge of the fixed-tail premise `hfix` of
`TemplateStepX.source_stepX` (and `SrcX.srcX_run`) at the canonical widths
`p = LookupSeed.width L`, `s = width L`, `q₁ = width L - 2`,
`q₂ = outerWidth L` with the canonical default tails
`CanonicalDefaultSource.canonicalDefaultTails` (the tail family and the
activity `scanAtCanonical` of `CodedEntryEvaluatorScratch.codedCanonicalEntry`),
by the frozen owner-5 `SrcF.fixed_source_value` (itself the admitted
`canonical_tail_encoded`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.StepXCanon

noncomputable section

open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix SourceProfileParameters
open Paper2.CanonicalDefaultWordScratch (words)

/-- `hfix` at the canonical widths and tails, for the activity `scanAtCanonical`. -/
theorem canonical_hfix (L w Q r : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q) [NeZero (width L)]
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (k : ℕ) (i : SourceConstruction.Items (width L) (Fin g.vertices)) :
    ∀ js : Fin (width L) → OuterColumn (width L - 2) (outerWidth L) (width L)
      (Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
        (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
        (outerWidth L) w Q k),
      (defaultCarrierCodecs g.vertices (LookupSeed.width L) (width L) (width L - 2)
        (outerWidth L) w Q k).2.encode
        (sourceColumn (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
          (by have := SourceProfiles.width_ge_four L; omega) hq) i
          (forgetTag (CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn hw hQ k)
            (.fixedTail js))) =
      (words (LookupSeed.width L) (width L) (width L - 2) (outerWidth L) w Q k).2 :=
  fun js => SrcF.fixed_source_value L g.vertices w Q hn hw hQ k _ i js

/-- Instantiation check: `source_stepX` at the canonical widths and tails with
`hfix` discharged (the application elaborates; no premise on the fixed tag remains). -/
example (L w Q r : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hn : 0 < g.vertices) (hw : 0 < w) (hQ : 0 < Q)
    [NeZero (width L)] [NeZero (width L - 2)] [NeZero (outerWidth L)] [NeZero w] [NeZero Q]
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) (Fin g.edges.length) * r)
    (k : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q (k + 1))
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q (k + 1))
    (i : SourceConstruction.Items (width L) (Fin g.vertices))
    (uu : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (width L) (Fin g.vertices)) (width L) (width L - 2)
      (outerWidth L) w Q k)
    (hraw : y.2 (x y.1).1 = .inr (i, uu)) : True := by
  have _h := TemplateStepX.source_stepX g hg (by unfold LookupSeed.width; positivity)
    (SourceProfiles.width_ge_four L) r hq k
    (CanonicalDefaultSource.canonicalDefaultTails L g.vertices w Q hn hw hQ) x y i uu hraw
    (canonical_hfix L w Q r g hg hn hw hQ hq k i)
  trivial

end

#print axioms canonical_hfix

end Paper2.StepXCanon
