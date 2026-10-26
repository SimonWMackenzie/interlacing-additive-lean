import CurrentAdditive.QuarticFaithfulSampledEntries
import Paper2.RLoopCanon

/-! Source-faithful v27 graph table: every tape has actual sampled labels,
and each of their recursive entries has the inherited clocked graph-loop
plus direct seed-coordinate machine certificate. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.GenericQuarticFaithful

open EthInapproximability.CurrentPaper
open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

abbrev W (L : ℕ) := width27 L
abbrev Cover (g : EncodedGraph.Graph) (L Δ : ℕ) (γ : ℚ) :=
  Q27 (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ
abbrev Rep (g : EncodedGraph.Graph) (L : ℕ) :=
  SourceRepetitionScratch.sourceRep L (Fin g.edges.length)

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (W L) :=
  ⟨by unfold W width27; positivity⟩
local instance (g : EncodedGraph.Graph) (L Δ : ℕ) (γ : ℚ) :
    NeZero (Cover g L Δ γ) :=
  ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩

theorem graph_table_seed_machine (g : EncodedGraph.Graph) (hg : g.Valid)
    [NeZero g.vertices] (hn : 0 < g.vertices)
    (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin g.vertices)
      (width L) (width L - 2) (outerWidth L)
      (W L) (Cover g L Δ γ) (LookupSeed.width L) k
      (rows27 g.vertices g.edges.length L Δ γ k)
      (cols27 g.vertices g.edges.length L Δ γ k)) :
    let activity := SourceActiveRank.scanAtCanonical
      (CanonicalEdgeTape.graphEdge g hg)
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin g.edges.length) hc.1)
    let ξ := CanonicalDefaultSource.canonicalDefaultTails
      L g.vertices (W L) (Cover g L Δ γ)
      hn (by unfold W width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
    ∃ rows cols,
      (table27Faithful hn (CanonicalEdgeTape.graphEdge g hg)
        L Δ γ k hc bits).matrix =
        RecursiveEntries.table (LookupSeed.matrix (LookupSeed.width L))
          activity ξ k rows cols ∧
      ∀ i j,
        (type_of% (Paper2.RLoop.seed_join_canonical
          L (W L) (Cover g L Δ γ) (Rep g L)
          g hg hn
          (by unfold W width27; positivity)
          (by exact RestorationPublicQScratch.publicQ_pos _ _)
          (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
            L (Fin g.edges.length) hc.1)
          k (rows i) (cols j))) ∧
        (table27Faithful hn (CanonicalEdgeTape.graphEdge g hg)
          L Δ γ k hc bits).matrix i j =
          RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
            activity ξ k (rows i) (cols j) := by
  intro activity ξ
  obtain ⟨rows, cols, htab⟩ := table27Faithful_sampled hn
    (CanonicalEdgeTape.graphEdge g hg) L Δ γ k hc bits
  refine ⟨rows, cols, htab, ?_⟩
  intro i j
  constructor
  · exact Paper2.RLoop.seed_join_canonical
      L (W L) (Cover g L Δ γ) (Rep g L)
      g hg hn
      (by unfold W width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin g.edges.length) hc.1)
      k (rows i) (cols j)
  · simpa only [RecursiveEntries.table, RecursiveEntries.evaluate_eq_matrix] using
      congrFun (congrFun htab i) j

#print axioms graph_table_seed_machine

end Paper2.GenericQuarticFaithful
