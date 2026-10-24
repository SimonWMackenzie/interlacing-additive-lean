import CurrentAdditive.QuarticSamplerOutputSplit
import CurrentAdditive.GenericGraphEntrySpec

/-! The v27 scheduled table and the fixed physical graph-entry machine
refer to the same recursive matrix on every successful sampled tape. The
abort branch is the literal all-zero table and requires no entry calls. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.GenericQuarticPhysical

open EthInapproximability.CurrentPaper
open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor

abbrev W (L : ℕ) := CurrentAdditive.RandomizedSchedule.width27 L
abbrev Cover (g : EncodedGraph.Graph) (L Δ : ℕ) (γ : ℚ) :=
  CurrentAdditive.RandomizedSchedule.Q27
    (V := Fin g.vertices) (E := Fin g.edges.length) L γ Δ
abbrev Rep (g : EncodedGraph.Graph) (L : ℕ) :=
  SourceRepetitionScratch.sourceRep L (Fin g.edges.length)

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (W L) :=
  ⟨by unfold W CurrentAdditive.RandomizedSchedule.width27; positivity⟩
local instance (g : EncodedGraph.Graph) (L Δ : ℕ) (γ : ℚ) :
    NeZero (Cover g L Δ γ) :=
  ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩

theorem scheduled_graph_machine_split (g : EncodedGraph.Graph) (hg : g.Valid)
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
      hn (by unfold W CurrentAdditive.RandomizedSchedule.width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
    (∃ rows cols,
      (scheduledTable27 hn (CanonicalEdgeTape.graphEdge g hg)
        L Δ γ k hc bits).matrix =
        RecursiveEntries.table (LookupSeed.matrix (LookupSeed.width L))
          activity ξ k rows cols ∧
      ∀ i j,
        GenericGraphEntrySpec.EntrySpec
          L (W L) (Cover g L Δ γ) (Rep g L)
          g hg hn
          (by unfold W CurrentAdditive.RandomizedSchedule.width27; positivity)
          (by exact RestorationPublicQScratch.publicQ_pos _ _)
          (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
            L (Fin g.edges.length) hc.1)
          (LookupSeed.matrix (LookupSeed.width L)) k (rows i) (cols j)) ∨
      (scheduledTable27 hn (CanonicalEdgeTape.graphEdge g hg)
        L Δ γ k hc bits).matrix = (fun _ _ => false) := by
  intro activity ξ
  rcases GenericQuarticOutput.scheduled27_table_split hn
      (CanonicalEdgeTape.graphEdge g hg) L Δ γ k hc bits with
    ⟨rows, cols, htab⟩ | habort
  · left
    refine ⟨rows, cols, htab, ?_⟩
    intro i j
    exact GenericGraphEntrySpec.checked
      L (W L) (Cover g L Δ γ) (Rep g L)
      g hg hn
      (by unfold W CurrentAdditive.RandomizedSchedule.width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin g.edges.length) hc.1)
      (LookupSeed.matrix (LookupSeed.width L)) k (rows i) (cols j)
  · exact Or.inr habort

#print axioms scheduled_graph_machine_split

end Paper2.GenericQuarticPhysical
