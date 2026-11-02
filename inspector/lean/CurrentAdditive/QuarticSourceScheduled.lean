import CurrentAdditive.QuarticClassBridge

/-! Every routed source graph beyond one explicit cutoff is on the scheduled
v27 branch. This includes routes of malformed original words. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.Unit4Shell.T10Finite
open _root_.CurrentAdditive.Eventual
open Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

theorem source_checks27_above
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc)) :
    ∀ Φ : ValidFormula,
      Bsrc.degreeBound * CurrentAdditive.QuarticSchedule.threshold27
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) ≤ Φ.val.variables →
      CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin (t10Graph Dsrc Bsrc Φ).vertices)
        (Edges := Fin (t10Graph Dsrc Bsrc Φ).edges.length)
        (Nat.clog 2 (t10Graph Dsrc Bsrc Φ).vertices)
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) := by
  let Δ := Bsrc.degreeBound
  let γ := sourceGap Dsrc Bsrc
  let T := CurrentAdditive.QuarticSchedule.threshold27 Δ γ
  intro Φ hlarge
  let g := t10Graph Dsrc Bsrc Φ
  let edge := CanonicalEdgeTape.graphEdge g (t10Graph_valid Dsrc Bsrc Φ)
  have hΔ : 0 < Δ := Bsrc.degreeBound_pos
  have hγ : 0 < γ := source_gap_pos Dsrc Bsrc
  obtain ⟨_, hNm, hinc, hdeg, _, _, _⟩ := t10_source Dsrc Bsrc Φ
  have hmn := (Paper2.Unit4Shell.T10Size.t45_relations Dsrc Bsrc Φ).2.1
  have hsize : T ≤ g.vertices := by
    dsimp only [T, Δ, g] at *
    nlinarith
  exact checks27_of_large (t10_vertices_pos Dsrc Bsrc Φ)
    edge Δ γ hγ hΔ hinc hdeg hsize

theorem source_checks27_large
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc)) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      N₀ ≤ Φ.val.variables →
      CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin (t10Graph Dsrc Bsrc Φ).vertices)
        (Edges := Fin (t10Graph Dsrc Bsrc Φ).edges.length)
        (Nat.clog 2 (t10Graph Dsrc Bsrc Φ).vertices)
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) :=
  ⟨Bsrc.degreeBound * CurrentAdditive.QuarticSchedule.threshold27
      Bsrc.degreeBound (sourceGap Dsrc Bsrc),
    source_checks27_above Dsrc Bsrc⟩

theorem source_checks27_routed_at
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1 / 12) (hE : EstimatesGrowingEventuallySelSq E c)
    (cs N₁ : ℕ)
    (hcut : cutN27 Dsrc Bsrc E c hc0 hc hE cs ≤ N₁)
    (x : List Bool) :
    let Φ := Paper2.AEth4.routedV (cs + 2) N₁
      ((cutN27_pos Dsrc Bsrc E c hc0 hc hE cs).trans hcut) x
    CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin (t10Graph Dsrc Bsrc Φ).vertices)
      (Edges := Fin (t10Graph Dsrc Bsrc Φ).edges.length)
      (Nat.clog 2 (t10Graph Dsrc Bsrc Φ).vertices)
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) := by
  intro Φ
  apply source_checks27_above
  exact ((cutN27_scheduled_threshold Dsrc Bsrc E c hc0 hc hE cs).trans
    hcut).trans (Paper2.AEth4.routed4_variables (cs + 2) N₁ x)

#print axioms source_checks27_above
#print axioms source_checks27_large
#print axioms source_checks27_routed_at

end Paper2.CurrentAdditive.QuarticClassEndpoint
