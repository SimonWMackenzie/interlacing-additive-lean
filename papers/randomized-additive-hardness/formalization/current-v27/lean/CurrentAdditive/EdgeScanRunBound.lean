import CurrentAdditive.EdgeScanFuel

/-! The fixed physical edge-scan controller inherits the proved cubic
bound for its actual prepared input bank. This preserves its literal exit
banks, rather than substituting a semantic evaluator for the controller. -/

namespace CurrentAdditive.LiteralEdgeScanFuel

noncomputable section

open Paper2 Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open LiteralEdgeScanJoin

theorem join_false_cubic (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool)
    (h : ¬ (0 < g.edges.length ∧ a / r / g.edges.length = ig)) :
    ∃ t ≤ 1000*(bankBits g a r ig xv kb+1)^3, ∃ c,
      ((advance full)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel .start))),
          (testCtl, ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))),
          W0 g a r ig xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, Function.update (Function.update (W1 g a r ig xv kb) ansC []) actC [false]⟩ := by
  obtain ⟨t, ht, c, hc⟩ := join_false g a r ig xv kb h
  have hf := falseFuel_le g a r ig xv
  rw [envelope_eq_bank g a r ig xv kb] at hf
  refine ⟨t, ?_, c, hc⟩
  change t ≤ falseFuel g a r ig at ht
  omega

theorem join_true_cubic (g : EncodedGraph.Graph) (hg : g.Valid)
    (a r ig xv : ℕ) (kb : Bool)
    (h : 0 < g.edges.length ∧ a / r / g.edges.length = ig) :
    let e : Fin g.edges.length := ⟨a / r % g.edges.length, Nat.mod_lt _ h.1⟩
    ∃ t ≤ 1000*(bankBits g a r ig xv kb+1)^3, ∃ c,
      ((advance full)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel .start))),
          (testCtl, ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))),
          W0 g a r ig xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, Wtrue g hg a r ig xv kb e⟩ := by
  intro e
  obtain ⟨t, ht, c, hc⟩ := join_true g hg a r ig xv kb h
  have hf := trueFuel_le g hg a r ig xv e
  rw [envelope_eq_bank g a r ig xv kb] at hf
  refine ⟨t, ?_, c, hc⟩
  change t ≤ trueFuel g hg a r ig xv e at ht
  omega

def scanExit (g : EncodedGraph.Graph) (hg : g.Valid)
    (a r ig xv : ℕ) (kb : Bool) : JJ → List Bool :=
  if h : 0 < g.edges.length ∧ a / r / g.edges.length = ig then
    Wtrue g hg a r ig xv kb ⟨a / r % g.edges.length, Nat.mod_lt _ h.1⟩
  else
    Function.update (Function.update (W1 g a r ig xv kb) ansC []) actC [false]

theorem join_cubic (g : EncodedGraph.Graph) (hg : g.Valid)
    (a r ig xv : ℕ) (kb : Bool) :
    ∃ t ≤ 1000*(bankBits g a r ig xv kb+1)^3, ∃ c,
      ((advance full)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel .start))),
          (testCtl, ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))),
          W0 g a r ig xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, scanExit g hg a r ig xv kb⟩ := by
  by_cases h : 0 < g.edges.length ∧ a / r / g.edges.length = ig
  · simpa only [scanExit, dif_pos h] using join_true_cubic g hg a r ig xv kb h
  · simpa only [scanExit, dif_neg h] using join_false_cubic g a r ig xv kb h

theorem join_public (g : EncodedGraph.Graph) (hg : g.Valid) (s q₂ : ℕ)
    (a : Fin q₂) (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (kb : Bool) :
    let r := q₂/CurrentAdditive.EdgeSource.sourceQ0 (Fin (4*s)) (Fin g.edges.length)
    let xv := CanonicalEndpointRankBridge.itemValue z
    ∃ t ≤ 1000*(publicEnvelope g s q₂)^3, ∃ c,
      ((advance full)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel .start))),
          (testCtl, ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))),
          W0 g a.val r ig.val xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, scanExit g hg a.val r ig.val xv kb⟩ := by
  intro r xv
  obtain ⟨t, ht, c, hc⟩ := join_cubic g hg a.val r ig.val xv kb
  have henv := envelope_le_public g s q₂ a ig z
  have hbound : 1000*(bankBits g a.val r ig.val xv kb+1)^3 ≤
      1000*(publicEnvelope g s q₂)^3 := by
    rw [← envelope_eq_bank]
    gcongr
  exact ⟨t, ht.trans hbound, c, hc⟩

end
end CurrentAdditive.LiteralEdgeScanFuel
