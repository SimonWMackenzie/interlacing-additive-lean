import Paper2.ScanJoin

/-! Unit 3, segment (1): value identity of the ONE physical scan program
`ScanJoin.full` with the production `SourceActiveRank.scanAtCanonical`, for the
public graph `g` (edge map `CanonicalEdgeTape.graphEdge g hg`, the same indexed
edge map the consumer `codedCanonicalEntry` receives), at every item
`(ig, z)` and every numeric canonical coordinate `a`, with the item operands
`itemValue z` and `z.isRight` (produced by `ItemOperands` from the actual
raw-row word).

* unselected (`¬ (0 < m ∧ a / r / 3 / m = ig)`): the scan is `none`, and the
  program halts with activity cell `[false]` (`ScanJoin.join_false`);
* selected: the program halts in `Wtrue`, whose activity cell holds `[act]`
  and whose rank cell holds `rk` marks, and the scan is
  `if act then some rk else none`. -/

namespace Paper2.ScanValue

open EthInapproximability.CurrentPaper
open SourceItems SourceActiveRank CanonicalSourceLabels
open CanonicalEndpointRankBridge CanonicalEndpointRankMachine

theorem scan_value_none {s r q₂ : ℕ} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hs : 3 ≤ s)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ig : Fin (4 * s)) (z : Fin g.vertices ⊕ Fin (s - 3)) (a : Fin q₂)
    (h : ¬ (0 < g.edges.length ∧ a.val / r / 3 / g.edges.length = ig.val)) :
    scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) hs hq (ig, z) a = none :=
  ScanCoordDecode.scan_none _ hs hq ig z a h

theorem scan_value_some {s r q₂ : ℕ} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hs : 3 ≤ s)
    (hq : q₂ = sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ig : Fin (4 * s)) (z : Fin g.vertices ⊕ Fin (s - 3)) (a : Fin q₂)
    (h : 0 < g.edges.length ∧ a.val / r / 3 / g.edges.length = ig.val) :
    let e : Fin g.edges.length := ⟨a.val / r / 3 % g.edges.length, Nat.mod_lt _ h.1⟩
    let W := ScanJoin.Wtrue g hg a.val r ig.val (itemValue z) z.isRight e
    ∃ act rk, W ScanJoin.actC = [act] ∧ W (.inr (.inr 3)) = List.replicate rk true ∧
      Option.map Fin.val (scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) hs hq (ig, z) a) =
        if act then some rk else none := by
  intro e W
  refine ⟨semanticActive (RankRun.kindOfNat (a.val / r % 3)) (RankRun.itemOfBool z.isRight)
      (CanonicalEdgeTape.graphEdge g hg e false).val
      (CanonicalEdgeTape.graphEdge g hg e true).val (itemValue z),
    semanticRank (RankRun.kindOfNat (a.val / r % 3)) (RankRun.itemOfBool z.isRight)
      (CanonicalEdgeTape.graphEdge g hg e false).val
      (CanonicalEdgeTape.graphEdge g hg e true).val (itemValue z),
    ScanJoin.Wtrue_act _ _ _ _ _ _ _ _, ScanJoin.Wtrue_rank _ _ _ _ _ _ _ _, ?_⟩
  have hbit : ScanTest.DT a.val r g.edges.length ig.val 13 = [true] := by
    show [decide (0 < g.edges.length ∧ a.val / r / 3 / g.edges.length = ig.val)] = [true]
    simp [h]
  have hv := (ScanTest.scan_test (CanonicalEdgeTape.graphEdge g hg) hs hq ig z a).2 h.1 hbit
  rw [hv]
  have hr := RankRun.rank_value (s := s) (CanonicalEdgeTape.graphEdge g hg) e z
    (a.val / r % 3) (Nat.mod_lt _ (by norm_num))
  rw [List.length_replicate] at hr
  exact hr.symm

#print axioms scan_value_none
#print axioms scan_value_some

end Paper2.ScanValue
