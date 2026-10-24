import EthInapproximability.CurrentPaper.ConcreteOutflow
import EthInapproximability.CurrentPaper.ConcreteReferenceErrors

/-!
# The complete row-count contradiction for the literal outer interlace

Source: frozen v8 `A-stage4-details.tex`, "The total row count" and
`eq:paper-scale-aligned-dense`.  The intermediate assembly lemma below keeps
the separately proved terminal-transfer estimate visible.  All other local
estimates, the assignment budget and the complete-node Kraft bound are derived
from actual inputs; no abstract flow certificate is introduced.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteGlobalLower

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace Workspace.Types.Protocol
open Parameters Construction JointTransfer ConcreteRouting ConcreteGlobalClosure
open ConcreteGlobalAssignment ConcreteOutflow ProtocolFrontier ProductExtraction
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction
open EthInapproximability.ParameterizedNP.DenseWeightedCount

/-- A row cannot both leave its owner's node and arrive at that same node. -/
theorem transferTo_self_empty {X Coord Node : Type*} [DecidableEq X]
    [DecidableEq Coord] [DecidableEq Node]
    (rows : Finset X) (origin : X → Coord) (dest : X → Node)
    (owner : Coord → Node) (j : Coord) :
    RoutedClosure.transferTo rows origin dest owner j j = ∅ := by
  ext x
  simp only [RoutedClosure.transferTo, GlobalCount.outgoing,
    Finset.mem_filter, Finset.notMem_empty, iff_false]
  tauto

variable (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
  {Y : Type} [Fintype Y] [Nonempty Y] (R : Fin i.rows → Y → Bool)
  (nv nb : ℕ) (hv : 0 < nv) (hb : 0 < nb)
  (hraw : 1000 * ((nv + nb) * i.rows) ≤ bins i * labelCount i)
  (order : ItemOrder nv nb)
  (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
  (cap : ∀ α, (activeItems vectors α).card ≤ bins i)

include hc hv hb hraw

set_option maxHeartbeats 1600000 in
/-- Assembly at the literal reference assignment. The remaining transfer
premise is stated on actual additional rows, not a synthetic mass array. -/
theorem contradiction_at_assignment
    (P : Protocol (RoutingRow i Y) (RoutingCol i nv nb) Bool)
    (A : Finset (RoutingRow i Y)) (S : Finset (RoutingCol i nv nb))
    (E J : Finset (Fin (outerWidth i))) (owner : Fin (outerWidth i) → List Bool)
    (hE : E.card ≤ exceptionalBudget i) (hdis : Disjoint E J)
    (hinj : Set.InjOn owner J)
    (hsingle : ∀ Q : Finset (Fin (outerWidth i)), Q.card = 1 → Disjoint E Q →
      (1 - (columnTolerance i : ℚ) : ℝ) *
          (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ^
            Q.card ≤ (projection Q S).card)
    (howner : ∀ j ∈ J, owner j ∈ nodes P (outerExponent i) A ∧
      (owner j).length = outerExponent i ∧
      ((retainedReference A (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter
        fun z => rowStop (outerExponent i) (completeNoBob (outerExponent i) P) z ≠
          owner j).card < (outerWidth i - 1) * referenceFloor i Y)
    (hJ : (outerWidth i : ℝ) - E.card / (1 - (9 / 16 : ℝ)) ≤ (J.card : ℝ))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ A.card)
    (hS : (retainedFraction i : ℚ) *
      (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ^
        outerWidth i ≤ S.card)
    (h1 : i.cost + firstExponent i ≤ Dfamily
      (interlaceFun (Function.swap (firstMatrix R (firstExponent i) (bins i))) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 5)))
    (h2 : i.cost + firstExponent i - 1 ≤ Dfamily
      (interlaceFun (Function.swap (firstMatrix R (firstExponent i) (bins i))) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 10)))
    (hN : ∀ U : Finset (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y),
      ∀ V : Finset (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)),
      (1 - ((rowTolerance i : ℚ) : ℝ)) *
        Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ U.card →
      (1 - ((columnTolerance i : ℚ) : ℝ)) *
        Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) ≤ V.card →
      certificateCost i ≤ D (subgame
        (protectedMatrix R (firstExponent i) (bins i) (secondWidth i) (labelCount i)
          nv nb (bins_pos i) (actualFamily i ha) order vectors cap) U V))
    (hP : ∀ z ∈ A, ∀ y ∈ S,
      P.eval z y = routingGame i ha R nv nb order vectors cap z y)
    (hcost : P.cost ≤ certificateCost i + outerExponent i - 1)
    (htransfer : ∀ j ∈ J, GlobalCount.mass
      (Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y))
      (GlobalCount.transferred
        (A.filter fun z => z.2 ∈ diagonalRows (firstExponent i) (bins i) (secondWidth i))
        Prod.fst (rowStop (outerExponent i) (completeNoBob (outerExponent i) P)) J owner j) ≤
        3 * rowTolerance i / 40) : False := by
  let m := Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y)
  let additional := A.filter fun z =>
    z.2 ∈ diagonalRows (firstExponent i) (bins i) (secondWidth i)
  let dest := rowStop (outerExponent i) (completeNoBob (outerExponent i) P)
  have hm : 0 < m := (physicalReferenceCount_pos i Y).trans_le (Finset.card_le_univ _)
  have hJrat : (outerWidth i : ℚ) -
      (exceptionalBudget i : ℚ) / (1 - (9 / 16 : ℚ)) ≤ (J.card : ℚ) := by
    have hJ0 : (outerWidth i : ℚ) - (E.card : ℚ) / (1 - (9 / 16 : ℚ)) ≤ J.card := by
      have hh : (7 : ℝ) * outerWidth i - 16 * E.card ≤ 7 * J.card := by
        norm_num at hJ
        linarith
      have hh' : (7 : ℚ) * outerWidth i - 16 * E.card ≤ 7 * J.card := by exact_mod_cast hh
      norm_num
      linarith
    have hE0 : (E.card : ℚ) ≤ exceptionalBudget i := by exact_mod_cast hE
    have hh := div_le_div_of_nonneg_right hE0 (by norm_num : (0 : ℚ) ≤ 1 - 9 / 16)
    linarith
  apply GlobalCount.global_count_contradiction additional Prod.fst dest
    (nodes P (outerExponent i) A) J owner
    (fun p => (stoppingCapacity (outerExponent i) p.length : ℚ)) m
    (outerWidth i : ℚ) (rowTolerance i) (capacityCoefficient i)
    ((exceptionalBudget i : ℚ) / (1 - (9 / 16 : ℚ)))
    hm (rowTolerance_pos i hc) (capacityCoefficient_nonneg i)
  · exact fun z hz => destination_mem P (outerExponent i) A (Finset.mem_filter.mp hz).1
  · exact fun j hj => (howner j hj).1
  · exact hinj
  · intro j hj
    simp only [stoppingCapacity, (howner j hj).2.1, Nat.sub_self, pow_zero, Nat.cast_one]
  · simpa only [outerWidth, Nat.cast_pow, Nat.cast_ofNat] using
      nodes_kraft_rat P (outerExponent i) A
  · exact hJrat
  · intro j hj
    have hd : Disjoint E ({j} : Finset (Fin (outerWidth i))) := by
      apply Finset.disjoint_left.mpr
      intro k hk he
      have hkj := Finset.mem_singleton.mp he
      exact Finset.disjoint_left.mp hdis hk (hkj.symm ▸ hj)
    have hs := hsingle {j} (by simp) hd
    simp only [Finset.card_singleton, pow_one] at hs
    apply physical_outflow i hc ha Y _ _ P A S owner j hA ?_ hP hcost
      (howner j hj).1 (howner j hj).2.1 (howner j hj).2.2 hN
    convert hs using 1
    congr 2
    ext f
    simp only [projection, Finset.mem_image]
  · exact htransfer
  · intro p hp
    have hpnode := (Finset.mem_sdiff.mp hp).1
    exact (all_nodes_receiving_capacity i hc ha R nv nb hv hb hraw order vectors cap
      P A S J hS h1 h2 hP hcost p hpnode).le
  · exact aggregate_capacity_gate i hc

end EthInapproximability.CurrentPaper.ConcreteGlobalLower
