import EthInapproximability.CurrentPaper.ConcreteGlobalLower
import EthInapproximability.CurrentPaper.TerminalTransferParameters

/-!
# Near-full lower bound for the literal outer interlace

Source: frozen v8 `A-stage4-details.tex`, `eq:paper-scale-aligned-dense`.
All three parts of the global count are derived here from the first, second,
and protected one-copy profiles. In particular neither transfer nor receiving
capacity nor a reference assignment is a premise of the theorem.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteOuterLower

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace Workspace.Types.Protocol
open Parameters Construction JointTransfer ConcreteRouting ConcreteGlobalClosure
open ConcreteGlobalAssignment ConcreteGlobalLower ProtocolFrontier ProductExtraction
open ConcreteReferenceErrors TerminalTransferParameters
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction

set_option maxHeartbeats 2400000

variable (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    (hlarge : 2 ^ 24 ≤ i.sourceConstant)
    {Y : Type} [Fintype Y] [Nonempty Y] (R : Fin i.rows → Y → Bool)
    (nv nb : ℕ) (hv : 0 < nv) (hb : 0 < nb)
    (hraw : 1000 * ((nv + nb) * i.rows) ≤ bins i * labelCount i)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i)

variable
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
    (hsecond : i.cost + firstExponent i + secondExponent i ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix R (firstExponent i) (bins i)
        (secondWidth i) (labelCount i) (actualFamily i ha))) 1)
      (bracketGE (Fin (labelCount i)) (SecondRows (firstExponent i) (bins i) (secondWidth i) Y)
        1 ((2 : ℝ) ^ (-(secondDepth i : ℝ))) (3 / 5)))
    (hsecondHalf : i.cost + firstExponent i + secondExponent i - 1 ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix R (firstExponent i) (bins i)
        (secondWidth i) (labelCount i) (actualFamily i ha))) 1)
      (bracketGE (Fin (labelCount i)) (SecondRows (firstExponent i) (bins i) (secondWidth i) Y)
        1 ((2 : ℝ) ^ (-(secondDepth i : ℝ))) (3 / 10)))
    (hreference : certificateCost i - 1 ≤ Dfamily
      (interlaceFun (fun a : referenceRows (Y := Y)
          (firstExponent i) (bins i) (secondWidth i) =>
        protectedMatrix R (firstExponent i) (bins i) (secondWidth i) (labelCount i)
          nv nb (bins_pos i) (actualFamily i ha) order vectors cap a.val) 1)
      (bracketGE (referenceRows (Y := Y) (firstExponent i) (bins i) (secondWidth i))
        (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 5)))
    (hreferenceHalf : certificateCost i - 2 ≤ Dfamily
      (interlaceFun (fun a : referenceRows (Y := Y)
          (firstExponent i) (bins i) (secondWidth i) =>
        protectedMatrix R (firstExponent i) (bins i) (secondWidth i) (labelCount i)
          nv nb (bins_pos i) (actualFamily i ha) order vectors cap a.val) 1)
      (bracketGE (referenceRows (Y := Y) (firstExponent i) (bins i) (secondWidth i))
        (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 10)))
    (hN : ∀ U : Finset (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y),
      ∀ V : Finset (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)),
      (1 - ((rowTolerance i : ℚ) : ℝ)) *
        Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ U.card →
      (1 - ((columnTolerance i : ℚ) : ℝ)) *
        Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) ≤ V.card →
      certificateCost i ≤ D (subgame
        (protectedMatrix R (firstExponent i) (bins i) (secondWidth i) (labelCount i)
          nv nb (bins_pos i) (actualFamily i ha) order vectors cap) U V))

include hc hlarge hv hb hraw h1 h2 hsecond hsecondHalf hreference hreferenceHalf hN

/-- Every actual protocol on the retained rectangle pays the full aligned
cost. The only lower-bound inputs are earlier one-copy profiles. -/
theorem protocol_lower
    (P : Protocol (RoutingRow i Y) (RoutingCol i nv nb) Bool)
    (A : Finset (RoutingRow i Y)) (S : Finset (RoutingCol i nv nb))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ A.card)
    (hS : (retainedFraction i : ℚ) *
      (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ^
        outerWidth i ≤ S.card)
    (hP : ∀ z ∈ A, ∀ y ∈ S,
      P.eval z y = routingGame i ha R nv nb order vectors cap z y) :
    certificateCost i + outerExponent i ≤ P.cost := by
  by_contra hn
  have hcost : P.cost ≤ certificateCost i + outerExponent i - 1 := by omega
  let N := protectedMatrix R (firstExponent i) (bins i) (secondWidth i) (labelCount i)
    nv nb (bins_pos i) (actualFamily i ha) order vectors cap
  let ref := referenceRows (Y := Y) (firstExponent i) (bins i) (secondWidth i)
  let additional := A.filter fun z =>
    z.2 ∈ diagonalRows (firstExponent i) (bins i) (secondWidth i)
  let dest := rowStop (outerExponent i) (completeNoBob (outerExponent i) P)
  let m := Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y)
  have hL : 0 < labelCount i := lt_of_lt_of_le
    (Nat.mul_pos (firstWidth_pos i) (by have := ha.1; omega))
    (ParameterGates.actualFamily_size_ge_alphabet i hc ha)
  letI : Nonempty (Fin i.rows) := Fin.pos_iff_nonempty.mp (by have := ha.1; omega)
  letI : Nonempty (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) := by
    apply Fintype.card_pos_iff.mp
    have hh := template_bin_card
      (X := Fin i.rows) (bins i) (labelCount i) nv nb ⟨0, bins_pos i⟩
    have hp := template_labels_pos
      (X := Fin i.rows) (bins i) (labelCount i) nv nb (bins_pos i) hL hv hb
    have hu := Finset.card_le_univ
      (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb ⟨0, bins_pos i⟩)
    rw [hh] at hu
    exact (Nat.mul_pos hL hp).trans_le hu
  obtain ⟨E, J, owner, hE, hdis, hinj, hsingle, hpair, howner, hJ⟩ :=
    physical_assignment_from_profiles i hc ha Y _ N P A S hreference hreferenceHalf
      hA hS hP hcost
  have hsum : (∑ j ∈ J, epsilon A ref dest owner j) ≤ rowTolerance i / (8 * (91 / 92)) :=
    physical_error_sum i hc ha Y A dest owner J hA (fun j hj => (howner j hj).2.2)
  have htransfer (j : Fin (outerWidth i)) (hj : j ∈ J) :
      GlobalCount.mass m (GlobalCount.transferred additional Prod.fst dest J owner j) ≤
        3 * rowTolerance i / 40 := by
    apply RoutedClosure.transfer_mass_bound additional Prod.fst dest owner J hinj j m
      (outerWidth i) (1 / 184) (lambda i) (rowTolerance i) (91 / 92)
      (epsilon A ref dest owner)
      (by norm_num) (lambda_nonneg i) (rowTolerance_pos i hc).le (by norm_num)
      (by simpa only [Fintype.card_fin] using Finset.card_le_univ J)
      (by norm_num) hsum (lambda_sum_gate i hc)
    intro k hk
    by_cases hjk : j = k
    · subst k
      rw [transferTo_self_empty]
      simp only [GlobalCount.mass, Finset.card_empty, Nat.cast_zero, zero_div]
      exact mul_nonneg (by norm_num)
        (add_nonneg (lambda_nonneg i) (epsilon_nonneg A ref dest owner j))
    have hdSingle : Disjoint E ({k} : Finset (Fin (outerWidth i))) := by
      apply Finset.disjoint_left.mpr
      intro z hz he
      exact Finset.disjoint_left.mp hdis hz ((Finset.mem_singleton.mp he).symm ▸ hk)
    have hdPair : Disjoint E ({k, j} : Finset (Fin (outerWidth i))) := by
      apply Finset.disjoint_left.mpr
      intro z hz he
      rcases Finset.mem_insert.mp he with he | he
      · exact Finset.disjoint_left.mp hdis hz (he.symm ▸ hk)
      · exact Finset.disjoint_left.mp hdis hz ((Finset.mem_singleton.mp he).symm ▸ hj)
    have hs := hsingle {k} (by simp) hdSingle
    have hp := hpair {k, j} (by simp [Ne.symm hjk]) hdPair
    simp only [Finset.card_singleton, pow_one] at hs
    rw [Finset.card_pair (Ne.symm hjk)] at hp
    apply parameters_terminal_transfer i hc ha hlarge R nv nb hv hb hraw order vectors cap
      h1 h2 hsecond hsecondHalf P A S hP hcost owner J j k hjk hk
      (howner k hk).1 (howner k hk).2.1 hsum
    · convert hs using 1
      congr 2
      ext f
      simp only [projection, Finset.mem_image]
    · convert hp using 1
      congr 2
      ext f
      simp only [projection, Finset.mem_image]
  apply contradiction_at_assignment i hc ha R nv nb hv hb hraw order vectors cap
    P A S E J owner hE hdis hinj ?_ howner hJ hA hS h1 h2 hN hP hcost htransfer
  intro Q hQ hd
  convert hsingle Q hQ hd using 1
  congr 2
  ext f
  simp only [projection, Finset.mem_image]

/-- The exact retained-submatrix statement used by scale alignment. -/
theorem subgame_lower
    (A : Finset (RoutingRow i Y)) (S : Finset (RoutingCol i nv nb))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ A.card)
    (hS : (retainedFraction i : ℚ) *
      (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ^
        outerWidth i ≤ S.card) :
    certificateCost i + outerExponent i ≤
      D (subgame (routingGame i ha R nv nb order vectors cap) A S) := by
  have hm : 0 < Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) :=
    (physicalReferenceCount_pos i Y).trans_le (Finset.card_le_univ _)
  have hδ : (columnLoss i : ℝ) < 1 := by
    have hh := (Rat.cast_lt (K := ℝ)).2 (columnLoss_lt i hc)
    norm_num at hh
    linarith
  have hApos : (0 : ℝ) < A.card := lt_of_lt_of_le
    (mul_pos (mul_pos (by linarith) (by exact_mod_cast outerWidth_pos i))
      (by exact_mod_cast hm)) hA
  have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hL : 0 < labelCount i := lt_of_lt_of_le
    (Nat.mul_pos (firstWidth_pos i) (by have := ha.1; omega))
    (ParameterGates.actualFamily_size_ge_alphabet i hc ha)
  letI : Nonempty (Fin i.rows) := Fin.pos_iff_nonempty.mp (by have := ha.1; omega)
  have hZ : 0 < Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) := by
    have hh := template_bin_card (X := Fin i.rows)
      (bins i) (labelCount i) nv nb ⟨0, bins_pos i⟩
    have hp := template_labels_pos (X := Fin i.rows)
      (bins i) (labelCount i) nv nb (bins_pos i) hL hv hb
    have hu := Finset.card_le_univ
      (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb ⟨0, bins_pos i⟩)
    rw [hh] at hu
    exact (Nat.mul_pos hL hp).trans_le hu
  have hθ : (0 : ℝ) < (retainedFraction i : ℝ) := by exact_mod_cast retainedFraction_pos i
  have hSpos : (0 : ℝ) < S.card := lt_of_lt_of_le
    (mul_pos hθ (pow_pos (by exact_mod_cast hZ) _)) hS
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSpos)
  let F := routingGame i ha R nv nb order vectors cap
  obtain ⟨P, hPc, hP⟩ := (Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty
    (subgame F A S)) : D (subgame F A S) ∈ AchievableCosts (subgame F A S))
  let Q := Protocol.extendSub A S hAne hSne P
  have hQ : ∀ z ∈ A, ∀ y ∈ S, Q.eval z y = F z y := by
    intro z hz y hy
    rw [show Q = Protocol.extendSub A S hAne hSne P from rfl,
      Protocol.eval_extendSub A S hAne hSne P ⟨z, hz⟩ ⟨y, hy⟩]
    exact hP ⟨z, hz⟩ ⟨y, hy⟩
  have hlower := protocol_lower i hc ha hlarge R nv nb hv hb hraw order vectors cap
    h1 h2 hsecond hsecondHalf hreference hreferenceHalf hN Q A S hA hS hQ
  simpa only [Q, Protocol.cost_extendSub, hPc] using hlower

end EthInapproximability.CurrentPaper.ConcreteOuterLower
