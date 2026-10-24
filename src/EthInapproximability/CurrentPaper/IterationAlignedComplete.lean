import EthInapproximability.CurrentPaper.ProtectedIterationBounds
import EthInapproximability.CurrentPaper.ConcreteOuterLower
import EthInapproximability.CurrentPaper.ConcreteAlignedProfiles

/-!
# Scale-aligned profiles from the original input and graph promises

Source: frozen v8 `A-stage4-details.tex`, `eq:paper-scale-aligned-dense`,
and `05-iteration.tex`, `thm:paper-finite-iteration`. The output profiles
are consequences of the actual preceding matrix and source graph, not
additional induction hypotheses.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.IterationAlignedComplete

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters Construction JointTransfer
open EthInapproximability.ParameterizedNP.GuardedSourceGraph

set_option maxHeartbeats 1600000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem source_constant_floor {c Δ : ℕ} {γ : ℚ} (hΔ : 0 < Δ)
    (hγ : 0 < γ) (hγone : γ ≤ 1) (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) :
    2 ^ 24 ≤ c := by
  have hΔone : (1 : ℚ) ≤ Δ := by exact_mod_cast hΔ
  have hm : (2 ^ 44 : ℚ) ≤ c := calc
    _ ≤ 2 ^ 44 * (Δ : ℚ) / γ := (le_div_iff₀ hγ).mpr (by nlinarith)
    _ ≤ c := hsource
  exact_mod_cast (show (2 ^ 24 : ℚ) ≤ c by norm_num at hm ⊢; linarith)

variable (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hc : 0 < c) (ha : Accepted (Iteration.parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)

include hc ha hf hcost hΔ hγ hγone hcommon hno hsource

theorem near_full
    (A : Finset (Fin (Parameters.outerWidth (Iteration.parameters G c b y n M)) ×
      Iteration.NRow G c b y n M))
    (S : Finset (Fin (Parameters.outerWidth (Iteration.parameters G c b y n M)) →
      Iteration.NCol G c b y n M))
    (hA : (1 - (columnLoss (Iteration.parameters G c b y n M) : ℝ)) *
      outerWidth (Iteration.parameters G c b y n M) *
      Fintype.card (Iteration.NRow G c b y n M) ≤ A.card)
    (hS : (retainedFraction (Iteration.parameters G c b y n M) : ℝ) *
      (Fintype.card (Iteration.NCol G c b y n M) : ℝ) ^
        outerWidth (Iteration.parameters G c b y n M) ≤ S.card) :
    certificateCost (Iteration.parameters G c b y n M) +
        outerExponent (Iteration.parameters G c b y n M) ≤
      D (subgame (interlaceFun (Iteration.protectedMatrix G c b y n M)
        (outerWidth (Iteration.parameters G c b y n M))) A S) := by
  classical
  let i := Iteration.parameters G c b y n M
  have hci : 0 < i.sourceConstant := hc
  have hfi : IsRobustAt M.entry i.incomingDepth := hf
  have hcosti : D M.entry = i.cost := hcost
  have hlarge : 2 ^ 24 ≤ i.sourceConstant := source_constant_floor hΔ hγ hγone hsource
  have hs : 4 ≤ bins i := Iteration.bins_ge_four G c b y n M
  have hv : 0 < GraphVectors.vertexCount V (bins i) := by
    unfold GraphVectors.vertexCount
    exact Nat.mul_pos (by omega) G.card_vertex_pos
  have hb : 0 < GraphVectors.auxiliaryCount (bins i) := by
    unfold GraphVectors.auxiliaryCount
    exact Nat.mul_pos (by omega) (by omega)
  have hvertices : Fintype.card V ≤ 2 * Fintype.card E :=
    G.card_vertex_le_two_mul_card_edge (fun v => (hcommon.2 v).1)
  have hraw := ConcreteRouting.actual_raw_source_count i hci ha (Fintype.card V) hvertices
  have hfirst := AmplificationFirstProfiles.scheduled_first_profiles M.entry i ha hfi
  rw [hcosti] at hfirst
  have hsecond := AmplificationInnerProfiles.scheduled_second_profiles i hci ha M.entry hfi hcosti
  have hsecondOne := hsecond.2.1.2.2.1
  have hsecondHalf := hsecond.2.1.2.2.2
  rw [hsecond.1] at hsecondOne hsecondHalf
  have href := ProtectedIterationDense.reference_profile G c b y n M hc ha hf hcost hvertices 0 (by omega)
  have hrefHalf := ProtectedIterationDense.reference_profile G c b y n M hc ha hf hcost hvertices 1 (by omega)
  have hC : certificateCost i = y + n + Iteration.baseOverhead G c b y n M + 1 := by
    simp only [certificateCost, Iteration.baseOverhead, Iteration.a,
      Iteration.stepParameters, i, Iteration.parameters, Nat.add_assoc]
  have href' : certificateCost i - 1 ≤
      Dfamily (interlaceFun
        (fun r : referenceRows (Y := Fin M.columns) (firstExponent i) (bins i) (secondWidth i) =>
          Iteration.protectedMatrix G c b y n M r.val) 1)
        (bracketGE (referenceRows (Y := Fin M.columns) (firstExponent i) (bins i) (secondWidth i))
          (Iteration.NCol G c b y n M) 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 5)) := by
    rw [hC]
    simpa only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, div_one] using href
  have hrefHalf' : certificateCost i - 2 ≤
      Dfamily (interlaceFun
        (fun r : referenceRows (Y := Fin M.columns) (firstExponent i) (bins i) (secondWidth i) =>
          Iteration.protectedMatrix G c b y n M r.val) 1)
        (bracketGE (referenceRows (Y := Fin M.columns) (firstExponent i) (bins i) (secondWidth i))
          (Iteration.NCol G c b y n M) 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 10)) := by
    have hsub : certificateCost i - 2 = y + n + Iteration.baseOverhead G c b y n M - 1 := by
      rw [hC]
      omega
    rw [hsub]
    simpa only [pow_one, show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num] using hrefHalf
  apply ConcreteOuterLower.subgame_lower i hci ha hlarge M.entry
    (GraphVectors.vertexCount V (bins i)) (GraphVectors.auxiliaryCount (bins i))
    hv hb hraw (GraphVectors.itemOrder G (bins i)) (GraphVectors.vectors G (bins i))
    (GraphVectors.supportCap G (show 3 ≤ bins i by omega))
    hfirst.2.1 hfirst.2.2 hsecondOne hsecondHalf href' hrefHalf' ?_ A S hA hS
  intro U W hU hW
  rw [hC]
  exact ProtectedIterationDense.subgame_lower G c b y n M hc ha hf hcost
    hΔ hγ hγone hcommon hno hsource U W hU hW

/-- The scale-aligned profiles are proved from the previous input matrix;
none of the four output conclusions is an assumption. -/
theorem aligned_profiles : Iteration.AlignedProfiles G c b y n M := by
  classical
  let i := Iteration.parameters G c b y n M
  let N := Iteration.protectedMatrix G c b y n M
  let Ref := referenceRows (Y := Fin M.columns)
    (firstExponent i) (bins i) (secondWidth i)
  let e : Ref ↪ Iteration.NRow G c b y n M :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hpos := ProtectedIterationDense.carrier_pos G c b y n M
  letI : Nonempty (Iteration.NRow G c b y n M) := Fintype.card_pos_iff.mp hpos.1
  letI : Nonempty (Iteration.NCol G c b y n M) := Fintype.card_pos_iff.mp hpos.2
  have hprop : (Fintype.card Ref : ℝ) =
      (91 / 92 : ℝ) * Fintype.card (Iteration.NRow G c b y n M) := by
    simpa only [Ref, Fintype.card_coe] using
      ProtectedDeletionGates.reference_count (Y := Fin M.columns)
        (firstExponent i) (bins i) (secondWidth i)
  have hRefpos : 0 < Fintype.card Ref := by
    have hp : (0 : ℝ) < Fintype.card Ref := by
      rw [hprop]
      exact mul_pos (by norm_num) (by exact_mod_cast hpos.1)
    exact_mod_cast hp
  letI : Nonempty Ref := Fintype.card_pos_iff.mp hRefpos
  have hvertices : Fintype.card V ≤ 2 * Fintype.card E :=
    G.card_vertex_le_two_mul_card_edge (fun v => (hcommon.2 v).1)
  have href := ProtectedIterationDense.reference_profile G c b y n M hc ha hf hcost hvertices 0 (by omega)
  have hrefHalf := ProtectedIterationDense.reference_profile G c b y n M hc ha hf hcost hvertices 1 (by omega)
  have hC : certificateCost i = y + n + Iteration.baseOverhead G c b y n M + 1 := by
    simp only [certificateCost, Iteration.baseOverhead, Iteration.a,
      Iteration.stepParameters, i, Iteration.parameters, Nat.add_assoc]
  have href' : certificateCost i - 1 ≤
      Dfamily (interlaceFun (fun r z => N (e r) z) 1)
        (bracketGE Ref (Iteration.NCol G c b y n M) 1
          ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 5)) := by
    rw [hC]
    simpa only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, div_one] using href
  have hrefHalf' : certificateCost i - 2 ≤
      Dfamily (interlaceFun (fun r z => N (e r) z) 1)
        (bracketGE Ref (Iteration.NCol G c b y n M) 1
          ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 10)) := by
    have hsub : certificateCost i - 2 = y + n + Iteration.baseOverhead G c b y n M - 1 := by
      rw [hC]
      omega
    rw [hsub]
    simpa only [pow_one, show (3 / 5 : ℝ) / 2 = 3 / 10 by norm_num] using hrefHalf
  have hupper : D N ≤ certificateCost i := by
    rw [hC]
    exact (ProtectedIterationBounds.no_exact G c b y n M hc ha hf hcost
      hΔ hγ hγone hcommon hno hsource).le
  have hnear := near_full G c b y n M hc ha hf hcost hΔ hγ hγone hcommon hno hsource
  have hout := ConcreteAlignedProfiles.profiles N e i hc hprop href' hrefHalf' hupper hnear
  change Iteration.AlignedProfiles G c b y n M
  simpa only [Iteration.AlignedProfiles, Iteration.aligned, Restoration.output,
    Iteration.alignedCost, Iteration.rq, Iteration.stepParameters, hC, N,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hout

end EthInapproximability.CurrentPaper.IterationAlignedComplete
