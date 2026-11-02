import EthInapproximability.CurrentPaper.Iteration
import EthInapproximability.CurrentPaper.ProtectedScheduledPrefix
import EthInapproximability.CurrentPaper.ProtectedScheduledReference
import EthInapproximability.CurrentPaper.ProtectedBranchPreparation
import EthInapproximability.CurrentPaper.ProtectedDenseParameters
import EthInapproximability.CurrentPaper.ProtectedGraphProfile
import EthInapproximability.CurrentPaper.ProtectedPreparedWidth
import EthInapproximability.CurrentPaper.ProtectedScheduledOrdinary
import EthInapproximability.CurrentPaper.ExactResidualIndexing

/-!
# Dense restrictions of the literal iteration matrix

Source: frozen v8 `A-stage4-details.tex`, `thm:paper-protected-stage4`,
`lem:paper-protected-preparation`, and `lem:paper-protected-routed-closure`.
The source graph has exactly the edge cardinality recorded by
`Iteration.parameters`; the matrix below is the literal iteration input.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedIterationDense

open scoped Classical
open NPCC Workspace.Types.Protocol Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction Parameters ProtectedSourceSchedule
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

set_option maxHeartbeats 1200000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The canonical sampler is literally the family in the finite iteration;
the proof of positivity does not change its entries. -/
theorem family_eq (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (ha : Accepted (Iteration.parameters G c b y n M)) :
    AmplificationInnerProfiles.scheduledFamily (Iteration.parameters G c b y n M) ha =
      Iteration.secondFamily G c b y n M := rfl

/-- The original transposed protocol cannot have the proposed short cost
on a dense retained rectangle. All prefix and graph witnesses refer to
this same physical protocol and these same retained inputs. -/
theorem protocol_lower (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hc : 0 < c) (ha : Accepted (Iteration.parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (A : Finset (Iteration.NRow G c b y n M))
    (B : Finset (Iteration.NCol G c b y n M))
    (hA : (1 - (rowTolerance (Iteration.parameters G c b y n M) : ℝ)) *
      Fintype.card (Iteration.NRow G c b y n M) ≤ A.card)
    (hB : (1 - (columnTolerance (Iteration.parameters G c b y n M) : ℝ)) *
      Fintype.card (Iteration.NCol G c b y n M) ≤ B.card)
    (P : Protocol (Iteration.NCol G c b y n M) (Iteration.NRow G c b y n M) Bool)
    (hcomp : ∀ r ∈ B, ∀ a ∈ A, P.eval r a = Iteration.protectedMatrix G c b y n M a r) :
    y + n + Iteration.baseOverhead G c b y n M + 1 ≤ P.cost := by
  let i := Iteration.parameters G c b y n M
  have hci : 0 < i.sourceConstant := hc
  have hfi : IsRobustAt M.entry i.incomingDepth := hf
  have hcosti : D M.entry = i.cost := hcost
  have hsourcei : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant := hsource
  have hs : 4 ≤ bins i := Iteration.bins_ge_four G c b y n M
  have hL : 0 < Iteration.labels G c b y n M := PrimeSampler.size_pos _ _ _
  have hv : 0 < GraphVectors.vertexCount V (bins i) := by
    unfold GraphVectors.vertexCount
    exact Nat.mul_pos (by omega) G.card_vertex_pos
  have hb : 0 < GraphVectors.auxiliaryCount (bins i) := by
    unfold GraphVectors.auxiliaryCount
    exact Nat.mul_pos (by omega) (by omega)
  by_contra hshort
  have hPcost : P.cost ≤ i.cost + firstExponent i + secondExponent i + binExponent i := by
    change ¬ (y + n + (firstExponent i + secondExponent i + binExponent i) + 1 ≤ P.cost) at hshort
    change P.cost ≤ y + n + firstExponent i + secondExponent i + binExponent i
    omega
  have hcomp' : ∀ r ∈ B, ∀ a ∈ A, P.eval r a =
      Construction.protectedMatrix M.entry (firstExponent i) (bins i) (secondWidth i)
        (Iteration.labels G c b y n M) (GraphVectors.vertexCount V (bins i))
        (GraphVectors.auxiliaryCount (bins i)) (bins_pos i)
        (AmplificationInnerProfiles.scheduledFamily i ha) (GraphVectors.itemOrder G (bins i))
        (GraphVectors.vectors G (bins i)) (GraphVectors.supportCap G (by omega)) a r := hcomp
  obtain ⟨hpref, bin, _, K, hK, _, hKphysical⟩ :=
    ProtectedScheduledPrefix.scheduled_prefix_families i hci ha M.entry hfi hcosti
      Δ γ (G.deltaV γ Δ) hΔ hγ hγone hsourcei
      (G.deltaStar_le_deltaV hγ hΔ hcommon)
      (GraphVectors.vertexCount V (bins i)) (GraphVectors.auxiliaryCount (bins i)) hv hb
      (GraphVectors.itemOrder G (bins i)) (GraphVectors.vectors G (bins i))
      (GraphVectors.supportCap G (by omega)) A B hA hB P hPcost hcomp'
  have hBq : (1 - columnTolerance i) * Fintype.card (Iteration.NCol G c b y n M) ≤
      (B.card : ℚ) := by
    exact_mod_cast hB
  have hdel := ProtectedSourceSchedule.graph_deletion_gates G i hΔ hγ hγone
    hcommon hsourcei (Iteration.labels G c b y n M) hL B hBq
  have ht := threshold_gates (X := Fin M.rows) i ha
  have hdelete := ProtectedDeletionGates.complement_count A hA
  obtain ⟨p, U, H, W, hH, hW, hsub, hord, hwit, hexcess, hphys, hgood, hWit⟩ :=
    ProtectedBranchPreparation.prepare_branch G hs hL ht.1 (firstWidth_pos i) hΔ hγ hγone
      (fun v => (hcommon.2 v).2) hno (Iteration.secondFamily G c b y n M)
      K bin A B (Protocol.prefixCodeRaw (binExponent i) P) hKphysical ht.2.1.le
      hdel.1 hdel.2 (by positivity)
      (Iteration.step_family_balanced_of_accepted G c b y n M hc ha)
      (ProtectedDenseParameters.threshold_defect_gate i ha)
      (ProtectedDenseParameters.balance_order_gate i) hK
      (ProtectedDenseParameters.dominant_density_gate i) hdelete
      (ProtectedDenseParameters.graph_room i ha hΔ hγ hγone hsourcei)
      (ProtectedDenseParameters.row_tolerance_strict i hΔ hγ hγone hsourcei)
  have hgraph := ProtectedGraphProfile.local_capacity_half M.entry i ha hfi
  rw [hcosti] at hgraph
  have hscalar := AmplificationSecondGates.scalar_gates i hci ha
  have hsum : secondExponent i - balanceExponent i + balanceExponent i = secondExponent i := by
    have hh := AmplificationSecondGates.balanceExponent_add_two_le_second i hci ha
    omega
  have hscale : (2 : ℝ) ^ (secondExponent i - balanceExponent i + balanceExponent i + 1) *
      (2 : ℝ) ^ (-(firstDepth i : ℝ)) ≤ 1 / 4 := by
    have hh := (ParameterGates.second_alpha_bounds i hci ha 0 (by omega)).2
    simp only [Nat.sub_zero, Nat.cast_zero, neg_zero, Real.rpow_zero] at hh
    rw [hsum, pow_succ]
    nlinarith
  have inputs := ProtectedScheduledOrdinary.scheduled_ordinary i hci ha M.entry hfi hcosti
    (secondExponent i - balanceExponent i) hsum hscalar.2.2.1
  have hthreshold : sourceThreshold (Fin M.rows) i =
      ⌈(Fintype.card (Fin M.rows) : ℝ) * sourceFraction i⌉₊ := by
    rw [sourceThreshold, mul_comm]
  have hlower := ProtectedPreparedWidth.physical_prepared_lower M.entry
    (firstExponent i) (bins i) (secondWidth i) (balanceExponent i)
    (secondExponent i - balanceExponent i) (Iteration.labels G c b y n M)
    (GraphVectors.vertexCount V (bins i)) (GraphVectors.auxiliaryCount (bins i))
    (i.cost + firstExponent i) _ U.card hscalar.2.2.1 (bins_pos i) hL (firstWidth_pos i)
    (Iteration.secondFamily G c b y n M) (GraphVectors.itemOrder G (bins i))
    (GraphVectors.vectors G (bins i)) (GraphVectors.supportCap G (by omega))
    (x := (2 : ℝ) ^ (-(firstDepth i : ℝ))) (h := 998 / 1000)
    (ε := 1 / (100 * (balanceOrder i : ℝ)))
    (by convert inputs using 1) hgraph
    B A (Protocol.prefixCodeRaw (binExponent i) P) p (bin p) (K p)
    (hK p) hphys H W hsub hord hwit hexcess
    (by
      rw [hthreshold] at hgood
      intro α hα
      refine ⟨?_, (hgood α hα).2⟩
      convert (hgood α hα).1 using 1
      apply Iff.of_eq
      congr 2
      funext β
      ext r
      simp [ProtectedDefects.coordinateSupport])
    (by simpa only [hthreshold] using hWit)
    hscale (Protocol.swap (Protocol.rowSubtreeAtRaw (binExponent i) P p))
    (ProtectedPreparedRouting.actual_suffix_agrees _ B A P hpref hcomp' p)
  have hcharged := ProtectedPreparedRouting.actual_prefix_cost P hpref p hlower
  omega

/-- Both physical domains in the literal iteration are nonempty. -/
theorem carrier_pos (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix) :
    0 < Fintype.card (Iteration.NRow G c b y n M) ∧
      0 < Fintype.card (Iteration.NCol G c b y n M) := by
  have hs := Iteration.bins_ge_four G c b y n M
  have hq := q2_pos G (Iteration.s G c b y n M)
  have hL : 0 < Iteration.labels G c b y n M := PrimeSampler.size_pos _ _ _
  have hv := G.card_vertex_pos
  have hr := M.rows_pos
  have hcol := M.columns_pos
  constructor
  · rw [Construction.card_protectedColumns]
    simp only [Fintype.card_fin]
    positivity
  · rw [Construction.card_protectedRows]
    simp only [Fintype.card_fin, GraphVectors.vertexCount, GraphVectors.auxiliaryCount]
    have hsub : 0 < Iteration.s G c b y n M - 3 := by omega
    positivity

/-- The two public deletion tolerances lie strictly below one. -/
theorem tolerance_bounds (i : Input) (hc : 0 < i.sourceConstant) :
    (0 : ℝ) < (rowTolerance i : ℝ) ∧ (rowTolerance i : ℝ) < 1 ∧
      (0 : ℝ) < (columnTolerance i : ℝ) ∧ (columnTolerance i : ℝ) < 1 := by
  have hs : 64 ≤ bins i := Nat.le_of_dvd (bins_pos i) (sixtyfour_dvd_bins i)
  have hn : 64 ≤ i.sourceConstant * bins i := by
    have hh := Nat.mul_le_mul_right (bins i) hc
    omega
  have hnR : (64 : ℝ) ≤ i.sourceConstant * bins i := by exact_mod_cast hn
  have hp : (0 : ℝ) < i.sourceConstant * bins i := by linarith
  simp only [rowTolerance, columnTolerance, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_mul, Rat.cast_mul]
  exact ⟨div_pos (by norm_num) hp, (div_lt_one hp).mpr (by linarith),
    div_pos (by norm_num) hp, (div_lt_one hp).mpr (by linarith)⟩

/-- Every dense submatrix of the actual `N` has the full one-bit-gap cost. -/
theorem subgame_lower (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hc : 0 < c) (ha : Accepted (Iteration.parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    (A : Finset (Iteration.NRow G c b y n M))
    (B : Finset (Iteration.NCol G c b y n M))
    (hA : (1 - (rowTolerance (Iteration.parameters G c b y n M) : ℝ)) *
      Fintype.card (Iteration.NRow G c b y n M) ≤ A.card)
    (hB : (1 - (columnTolerance (Iteration.parameters G c b y n M) : ℝ)) *
      Fintype.card (Iteration.NCol G c b y n M) ≤ B.card) :
    y + n + Iteration.baseOverhead G c b y n M + 1 ≤
      D (subgame (Iteration.protectedMatrix G c b y n M) A B) := by
  have hcard := carrier_pos G c b y n M
  have htol := tolerance_bounds (Iteration.parameters G c b y n M) hc
  have hAne : A.Nonempty := Finset.card_pos.mp (by
    have hp : (0 : ℝ) < (1 - (rowTolerance (Iteration.parameters G c b y n M) : ℝ)) *
        Fintype.card (Iteration.NRow G c b y n M) :=
      mul_pos (by linarith [htol.2.1]) (by exact_mod_cast hcard.1)
    exact_mod_cast hp.trans_le hA)
  have hBne : B.Nonempty := Finset.card_pos.mp (by
    have hp : (0 : ℝ) < (1 - (columnTolerance (Iteration.parameters G c b y n M) : ℝ)) *
        Fintype.card (Iteration.NCol G c b y n M) :=
      mul_pos (by linarith [htol.2.2.2]) (by exact_mod_cast hcard.2)
    exact_mod_cast hp.trans_le hB)
  let F := Iteration.protectedMatrix G c b y n M
  obtain ⟨P, hPc, hP⟩ := (Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty
    (subgame F A B)) : D (subgame F A B) ∈ AchievableCosts (subgame F A B))
  let Q := Protocol.swap (Protocol.extendSub A B hAne hBne P)
  have hQ : ∀ r ∈ B, ∀ a ∈ A, Q.eval r a = F a r := by
    intro r hr a ha
    change (Protocol.swap (Protocol.extendSub A B hAne hBne P)).eval r a = F a r
    rw [Protocol.eval_swap, Protocol.eval_extendSub A B hAne hBne P ⟨a, ha⟩ ⟨r, hr⟩]
    exact hP ⟨a, ha⟩ ⟨r, hr⟩
  have hlower := protocol_lower G c b y n M hc ha hf hcost hΔ hγ hγone hcommon hno
    hsource A B hA hB Q hQ
  simpa only [Q, Protocol.cost_swap, Protocol.cost_extendSub, hPc] using hlower

/-- The exact near-full one-copy profile needed before scale alignment. -/
theorem dense_profile (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hc : 0 < c) (ha : Accepted (Iteration.parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hcommon : G.SourceCommon γ Δ) (hno : G.SourceNO γ)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) :
    y + n + Iteration.baseOverhead G c b y n M + 1 ≤
      Dfamily (interlaceFun (Iteration.protectedMatrix G c b y n M) 1)
        (bracketGE (Iteration.NRow G c b y n M) (Iteration.NCol G c b y n M) 1
          (1 - (rowTolerance (Iteration.parameters G c b y n M) : ℝ))
          (1 - (columnTolerance (Iteration.parameters G c b y n M) : ℝ))) := by
  letI : Nonempty (Iteration.NRow G c b y n M) := Fintype.card_pos_iff.mp (carrier_pos G c b y n M).1
  have htol := tolerance_bounds (Iteration.parameters G c b y n M) hc
  apply ExactResidualIndexing.oneCopy_family_lower_of_subgame _ (by linarith [htol.1])
    (by linarith [htol.2.2.1])
  intro A B hA hB
  exact subgame_lower G c b y n M hc ha hf hcost hΔ hγ hγone hcommon hno hsource A B
    (by simpa only [mul_comm] using hA) (by simpa only [mul_comm] using hB)

/-- Both reference profiles for the exact row-submatrix of the iteration's
protected matrix. Unlike the dense theorem, these do not use the NO promise. -/
theorem reference_profile (G : EndpointGraph V E) (c b y n : ℕ) (M : Iteration.Matrix)
    (hc : 0 < c) (ha : Accepted (Iteration.parameters G c b y n M))
    (hf : IsRobustAt M.entry b) (hcost : D M.entry = y + n)
    (hvertices : Fintype.card V ≤ 2 * Fintype.card E) (j : ℕ) (hj : j ≤ 1) :
    y + n + Iteration.baseOverhead G c b y n M - j ≤
      Dfamily (interlaceFun
        (fun r : JointTransfer.referenceRows (Y := Fin M.columns)
            (Iteration.a G c b y n M) (Iteration.s G c b y n M) (Iteration.q₂ G c b y n M) =>
          Iteration.protectedMatrix G c b y n M r.val) 1)
        (bracketGE
          (JointTransfer.referenceRows (Y := Fin M.columns)
            (Iteration.a G c b y n M) (Iteration.s G c b y n M) (Iteration.q₂ G c b y n M))
          (Iteration.NCol G c b y n M) 1
          ((2 : ℝ) ^ (-(tailDepth (Iteration.parameters G c b y n M) : ℝ)))
          ((3 / 5 : ℝ) / 2 ^ j)) := by
  let i := Iteration.parameters G c b y n M
  have hs : 4 ≤ bins i := Iteration.bins_ge_four G c b y n M
  have h := ProtectedScheduledReference.scheduled_reference_profile i hc ha M.entry hf hcost
    (Fintype.card V) G.card_vertex_pos hvertices (GraphVectors.itemOrder G (bins i))
    (GraphVectors.vectors G (bins i)) (GraphVectors.supportCap G (by omega)) j hj
  have hbin : j ≤ binExponent i := by
    have hh := (ParameterGates.hard_seed_exponent_domains i).2.2.2
    omega
  have heq : y + n + Iteration.baseOverhead G c b y n M - j =
      i.cost + firstExponent i + secondExponent i + (binExponent i - j) := by
    change y + n + (firstExponent i + secondExponent i + binExponent i) - j =
      y + n + firstExponent i + secondExponent i + (binExponent i - j)
    omega
  rw [heq]
  exact h

end EthInapproximability.CurrentPaper.ProtectedIterationDense
