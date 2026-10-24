import CurrentAdditive.EventualJoinAt
import Paper2.E6Final

/-! Private class-level routed decider for the literal eventual table-entry
estimator domain. The fixed cutoff may depend on the estimator's threshold,
but the resulting decider is one physical `ETape.Algorithm`. -/

noncomputable section
namespace CurrentAdditive.Eventual

open Paper2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth Paper2.AEth2 Paper2.AEth4 Paper2.AEth5 Paper2.AEth6

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def cutN_eventual (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c) : ℕ :=
  max 1 (max (N0 D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2))
    (max (Classical.choose (decider_error_joinAt_eventual D B (cs + 2) c hc0 hc E hE))
      (Classical.choose (decTime_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2)))))

theorem cutN_eventual_pos (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c) :
    1 ≤ cutN_eventual D B E cs c hc0 hc hE := le_max_left _ _

theorem cutN_eventual_N0 (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c) :
    N0 D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2) ≤ cutN_eventual D B E cs c hc0 hc hE :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cutN_eventual_K (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c) :
    2 ≤ (cs + 2) * cutN_eventual D B E cs c hc0 hc hE := by
  have := cutN_eventual_pos D B E cs c hc0 hc hE
  nlinarith

/-- **THE composite growing-gap decider** (R20 carrier) for estimator `E` and density `cs`. -/
def growDec_eventual (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c) : ETape.Algorithm :=
  decAlg D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2) (cutN_eventual D B E cs c hc0 hc hE)
    (cutN_eventual_pos D B E cs c hc0 hc hE)
    (cutN_eventual_N0 D B E cs c hc0 hc hE)
    (cutN_eventual_K D B E cs c hc0 hc hE)

set_option maxHeartbeats 1000000 in
/-- **Segment 3: the composite decider is an R20 sparse decider at density `cs`.** -/
theorem growDec_eventual_sparse (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySel E c) (cs : ℕ) :
    SparseDeciderR20 cs (growDec_eventual D B E cs c hc0 hc hE) := by
  have hN₁ := cutN_eventual_pos D B E cs c hc0 hc hE
  have hN := cutN_eventual_N0 D B E cs c hc0 hc hE
  have hK := cutN_eventual_K D B E cs c hc0 hc hE
  have herr := Classical.choose_spec (decider_error_joinAt_eventual D B (cs + 2) c hc0 hc E hE)
  have hclk := Classical.choose_spec
    (decTime_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2))
  have hNerr : Classical.choose (decider_error_joinAt_eventual D B (cs + 2) c hc0 hc E hE) ≤ cutN_eventual D B E cs c hc0 hc hE :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hNclk : Classical.choose (decTime_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2)) ≤
      cutN_eventual D B E cs c hc0 hc hE :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  refine ⟨fun input hwf hsp => ?_, fun ε hε => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
    have hspK : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
      le_trans hsp (Nat.mul_le_mul_right _ (by omega))
    set Φ' := routedV (cs + 2) (cutN_eventual D B E cs c hc0 hc hE) hN₁ (EncodedCNF.encode Φ.val) with hΦ'
    have hJ := decAlg_joinAt D B E (cs + 2) (cutN_eventual D B E cs c hc0 hc hE) hN₁ hN hK (EncodedCNF.encode Φ.val)
    have hsp' : Φ'.val.clauses.length ≤ (cs + 2) * Φ'.val.variables :=
      routed4_sparse (cs + 2) (cutN_eventual D B E cs c hc0 hc hE) hK _
    have hv' : cutN_eventual D B E cs c hc0 hc hE ≤ Φ'.val.variables := routed4_variables _ _ _
    have h := herr Φ' hsp' (le_trans hNerr hv') (growDec_eventual D B E cs c hc0 hc hE)
      (EncodedCNF.encode Φ.val) hJ
    have hlang : EncodedCNF.encode Φ'.val ∈ EncodedCNF.Language ↔
        EncodedCNF.encode Φ.val ∈ EncodedCNF.Language := by
      rw [EncodedCNF.encode_mem_iff Φ'.val Φ'.property]
      exact routed4_sat_iff (cs + 2) hN₁ Φ.val Φ.property hspK
    exact ⟨fun hin => h.1 (hlang.2 hin), fun hout => h.2 (fun h' => hout (hlang.1 h'))⟩
  · obtain ⟨C', d, N₂, hb⟩ := hclk (cutN_eventual D B E cs c hc0 hc hE) hN₁ hNclk hK ε hε
    refine ⟨C', d, N₂, fun input hwf hsp hN2 => ?_⟩
    obtain ⟨Φ, rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
    rw [ADecider.variableCount_encode] at hN2 ⊢
    have hspK : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
      le_trans hsp (Nat.mul_le_mul_right _ (by omega))
    exact hb Φ hspK hN2


include D B in
theorem T24_class_eventual (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hETH : RandomizedSparseETH_R20) :
    ¬ ∃ E : SelectedTape.Algorithm, EstimatesGrowingEventuallySel E c := by
  rintro ⟨E, hE⟩
  exact (not_R20_iff.2 (fun cs => ⟨growDec_eventual D B E cs c hc0 hc hE,
    growDec_eventual_sparse D B E c hc0 hc hE cs⟩)) hETH

#print axioms growDec_eventual_sparse
#print axioms T24_class_eventual

end CurrentAdditive.Eventual
