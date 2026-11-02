import CurrentAdditive.EventualSquareJoinAt
import Paper2.E7SqFinal

/-! Private square class-level routed decider for the literal eventual
padded table-entry domain. The chosen cutoff becomes a fixed natural
constant in one physical `ETape.Algorithm`. -/

noncomputable section
namespace CurrentAdditive.Eventual

open Paper2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth Paper2.AEth2 Paper2.AEth4 Paper2.AEth5 Paper2.AEth6 Paper2.AEth7

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def cutNSq_eventual (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) : ℕ :=
  max 1 (max (N0Sq D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2))
    (Classical.choose (decider_error_joinAt_square_eventual D B (cs + 2) c hc0 hc E hE)))

theorem cutNSq_eventual_pos (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) :
    1 ≤ cutNSq_eventual D B E cs c hc0 hc hE := le_max_left _ _

theorem cutNSq_eventual_N0 (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) :
    N0Sq D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2) ≤ cutNSq_eventual D B E cs c hc0 hc hE :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem cutNSq_eventual_K (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) :
    2 ≤ (cs + 2) * cutNSq_eventual D B E cs c hc0 hc hE := by
  have := cutNSq_eventual_pos D B E cs c hc0 hc hE
  nlinarith

/-- **THE composite SQUARE growing-gap decider** (R20 carrier; header tail `hdTailSq` with the admitted square
post machine `Paper2.ASquare.Post.squareMachine`) for estimator `E` and density `cs`. -/
def growDecSq_eventual (E : SelectedTape.Algorithm) (cs : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) : ETape.Algorithm :=
  decAlgSq D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2) (cutNSq_eventual D B E cs c hc0 hc hE)
    (cutNSq_eventual_pos D B E cs c hc0 hc hE) (cutNSq_eventual_N0 D B E cs c hc0 hc hE) (cutNSq_eventual_K D B E cs c hc0 hc hE)

set_option maxHeartbeats 1000000 in
/-- **Segment 6f: the square composite decider is an R20 sparse decider at density `cs`.** -/
theorem growDecSq_eventual_sparse (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hE : EstimatesGrowingEventuallySelSq E c) (cs : ℕ) :
    SparseDeciderR20 cs (growDecSq_eventual D B E cs c hc0 hc hE) := by
  have hN₁ := cutNSq_eventual_pos D B E cs c hc0 hc hE
  have hN := cutNSq_eventual_N0 D B E cs c hc0 hc hE
  have hK := cutNSq_eventual_K D B E cs c hc0 hc hE
  have herr := Classical.choose_spec (decider_error_joinAt_square_eventual D B (cs + 2) c hc0 hc E hE)
  have hNerr : Classical.choose (decider_error_joinAt_square_eventual D B (cs + 2) c hc0 hc E hE) ≤ cutNSq_eventual D B E cs c hc0 hc hE :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun input hwf hsp => ?_, fun ε hε => ?_⟩
  · obtain ⟨Φ, rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
    have hspK : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
      le_trans hsp (Nat.mul_le_mul_right _ (by omega))
    set Φ' := routedV (cs + 2) (cutNSq_eventual D B E cs c hc0 hc hE) hN₁ (EncodedCNF.encode Φ.val) with hΦ'
    have hJ := decAlgSq_joinAt D B E (cs + 2) (cutNSq_eventual D B E cs c hc0 hc hE) hN₁ hN hK (EncodedCNF.encode Φ.val)
    have hsp' : Φ'.val.clauses.length ≤ (cs + 2) * Φ'.val.variables :=
      routed4_sparse (cs + 2) (cutNSq_eventual D B E cs c hc0 hc hE) hK _
    have hv' : cutNSq_eventual D B E cs c hc0 hc hE ≤ Φ'.val.variables := routed4_variables _ _ _
    have h := herr Φ' hsp' (le_trans hNerr hv') (growDecSq_eventual D B E cs c hc0 hc hE)
      (EncodedCNF.encode Φ.val) hJ
    have hlang : EncodedCNF.encode Φ'.val ∈ EncodedCNF.Language ↔
        EncodedCNF.encode Φ.val ∈ EncodedCNF.Language := by
      rw [EncodedCNF.encode_mem_iff Φ'.val Φ'.property]
      exact routed4_sat_iff (cs + 2) hN₁ Φ.val Φ.property hspK
    exact ⟨fun hin => h.1 (hlang.2 hin), fun hout => h.2 (fun h' => hout (hlang.1 h'))⟩
  · obtain ⟨C', d, N₂, hb⟩ := decTimeSq_budget D B (Paper2.HeaderStrip.selectedClassifier E) (cs + 2)
      (cutNSq_eventual D B E cs c hc0 hc hE) hN₁ hK ε hε
    refine ⟨C', d, N₂, fun input hwf hsp hN2 => ?_⟩
    obtain ⟨Φ, rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode, ADecider.variableCount_encode] at hsp
    rw [ADecider.variableCount_encode] at hN2 ⊢
    have hspK : Φ.val.clauses.length ≤ (cs + 2) * Φ.val.variables :=
      le_trans hsp (Nat.mul_le_mul_right _ (by omega))
    exact hb Φ hspK hN2


include D B in
theorem T24_square_class_eventual (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1 / 12)
    (hETH : RandomizedSparseETH_R20) :
    ¬ ∃ E : SelectedTape.Algorithm, EstimatesGrowingEventuallySelSq E c := by
  rintro ⟨E, hE⟩
  exact (not_R20_iff.2 (fun cs => ⟨growDecSq_eventual D B E cs c hc0 hc hE,
    growDecSq_eventual_sparse D B E c hc0 hc hE cs⟩)) hETH

#print axioms growDecSq_eventual_sparse
#print axioms T24_square_class_eventual

end CurrentAdditive.Eventual
