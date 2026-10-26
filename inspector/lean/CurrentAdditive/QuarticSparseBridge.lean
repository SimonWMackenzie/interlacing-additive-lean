import CurrentAdditive.QuarticSquareHeaderClockBound
import CurrentAdditive.QuarticJointBridge
import Paper2.ETapeETH

/-! Routing handles every small or malformed source input once the physical
v27 algorithm realizes the exact joint law and has the declared runtime. -/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.AEth2
open _root_.CurrentAdditive.Eventual
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.T10Size
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

def cutN27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1 / 12) (hE : EstimatesGrowingEventuallySelSq E c)
    (cs : ℕ) : ℕ :=
  max 1 (max
    (max
      (Classical.choose (source_decider_error_at_large27
        Dsrc Bsrc E c hc0 hc hE (cs + 2)))
      (2 ^ (2 ^ (Dsrc.sizeExponent + 1) * t45C Dsrc Bsrc (cs + 2))))
    (Bsrc.degreeBound * CurrentAdditive.QuarticSchedule.threshold27
      Bsrc.degreeBound (sourceGap Dsrc Bsrc)))

theorem cutN27_pos
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1 / 12) (hE : EstimatesGrowingEventuallySelSq E c)
    (cs : ℕ) : 1 ≤ cutN27 Dsrc Bsrc E c hc0 hc hE cs :=
  le_max_left _ _

theorem cutN27_scheduled_threshold
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1 / 12) (hE : EstimatesGrowingEventuallySelSq E c)
    (cs : ℕ) :
    Bsrc.degreeBound * CurrentAdditive.QuarticSchedule.threshold27
      Bsrc.degreeBound (sourceGap Dsrc Bsrc) ≤
      cutN27 Dsrc Bsrc E c hc0 hc hE cs :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem sparse_of_joint_runtime_at27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (E : SelectedTape.Algorithm) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < 1 / 12) (hE : EstimatesGrowingEventuallySelSq E c)
    (cs N₁ : ℕ)
    (hcut : cutN27 Dsrc Bsrc E c hc0 hc hE cs ≤ N₁)
    (A : ETape.Algorithm)
    (hJ : ∀ x : List Bool,
      JoinRealisesSqAt27 Dsrc Bsrc x
        (Paper2.AEth4.routedV (cs + 2) N₁
          ((cutN27_pos Dsrc Bsrc E c hc0 hc hE cs).trans hcut) x) E A)
    (hT : ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ,
      ∀ input, Paper2.AModel.WellFormedCNF input →
      Paper2.AModel.cnfClauseCount input ≤
        cs * EncodedETHTail.variableCount input →
      N₀ ≤ EncodedETHTail.variableCount input →
      A.time input ≤ C *
        ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
        (input.length + 1) ^ d) :
    SparseDeciderR20 cs A := by
  refine ⟨?_, hT⟩
  intro input hwf hsp
  obtain ⟨Φ, rfl⟩ := hwf
  rw [Paper2.ADecider.cnfClauseCount_encode,
    Paper2.ADecider.variableCount_encode] at hsp
  have hN₁ : 1 ≤ N₁ :=
    (cutN27_pos Dsrc Bsrc E c hc0 hc hE cs).trans hcut
  have hK : 2 ≤ (cs + 2) * N₁ := by
    have h2 : 2 ≤ cs + 2 := by omega
    simpa using Nat.mul_le_mul h2 hN₁
  let Φ' := Paper2.AEth4.routedV (cs + 2) N₁ hN₁
    (EncodedCNF.encode Φ.val)
  have hsp' : Φ'.val.clauses.length ≤
      (cs + 2) * Φ'.val.variables :=
    Paper2.AEth4.routed4_sparse (cs + 2) N₁ hK _
  have hvars : N₁ ≤ Φ'.val.variables :=
    Paper2.AEth4.routed4_variables _ _ _
  have hlarge : Classical.choose
      (source_decider_error_at_large27 Dsrc Bsrc E c hc0 hc hE (cs + 2)) ≤
      Φ'.val.variables := by
    have hle : Classical.choose
        (source_decider_error_at_large27 Dsrc Bsrc E c hc0 hc hE (cs + 2)) ≤ N₁ :=
      ((le_max_left _ _).trans ((le_max_left _ _).trans
        (le_max_right _ _))).trans hcut
    omega
  have hbig : 2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      t45C Dsrc Bsrc (cs + 2)) ≤ Φ'.val.variables := by
    have hle : 2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
        t45C Dsrc Bsrc (cs + 2)) ≤ N₁ :=
      ((le_max_right _ _).trans ((le_max_left _ _).trans
        (le_max_right _ _))).trans hcut
    omega
  have herr := Classical.choose_spec
    (source_decider_error_at_large27 Dsrc Bsrc E c hc0 hc hE (cs + 2))
  have hprob := herr Φ' hsp' hlarge hbig A
    (EncodedCNF.encode Φ.val) (hJ (EncodedCNF.encode Φ.val))
  have hspK : Φ.val.clauses.length ≤
      (cs + 2) * Φ.val.variables :=
    le_trans hsp (Nat.mul_le_mul_right _ (by omega))
  have hlang : EncodedCNF.encode Φ'.val ∈ EncodedCNF.Language ↔
      EncodedCNF.encode Φ.val ∈ EncodedCNF.Language := by
    rw [EncodedCNF.encode_mem_iff Φ'.val Φ'.property]
    exact Paper2.AEth4.routed4_sat_iff (cs + 2) hN₁
      Φ.val Φ.property hspK
  exact ⟨fun hin => hprob.1
      ((EncodedCNF.encode_mem_iff Φ'.val Φ'.property).mp (hlang.2 hin)),
    fun hout => hprob.2 (fun h' =>
      hout (hlang.1 ((EncodedCNF.encode_mem_iff Φ'.val Φ'.property).mpr h')))⟩

#print axioms sparse_of_joint_runtime_at27
#print axioms cutN27_scheduled_threshold

end Paper2.CurrentAdditive.QuarticClassEndpoint

end
