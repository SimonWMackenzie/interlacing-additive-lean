import CurrentAdditive.SmallBiasCanonicalClass
import EthInapproximability.CurrentPaper.ComplexityReductionClosure

/-!
# Deterministic midpoint and the conditional class endpoint

Source: v27 `yao:bpp`, deterministic clause. A dyadic-output estimator
is called on the canonical matrix word, and its decoded result is compared
to the rational midpoint in the source header. The mathematical correctness
of this specific Boolean decision function is proved below. Its physical
polynomial clock is an explicit remaining machine obligation.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open Paper2.Yao Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity

def canonicalDetDecision (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (est : List Bool → List Bool) (input : List Bool) : Bool :=
  let i := sourceCanonicalInstance g G input
  match Paper2.AModel.decodeDyadic (est (canonicalEstimatorWord g G input)) with
  | none => false
  | some v => decide (v < ((2 * i.threshold + (g - 1) : ℕ) : ℝ) / 2)

/-- A deterministic estimator is accurate on every valid matrix word. -/
def DeterministicEstimatesYao (est : List Bool → List Bool)
    (μ : YaoMeasure) (u : ℝ) : Prop :=
  ∀ w c, Paper2.AModel.targetYao μ w = some c →
    ∃ v, Paper2.AModel.decodeDyadic (est w) = some v ∧ |v - c| ≤ u

theorem canonicalDetDecision_correct (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (est : List Bool → List Bool) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hest : DeterministicEstimatesYao est μ u) (input : List Bool) :
    input ∈ G.L ↔ canonicalDetDecision g G est input = true := by
  let i := sourceCanonicalInstance g G input
  have hi : i.Valid := sourceCanonicalInstance_valid g G input
  obtain ⟨v, hv, hacc⟩ := hest
    (canonicalEstimatorWord g G input) (μ.eval i)
    (Paper2.YaoSelected.target_matrix μ i hi)
  have hgap := sourceCanonicalInstance_yes_no g G input
  have hthreshold : i.threshold =
      2 * sourceExactAddressWidth g G input + 4 * v27GapParameter g + 2 := rfl
  have hg1 : 1 ≤ g := by
    have h : (1 : ℝ) ≤ g := by linarith
    exact_mod_cast h
  have hmid : (((2 * i.threshold + (g - 1) : ℕ) : ℝ) / 2) =
      (i.threshold : ℝ) + ((g : ℝ) - 1) / 2 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hg1]
    push_cast
    ring
  have hwindow := measure_window μ i
  have hyes : input ∈ G.L → v <
      (((2 * i.threshold + (g - 1) : ℕ) : ℝ) / 2) := by
    intro hm
    have hD : Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold := by
      rw [hthreshold]
      exact hgap.1 hm
    have hc : μ.eval i ≤ i.threshold + 1 := by omega
    have hvbound : v - (μ.eval i : ℝ) ≤ u := (abs_le.mp hacc).2
    rw [hmid]
    exact_mod_cast (show v < (i.threshold : ℝ) + ((g : ℝ) - 1) / 2 by
      have hcc : (μ.eval i : ℝ) ≤ (i.threshold : ℝ) + 1 := by exact_mod_cast hc
      linarith)
  have hno : input ∉ G.L → ¬ v <
      (((2 * i.threshold + (g - 1) : ℕ) : ℝ) / 2) := by
    intro hn
    have hD : i.threshold + g ≤ Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) := by
      rw [hthreshold]
      exact hgap.2 hn
    have hc : i.threshold + g - 2 ≤ μ.eval i := by omega
    have hvbound : (μ.eval i : ℝ) - v ≤ u := by
      linarith [(abs_le.mp hacc).1]
    rw [hmid]
    intro hlt
    have hg3 : 3 ≤ g := by
      have h : (3 : ℝ) ≤ g := by linarith
      exact_mod_cast h
    have hcc : (i.threshold : ℝ) + (g : ℝ) - 2 ≤ (μ.eval i : ℝ) := by
      have hcc' : ((i.threshold + g - 2 : ℕ) : ℝ) ≤ (μ.eval i : ℝ) := by
        exact_mod_cast hc
      rw [Nat.cast_sub (by omega : 2 ≤ i.threshold + g)] at hcc'
      push_cast at hcc'
      exact hcc'
    linarith
  constructor
  · intro hm
    simp only [canonicalDetDecision, hv, decide_eq_true_eq]
    exact hyes hm
  · intro hd
    by_contra hn
    have hnv := hno hn
    simp only [canonicalDetDecision, hv, decide_eq_true_eq] at hd
    exact hnv hd

theorem canonical_source_inP (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (est : List Bool → List Bool) (μ : YaoMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hg : 2 * u + 3 < (g : ℝ))
    (hest : DeterministicEstimatesYao est μ u)
    (hclock : BitMachine.Polytime (fun input =>
      [canonicalDetDecision g G est input])) :
    ComplexityReductionClosure.InP G.L :=
  ⟨canonicalDetDecision g G est, hclock,
    canonicalDetDecision_correct g G est μ u hu hg hest⟩

theorem canonical_np_subset_p_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (μ : YaoMeasure)
    (hest : DeterministicEstimatesYao est μ u)
    (hclock : BitMachine.Polytime (fun input =>
      [canonicalDetDecision (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))) est input])) :
    ∀ L, InNP L → ComplexityReductionClosure.InP L := by
  let g := sourceEstimatorGap u
  let G := GF (v27GapParameter g)
  have hhard : NPHard G.L := by rw [hL]; exact hard
  exact ComplexityReductionClosure.npHard_inP_implies_np_subset_p hhard
    (canonical_source_inP g G est μ u hu (sourceEstimatorGap_bound u) hest hclock)

#print axioms CurrentAdditive.SmallBias.canonicalDetDecision_correct
#print axioms CurrentAdditive.SmallBias.canonical_np_subset_p_fixed_error

end CurrentAdditive.SmallBias
