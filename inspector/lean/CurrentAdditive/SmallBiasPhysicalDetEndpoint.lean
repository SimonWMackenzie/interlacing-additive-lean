import CurrentAdditive.SmallBiasDetTapeClosure

/-!
# Physical deterministic class endpoint, conditional only on the printer

The median/dyadic comparator is the inherited checked finite machine.
The estimator is a given polynomial-time deterministic dyadic estimator.
The remaining reduction-side premise is the polynomial clock for the
source-faithful canonical classifier word itself.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 3000000

open Classical
open Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

def physicalDetAlgorithm (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est) :
    Paper2.SelectedTape.Algorithm :=
  canonicalSelectedDecider g G hprint (selectedDetEstimator est hest)

def physicalDetDecision (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (input : List Bool) : Bool :=
  decide ((physicalDetAlgorithm g G hprint est hest).output input [] = [true])

theorem physicalDetAlgorithm_output_singleton (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (input : List Bool) :
    ∃ b, (physicalDetAlgorithm g G hprint est hest).output input [] = [b] := by
  let E := selectedDetEstimator est hest
  change ∃ b, (canonicalSelectedDecider g G hprint E).output input [] = [b]
  rw [canonicalSelectedDecider, Paper2.SelectedTape.pullback_output]
  rw [Paper2.ADecider4.classifier_output]
  unfold Paper2.MedianOwner.Final.medOutput
  exact ⟨_, rfl⟩

theorem physicalDetAlgorithm_output_bit (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (input : List Bool) :
    (physicalDetAlgorithm g G hprint est hest).output input [] =
      [physicalDetDecision g G hprint est hest input] := by
  obtain ⟨b, hb⟩ := physicalDetAlgorithm_output_singleton g G hprint est hest input
  rw [hb]
  cases b <;> simp [physicalDetDecision, hb]

theorem zeroTapeProb (A : Paper2.SelectedTape.Algorithm)
    (hz : ∀ x, A.tapeLength x = 0) (x : List Bool)
    (E : List Bool → Prop) :
    A.prob x E = if E (A.output x []) then 1 else 0 := by
  have hcR : A.cR = 0 := by
    have h := hz []
    simpa [Paper2.SelectedTape.Algorithm.tapeLength] using h
  simp [Paper2.SelectedTape.Algorithm.prob,
    Paper2.SelectedTape.Algorithm.tapeLength, hcR,
    Paper2.FiniteLaw.prob, Paper2.Unit4Shell.Definitions.uniformTape]

theorem physicalDetDecision_correct (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (μ : YaoMeasure) (u : ℝ) (hu : 0 ≤ u)
    (hg : 2 * u + 3 < (g : ℝ))
    (hacc : DeterministicEstimatesYao est μ u) (input : List Bool) :
    input ∈ G.L ↔ physicalDetDecision g G hprint est hest input = true := by
  let A := physicalDetAlgorithm g G hprint est hest
  have hz : ∀ x, A.tapeLength x = 0 :=
    canonicalDetClassifier_tape_zero g G hprint est hest
  have hd : A.Decides G.L (1 / 3) :=
    canonicalSelectedDecider_decides g G hprint
      (selectedDetEstimator est hest) μ u hu hg
      (selectedDetEstimator_estimatesYao est hest μ u hacc)
  have hp := zeroTapeProb A hz input (· = [true])
  constructor
  · intro hm
    have hyes := (hd input).1 hm
    rw [hp] at hyes
    by_contra hn
    have hfalse : A.output input [] ≠ [true] := by
      simpa [physicalDetDecision, A] using hn
    simp [hfalse] at hyes
    norm_num at hyes
  · intro hbit
    by_contra hn
    have hno := (hd input).2 hn
    have htrue : A.output input [] = [true] := by
      simpa [physicalDetDecision, A] using hbit
    rw [hp, if_pos htrue] at hno
    norm_num at hno

theorem physicalDetDecision_polytime (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est) :
    BitMachine.Polytime (fun input =>
      [physicalDetDecision g G hprint est hest input]) := by
  let A := physicalDetAlgorithm g G hprint est hest
  have hz : ∀ x, A.tapeLength x = 0 :=
    canonicalDetClassifier_tape_zero g G hprint est hest
  have hphysical := zeroTapeOutputPolytime A hz
  have heq : (fun input => [physicalDetDecision g G hprint est hest input]) =
      (fun input => A.output input []) := by
    funext input
    exact (physicalDetAlgorithm_output_bit g G hprint est hest input).symm
  rw [heq]
  exact hphysical

theorem physical_canonical_p_equals_np_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (hest : BitMachine.Polytime est)
    (μ : YaoMeasure) (hacc : DeterministicEstimatesYao est μ u)
    (hprint : BitMachine.Polytime
      (canonicalClassifierWord (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))))) :
    PEqualsNP := by
  let g := sourceEstimatorGap u
  let G := GF (v27GapParameter g)
  have hhard : NPHard G.L := by rw [hL]; exact hard
  have hmem : ComplexityReductionClosure.InP G.L :=
    ⟨physicalDetDecision g G hprint est hest,
      physicalDetDecision_polytime g G hprint est hest,
      physicalDetDecision_correct g G hprint est hest μ u hu
        (sourceEstimatorGap_bound u) hacc⟩
  exact p_equals_np_of_np_subset_p
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hhard hmem)

#print axioms CurrentAdditive.SmallBias.physicalDetDecision_polytime
#print axioms CurrentAdditive.SmallBias.physical_canonical_p_equals_np_fixed_error

end CurrentAdditive.SmallBias
