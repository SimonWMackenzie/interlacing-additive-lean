import Paper2.MedPoly
import Paper2.HeaderEstimatorSelected
import CurrentAdditive.YaoEndpointPhysical

/-! The physical 147-run median, generalized from Paper2.MedianOwner.Final
to a numeric output decoder supplied by the estimator model. The inherited
machine, tape and clock formulas are unchanged. -/

noncomputable section
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace CurrentAdditive.ModelEndpointReview

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification (reps)
open Paper2.MedianOwner Paper2.MedianOwner.Med
open Paper2.MedianOwner.Final (chunk chunk_length pref_chunks ofFn_chunk acc_eq_card medClock_le Kc)
open Paper2.AModel (PrefixAlgorithm)

variable (A : PrefixAlgorithm) (C : Machine) (dec : List Bool → Option ℝ) (thr : List Bool → ℝ) (TC : List Bool → ℕ)

open Classical in
/-- The comparator hypothesis: `C` prints the one bit `decide (dec out < thr w)` on
`pair w out` within `TC w`, for every word `out` of length at most the output bound of `A`. -/
def CmpSpecGeneral : Prop :=
  ∀ w out, out.length ≤ outBound A.machine w.length (A.tapeLength w.length) (A.time w) →
    C.OutputsWithin (pair w out) [decide (Below dec (thr w) out)] (TC w)

open Classical in
/-- The printed word of the median machine on `pair w tape`. -/
noncomputable def medOutputGeneral (w tape : List Bool) : List Bool :=
  [decide (MajBelow dec
    (fun i : Fin reps => A.output w (chunk (A.tapeLength w.length) i tape)) (thr w))]

theorem ofFn_chunk (s : ℕ) (t : Fin (reps * s) → Bool) (i : Fin reps) :
    chunk s i (List.ofFn t) = List.ofFn (seg reps s t i) := by
  rw [ofFn_seg]; rfl

open Classical in
/-- **The repeat-and-median machine as a D-A1 prefix-model algorithm.** One fixed machine
`medMachine 146 A.machine C`; tape length `reps · R(|w|)`; clock
`medClock 146 A.machine C |w| R(|w|) (A.time w) (TC w)`; printed word `medOutputGeneral`. -/
noncomputable def medAlgGeneral (hC : CmpSpecGeneral A C dec thr TC) : PrefixAlgorithm where
  machine := medMachine 146 A.machine C
  tapeLength := fun m => reps * A.tapeLength m
  time := fun w => medClock 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w)
  output := medOutputGeneral A dec thr
  runs := by
    intro w tape
    have hL : (List.ofFn tape).length = (146 + 1) * (A.tapeLength w.length) := by simp [reps]
    have hseg : ∀ i ≤ 146, ∃ g : Fin (A.tapeLength w.length) → Bool, List.ofFn g = chunk (A.tapeLength w.length) i (List.ofFn tape) := by
      intro i hi
      exact ⟨seg reps (A.tapeLength w.length) tape ⟨i, by simp [reps]; omega⟩,
        (ofFn_chunk (A.tapeLength w.length) tape ⟨i, by simp [reps]; omega⟩).symm⟩
    have hE : ∀ i ≤ 146, A.machine.OutputsWithin (pair w (chunk (A.tapeLength w.length) i (List.ofFn tape)))
        (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))) (A.time w) := by
      intro i hi
      obtain ⟨g, hg⟩ := hseg i hi
      have := A.runs w g
      rw [hg] at this
      exact this
    have hC' : ∀ i ≤ 146, C.OutputsWithin (pair w (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))))
        [decide (Below dec (thr w) (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))))] (TC w) := by
      intro i hi
      apply hC
      have hb := output_length_bound A.machine (hE i hi)
      rw [EncodedComplexity.pair_length, chunk_length (A.tapeLength w.length) 146 i _ hL hi] at hb
      unfold outBound
      omega
    have hmain := med_outputs 146 A.machine C w (A.tapeLength w.length) (A.time w) (TC w)
      (fun i => chunk (A.tapeLength w.length) i (List.ofFn tape)) (fun i => A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))
      (fun i => decide (Below dec (thr w) (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))))
      (fun i hi => chunk_length (A.tapeLength w.length) 146 i _ hL hi) hE hC'
    rw [pref_chunks (A.tapeLength w.length) 146 _ hL, acc_eq_card] at hmain
    have hout : medOutputGeneral A dec thr w (List.ofFn tape) = [decide (146 + 1 < 2 * Fintype.card
        {i : Fin (146 + 1) // decide (Below dec (thr w)
          (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))) = true})] := by
      unfold medOutputGeneral
      simp only [List.cons.injEq, and_true]
      apply decide_eq_decide.mpr
      simp only [decide_eq_true_eq]
      exact Iff.rfl
    change (medMachine 146 A.machine C).OutputsWithin _ (medOutputGeneral A dec thr w (List.ofFn tape)) _
    rw [hout]
    exact hmain

/-- The acceptance probability of `medAlgGeneral` is the probability of the majority event over the
uniform tape of length `reps · R(|w|)`, run `i` reading segment `i`. -/
theorem medAlgGeneral_prob (hC : CmpSpecGeneral A C dec thr TC) (w : List Bool) :
    (medAlgGeneral A C dec thr TC hC).prob w (· = [true]) =
      (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
        MajBelow dec
          (fun i => A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))) (thr w)) := by
  classical
  unfold PrefixAlgorithm.prob
  congr 1
  funext t
  simp only [medAlgGeneral, medOutputGeneral, List.cons.injEq, and_true, decide_eq_true_eq]
  simp only [ofFn_chunk]

/-- **YES side** (I:120-122): if one run of the estimator is within `a` of `c ≤ B` with probability
`≥ 2/3` and the threshold is `B + k/2` with `2a < k`, the median machine accepts with probability
`≥ 99/100`. -/
theorem medAlgGeneral_yes (hC : CmpSpecGeneral A C dec thr TC) (w : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k) (hthr : thr w = (B : ℝ) + (k : ℝ) / 2)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, dec out = some v ∧ |v - c| ≤ a))
    (hcB : c ≤ B) : 99 / 100 ≤ (medAlgGeneral A C dec thr TC hC).prob w (· = [true]) := by
  rw [medAlgGeneral_prob, hthr]
  exact (median_midpoint_testR dec (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a B k hk hE).2.1 hcB

/-- **NO side** (I:120-122): with `B + k ≤ c`, the median machine accepts with probability
`≤ 1/100`. -/
theorem medAlgGeneral_no (hC : CmpSpecGeneral A C dec thr TC) (w : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k) (hthr : thr w = (B : ℝ) + (k : ℝ) / 2)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, dec out = some v ∧ |v - c| ≤ a))
    (hBc : B + k ≤ c) : (medAlgGeneral A C dec thr TC hC).prob w (· = [true]) ≤ 1 / 100 := by
  rw [medAlgGeneral_prob, hthr]
  have h := (median_midpoint_testR dec (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a B k hk hE).2.2 hBc
  rw [Paper2.Unit4Shell.Amplification.prob_not] at h
  linarith

/-- **`medAlgGeneral` is polynomial** (D-A1 `Polynomial` of lane a-model) when the estimator is polynomial
and the comparator clock is polynomially bounded. -/
theorem medAlgGeneral_polynomial (hC : CmpSpecGeneral A C dec thr TC) (hA : A.Polynomial)
    (hT : ∃ cT dT : ℕ, ∀ w : List Bool, TC w ≤ cT * (w.length + 1) ^ dT) :
    (medAlgGeneral A C dec thr TC hC).Polynomial := by
  obtain ⟨cA, dA, hA⟩ := hA
  obtain ⟨cT, dT, hT⟩ := hT
  refine ⟨(3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA, dA + dT + 1, fun w => ?_⟩
  set N := w.length + 1
  have hN : 1 ≤ N := by omega
  set D := dA + dT + 1
  have hpA : N ^ dA ≤ N ^ D := Nat.pow_le_pow_right hN (by omega)
  have hpT : N ^ dT ≤ N ^ D := Nat.pow_le_pow_right hN (by omega)
  have hp1 : N ≤ N ^ D := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ D := Nat.pow_le_pow_right hN (by omega)
  have hs := (hA w).1
  have ht := (hA w).2
  have hc := hT w
  have hsD : A.tapeLength w.length ≤ cA * N ^ D := hs.trans (Nat.mul_le_mul_left _ hpA)
  have htD : A.time w ≤ cA * N ^ D := ht.trans (Nat.mul_le_mul_left _ hpA)
  have hcD : TC w ≤ cT * N ^ D := hc.trans (Nat.mul_le_mul_left _ hpT)
  have hX : w.length + A.tapeLength w.length + A.time w + TC w + 1 ≤ (3 + 2 * cA + cT) * N ^ D := by
    have e : (3 + 2 * cA + cT) * N ^ D = 3 * N ^ D + cA * N ^ D + cA * N ^ D + cT * N ^ D := by ring
    omega
  constructor
  · show reps * A.tapeLength w.length ≤ _
    have : reps * A.tapeLength w.length ≤ reps * (cA * N ^ D) := Nat.mul_le_mul_left _ hsD
    have e : ((3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA) * N ^ D =
        (3 + 2 * cA + cT) * Kc 146 A.machine C * N ^ D + reps * (cA * N ^ D) := by ring
    rw [e]
    exact this.trans (Nat.le_add_left _ _)
  · show medClock 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w) ≤ _
    have hm := medClock_le 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w)
    have hm2 : (w.length + A.tapeLength w.length + A.time w + TC w + 1) * Kc 146 A.machine C ≤
        (3 + 2 * cA + cT) * N ^ D * Kc 146 A.machine C := Nat.mul_le_mul_right _ hX
    have e : ((3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA) * N ^ D =
        (3 + 2 * cA + cT) * N ^ D * Kc 146 A.machine C + reps * cA * N ^ D := by ring
    rw [e]
    exact hm.trans (hm2.trans (Nat.le_add_right _ _))


#print axioms CurrentAdditive.ModelEndpointReview.medAlgGeneral_polynomial

open CurrentAdditive.SmallBias Paper2.YaoBppDraft
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- A numerical estimator in the manuscript's comparison model. `decode` is
semantic: it need not parse a dyadic word. The physical comparator receives
the public numerator `m` as the first field of `w` and decides whether the
output value is below the binary rational `m/2`. Its machine and polynomial
clock are fixed before the input and tape. Comparison is required on all
possible estimator output lengths, including unsuccessful outputs. -/
structure ComparisonEstimator (μ : YaoMeasure) (u : ℝ) where
  estimator : Paper2.SelectedTape.Algorithm
  decode : List Bool → Option ℝ
  comparator : BitMachine.Machine
  compareTime : List Bool → ℕ
  compareRuns : CmpSpecGeneral
    ((Paper2.HeaderStrip.selectedEstimator estimator).toPrefix)
    comparator decode Paper2.CmpOwner.thrW compareTime
  comparePoly : ∃ c d : ℕ, ∀ w : List Bool,
    compareTime w ≤ c * (w.length + 1) ^ d
  accurate : ∀ w c, Paper2.AModel.targetYao μ w = some c →
    2 / 3 ≤ estimator.prob w
      (fun out => ∃ v, decode out = some v ∧ |v - c| ≤ u)

def ComparisonEstimator.median {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) : Paper2.AModel.PrefixAlgorithm :=
  medAlgGeneral ((Paper2.HeaderStrip.selectedEstimator E.estimator).toPrefix)
    E.comparator E.decode Paper2.CmpOwner.thrW E.compareTime E.compareRuns

theorem ComparisonEstimator.median_poly {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) : E.median.Polynomial :=
  medAlgGeneral_polynomial _ _ _ _ _ E.compareRuns
    (Paper2.HeaderStrip.selectedEstimator_toPrefix_polynomial E.estimator)
    E.comparePoly

theorem ComparisonEstimator.median_tape {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (n : ℕ) :
    E.median.tapeLength n =
      (reps * (Paper2.HeaderStrip.selectedEstimator E.estimator).cR) *
        (n + 1) ^ (Paper2.HeaderStrip.selectedEstimator E.estimator).dR := by
  change reps * ((Paper2.HeaderStrip.selectedEstimator E.estimator).cR *
    (n + 1) ^ (Paper2.HeaderStrip.selectedEstimator E.estimator).dR) = _
  ring

private theorem median_shape {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) :
    ∃ c d : ℕ, ∀ n, E.median.tapeLength n = c * (n + 1) ^ d :=
  ⟨reps * (Paper2.HeaderStrip.selectedEstimator E.estimator).cR,
    (Paper2.HeaderStrip.selectedEstimator E.estimator).dR, E.median_tape⟩

def ComparisonEstimator.classifier {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) : Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.Algorithm.ofPrefixMonomial E.median E.median_poly
    (median_shape E)

theorem ComparisonEstimator.classifier_prob {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (w : List Bool) (P : List Bool → Prop) :
    E.classifier.prob w P = E.median.prob w P :=
  Paper2.SelectedTape.Algorithm.ofPrefixMonomial_prob
    E.median E.median_poly (median_shape E) w P

theorem ComparisonEstimator.header_accuracy {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (n : ℕ) (rest : List Bool) (c : ℕ)
    (hc : Paper2.AModel.targetYao μ rest = some c) :
    2 / 3 ≤ ((Paper2.HeaderStrip.selectedEstimator E.estimator).toPrefix).prob
      (natField n ++ rest)
      (fun out => ∃ v, E.decode out = some v ∧ |v - c| ≤ u) := by
  rw [Paper2.HeaderStrip.selectedEstimator_toPrefix_prob]
  exact E.accurate rest c hc

private theorem gap_ge_three (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) : 3 ≤ g := by
  have h : (3 : ℝ) ≤ g := by linarith
  exact_mod_cast h

private theorem header_arithmetic (u : ℝ) (hu : 0 ≤ u) (g B : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) :
    2 * B + (g - 1) = 2 * (B + 1) + (g - 3) := by
  have := gap_ge_three u hu g hg
  omega

/-- Both cost cases refer to the same valid indexed instance and its original
row-major matrix word. The stronger `g>2u+3` absorbs the two model-convention
bits uniformly, including Bob first without transposition. -/
theorem ComparisonEstimator.classifier_law {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ))
    (i : Instance) (hi : i.Valid) :
    (Paper2.Yao.Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold →
      99 / 100 ≤ E.classifier.prob
        (natField (2 * i.threshold + (g - 1)) ++
          Paper2.AModel.matrixWord i.rows i.cols i.table) (· = [true])) ∧
    (i.threshold + g ≤ Paper2.Yao.Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) →
      E.classifier.prob
        (natField (2 * i.threshold + (g - 1)) ++
          Paper2.AModel.matrixWord i.rows i.cols i.table) (· = [true]) ≤ 1 / 100) := by
  let rest := Paper2.AModel.matrixWord i.rows i.cols i.table
  let w := natField (2 * i.threshold + (g - 1)) ++ rest
  let c := μ.eval i
  let A := (Paper2.HeaderStrip.selectedEstimator E.estimator).toPrefix
  have htarget : Paper2.AModel.targetYao μ rest = some c :=
    Paper2.YaoSelected.target_matrix μ i hi
  have hacc : 2 / 3 ≤ A.prob w
      (fun out => ∃ v, E.decode out = some v ∧ |v - c| ≤ u) :=
    E.header_accuracy _ _ _ htarget
  have hgap : 2 * u < ((g - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (gap_ge_three u hu g hg)]
    push_cast
    linarith
  have hthr : Paper2.CmpOwner.thrW w =
      ((i.threshold + 1 : ℕ) : ℝ) + ((g - 3 : ℕ) : ℝ) / 2 := by
    unfold w
    rw [header_arithmetic u hu g i.threshold hg]
    exact Paper2.CmpOwner.thrW_midpoint (i.threshold + 1) (g - 3) rest
  constructor
  · intro hD
    have hc : c ≤ i.threshold + 1 := by
      have hw := (measure_window μ i).2
      omega
    rw [E.classifier_prob]
    exact medAlgGeneral_yes A E.comparator E.decode Paper2.CmpOwner.thrW
      E.compareTime E.compareRuns w c u (i.threshold + 1) (g - 3)
      hgap hthr hacc hc
  · intro hD
    have hc : i.threshold + 1 + (g - 3) ≤ c := by
      have hw := (measure_window μ i).1
      have hg3 := gap_ge_three u hu g hg
      omega
    rw [E.classifier_prob]
    exact medAlgGeneral_no A E.comparator E.decode Paper2.CmpOwner.thrW
      E.compareTime E.compareRuns w c u (i.threshold + 1) (g - 3)
      hgap hthr hacc hc

def ComparisonEstimator.sourceDecider {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G)) :
    Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.pullback (canonicalClassifierWord g G) hprint E.classifier

theorem ComparisonEstimator.sourceDecider_decides {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ))
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G)) :
    (E.sourceDecider g G hprint).Decides G.L (1 / 3) := by
  intro input
  let i := sourceCanonicalInstance g G input
  have hi : i.Valid := sourceCanonicalInstance_valid g G input
  have hgap := sourceCanonicalInstance_yes_no g G input
  have hthreshold : i.threshold =
      2 * sourceExactAddressWidth g G input + 4 * v27GapParameter g + 2 := rfl
  have h := E.classifier_law hu g hg i hi
  constructor
  · intro hm
    have hD : Paper2.Yao.Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ i.threshold := by
      rw [hthreshold]
      exact hgap.1 hm
    rw [ComparisonEstimator.sourceDecider, Paper2.SelectedTape.pullback_prob]
    have hyes : 99 / 100 ≤ E.classifier.prob
        (canonicalClassifierWord g G input) (· = [true]) := by
      simpa only [canonicalClassifierWord, canonicalEstimatorWord] using h.1 hD
    linarith
  · intro hn
    have hD : i.threshold + g ≤ Paper2.Yao.Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) := by
      rw [hthreshold]
      exact hgap.2 hn
    rw [ComparisonEstimator.sourceDecider, Paper2.SelectedTape.pullback_prob]
    have hno : E.classifier.prob
        (canonicalClassifierWord g G input) (· = [true]) ≤ 1 / 100 := by
      simpa only [canonicalClassifierWord, canonicalEstimatorWord] using h.2 hD
    linarith

theorem comparison_np_subset_bpp {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (hu : 0 ≤ u)
    (G : Paper2.YaoX05Draft.GLSourceDraft
      (v27GapParameter (sourceEstimatorGap u)))
    (hard : NPHard G.L) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  let g := sourceEstimatorGap u
  have hencoded := physical_source_encoded_polytime g G
  have hprint : BitMachine.Polytime (canonicalClassifierWord g G) :=
    canonicalClassifierWord_polytime_of_encoded g
      (by have := gap_ge_three u hu g (sourceEstimatorGap_bound u); omega)
      G hencoded
  have hmem : Paper2.SelectedTape.InBPP G.L :=
    ⟨E.sourceDecider g G hprint,
      E.sourceDecider_decides hu g (sourceEstimatorGap_bound u) G hprint⟩
  exact Paper2.SelectedTape.np_subset_inBPP hard hmem

#print axioms comparison_np_subset_bpp

theorem ComparisonEstimator.classifier_tape_zero {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (hz : E.estimator.cR = 0)
    (x : List Bool) : E.classifier.tapeLength x = 0 := by
  have hh : (Paper2.HeaderStrip.selectedEstimator E.estimator).cR = 0 := by
    simp [Paper2.HeaderStrip.selectedEstimator, Paper2.SelectedTape.pullback, hz]
  have hm : E.median.tapeLength x.length = 0 := by
    rw [E.median_tape]
    simp [hh]
  have hchosen := Classical.choose_spec (Classical.choose_spec (median_shape E)) x.length
  have heq : E.classifier.tapeLength x = E.median.tapeLength x.length := by
    change (Classical.choose (median_shape E)) * (x.length + 1) ^
      (Classical.choose (Classical.choose_spec (median_shape E))) = _
    exact hchosen.symm
  exact heq.trans hm

def ComparisonEstimator.sourceDecision {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) : Bool :=
  decide ((E.sourceDecider g G hprint).output input [] = [true])

theorem ComparisonEstimator.sourceDecider_output_singleton
    {μ : YaoMeasure} {u : ℝ} (E : ComparisonEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) :
    ∃ b, (E.sourceDecider g G hprint).output input [] = [b] := by
  rw [ComparisonEstimator.sourceDecider, Paper2.SelectedTape.pullback_output]
  unfold ComparisonEstimator.classifier Paper2.SelectedTape.Algorithm.ofPrefixMonomial
  unfold ComparisonEstimator.median medAlgGeneral medOutputGeneral
  exact ⟨_, rfl⟩

theorem ComparisonEstimator.sourceDecider_output_bit
    {μ : YaoMeasure} {u : ℝ} (E : ComparisonEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) :
    (E.sourceDecider g G hprint).output input [] =
      [E.sourceDecision g G hprint input] := by
  obtain ⟨b, hb⟩ := E.sourceDecider_output_singleton g G hprint input
  rw [hb]
  cases b <;> simp [ComparisonEstimator.sourceDecision, hb]

theorem ComparisonEstimator.sourceDecision_polytime
    {μ : YaoMeasure} {u : ℝ} (E : ComparisonEstimator μ u)
    (hz : E.estimator.cR = 0) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G)) :
    BitMachine.Polytime (fun input => [E.sourceDecision g G hprint input]) := by
  let A := E.sourceDecider g G hprint
  have hzClass : E.classifier.cR = 0 := by
    have h := E.classifier_tape_zero hz []
    simpa [Paper2.SelectedTape.Algorithm.tapeLength] using h
  have hzA : ∀ x, A.tapeLength x = 0 := by
    intro x
    simp [A, ComparisonEstimator.sourceDecider, Paper2.SelectedTape.pullback,
      Paper2.SelectedTape.Algorithm.tapeLength, hzClass]
  have hphysical := zeroTapeOutputPolytime A hzA
  have heq : (fun input => [E.sourceDecision g G hprint input]) =
      (fun input => A.output input []) := by
    funext input
    exact (E.sourceDecider_output_bit g G hprint input).symm
  rw [heq]
  exact hphysical

theorem ComparisonEstimator.sourceDecision_correct
    {μ : YaoMeasure} {u : ℝ} (E : ComparisonEstimator μ u)
    (hu : 0 ≤ u) (hz : E.estimator.cR = 0) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ))
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) :
    input ∈ G.L ↔ E.sourceDecision g G hprint input = true := by
  let A := E.sourceDecider g G hprint
  have hzClass : E.classifier.cR = 0 := by
    have h := E.classifier_tape_zero hz []
    simpa [Paper2.SelectedTape.Algorithm.tapeLength] using h
  have hzA : ∀ x, A.tapeLength x = 0 := by
    intro x
    simp [A, ComparisonEstimator.sourceDecider, Paper2.SelectedTape.pullback,
      Paper2.SelectedTape.Algorithm.tapeLength, hzClass]
  have hd : A.Decides G.L (1 / 3) :=
    E.sourceDecider_decides hu g hg G hprint
  have hp := zeroTapeProb A hzA input (· = [true])
  constructor
  · intro hm
    have hyes := (hd input).1 hm
    rw [hp] at hyes
    by_contra hn
    have hfalse : A.output input [] ≠ [true] := by
      simpa [ComparisonEstimator.sourceDecision, A] using hn
    simp [hfalse] at hyes
    norm_num at hyes
  · intro hbit
    by_contra hn
    have hno := (hd input).2 hn
    have htrue : A.output input [] = [true] := by
      simpa [ComparisonEstimator.sourceDecision, A] using hbit
    rw [hp, if_pos htrue] at hno
    norm_num at hno

theorem comparison_p_equals_np {μ : YaoMeasure} {u : ℝ}
    (E : ComparisonEstimator μ u) (hu : 0 ≤ u)
    (hz : E.estimator.cR = 0)
    (G : Paper2.YaoX05Draft.GLSourceDraft
      (v27GapParameter (sourceEstimatorGap u)))
    (hard : NPHard G.L) : PEqualsNP := by
  let g := sourceEstimatorGap u
  have hencoded := physical_source_encoded_polytime g G
  have hprint : BitMachine.Polytime (canonicalClassifierWord g G) :=
    canonicalClassifierWord_polytime_of_encoded g
      (by have := gap_ge_three u hu g (sourceEstimatorGap_bound u); omega)
      G hencoded
  have hmem : ComplexityReductionClosure.InP G.L :=
    ⟨E.sourceDecision g G hprint,
      E.sourceDecision_polytime hz g G hprint,
      E.sourceDecision_correct hu hz g (sourceEstimatorGap_bound u) G hprint⟩
  exact p_equals_np_of_np_subset_p
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard hmem)

#print axioms comparison_p_equals_np

/-- The exact total-output manuscript interface used by the endpoint. `value`
assigns a number to every output word; the comparator is physically clocked
on every possible output up to the estimator's machine output bound. The
thresholds needed for the gap proof are the public binary rationals `m/2`
encoded as the first natural-number field of `w`. A model with comparison
against every binary rational supplies this selected-threshold interface. -/
structure NumericComparisonEstimator (μ : YaoMeasure) (u : ℝ) where
  estimator : Paper2.SelectedTape.Algorithm
  value : List Bool → ℝ
  comparator : BitMachine.Machine
  compareTime : List Bool → ℕ
  compareRuns : ∀ w out,
    out.length ≤ outBound
      (Paper2.HeaderStrip.selectedEstimator estimator).machine
      w.length
      ((Paper2.HeaderStrip.selectedEstimator estimator).toPrefix.tapeLength w.length)
      ((Paper2.HeaderStrip.selectedEstimator estimator).toPrefix.time w) →
    comparator.OutputsWithin (pair w out)
      [decide (value out < Paper2.CmpOwner.thrW w)] (compareTime w)
  comparePoly : ∃ c d : ℕ, ∀ w : List Bool,
    compareTime w ≤ c * (w.length + 1) ^ d
  accurate : ∀ w c, Paper2.AModel.targetYao μ w = some c →
    2 / 3 ≤ estimator.prob w (fun out => |value out - c| ≤ u)

def NumericComparisonEstimator.toComparison {μ : YaoMeasure} {u : ℝ}
    (E : NumericComparisonEstimator μ u) : ComparisonEstimator μ u where
  estimator := E.estimator
  decode := fun out => some (E.value out)
  comparator := E.comparator
  compareTime := E.compareTime
  compareRuns := by
    intro w out hbound
    simpa [Below] using
      E.compareRuns w out hbound
  comparePoly := E.comparePoly
  accurate := by
    intro w c hc
    simpa using E.accurate w c hc

theorem numeric_comparison_np_subset_bpp {μ : YaoMeasure} {u : ℝ}
    (E : NumericComparisonEstimator μ u) (hu : 0 ≤ u)
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  let G := GF (v27GapParameter (sourceEstimatorGap u))
  have hhard : NPHard G.L := by rw [hL]; exact hard
  exact comparison_np_subset_bpp E.toComparison hu G hhard

theorem numeric_comparison_p_equals_np {μ : YaoMeasure} {u : ℝ}
    (E : NumericComparisonEstimator μ u) (hu : 0 ≤ u)
    (hz : E.estimator.cR = 0)
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3) : PEqualsNP := by
  let G := GF (v27GapParameter (sourceEstimatorGap u))
  have hhard : NPHard G.L := by rw [hL]; exact hard
  exact comparison_p_equals_np E.toComparison hu hz G hhard

#print axioms numeric_comparison_np_subset_bpp
#print axioms numeric_comparison_p_equals_np

end CurrentAdditive.ModelEndpointReview
