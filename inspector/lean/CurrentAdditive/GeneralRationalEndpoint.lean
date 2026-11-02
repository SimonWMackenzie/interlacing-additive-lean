import CurrentAdditive.GeneralComparatorMedian
import CurrentAdditive.RationalCodeAdapter

/-! Private continuation from the frozen general-comparator packet. The
comparator is now presented on a canonical code for every signed binary
rational. The median machine runs on all words, while numerical correctness
is used only at a valid source-produced threshold header. -/

noncomputable section
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace CurrentAdditive.ModelEndpointReview.RationalEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification (reps)
open Paper2.MedianOwner Paper2.MedianOwner.Med
open Paper2.MedianOwner.Final (chunk chunk_length pref_chunks acc_eq_card medClock_le Kc)
open Paper2.AModel (PrefixAlgorithm)
open CurrentAdditive.ModelEndpointReview.RationalCodeAdapter
open Classical

def rationalCode (z : ℤ) (j : ℕ) : List Bool :=
  if j = 1 ∧ 0 ≤ z then false :: natField z.toNat
  else true :: Paper2.AModel.encodeDyadic z j

theorem rationalCode_half (m : ℕ) :
    rationalCode (m : ℤ) 1 = false :: natField m := by
  simp [rationalCode]

theorem rationalCode_half_length (m : ℕ) :
    (rationalCode (m : ℤ) 1).length = 2 * m.bits.length + 2 := by
  simp [rationalCode_half, natField, field_length]

/-- A total comparator output function with a fixed all-word physical clock.
The correctness law covers every signed dyadic `z/2^j`, not just the midpoint
family; arbitrary estimator output words are included. -/
structure RationalComparator (value : List Bool → ℝ) where
  output : List Bool → List Bool
  physical : BitMachine.Polytime output
  singleton : ∀ input, ∃ b, output input = [b]
  correct : ∀ z : ℤ, ∀ j : ℕ, ∀ out : List Bool,
    output (pair (rationalCode z j) out) =
      [decide (value out < (z : ℝ) / 2 ^ j)]

variable (A : PrefixAlgorithm) (C : Machine)
  (judge : List Bool → List Bool → Bool) (TC : List Bool → ℕ)

def CmpSpecJudge : Prop :=
  ∀ w out, out.length ≤ outBound A.machine w.length (A.tapeLength w.length) (A.time w) →
    C.OutputsWithin (pair w out) [judge w out] (TC w)

def medOutputJudge (w tape : List Bool) : List Bool :=
  [decide (reps < 2 * Fintype.card
    {i : Fin reps // judge w (A.output w (chunk (A.tapeLength w.length) i tape)) = true})]

noncomputable def medAlgJudge (hC : CmpSpecJudge A C judge TC) : PrefixAlgorithm where
  machine := medMachine 146 A.machine C
  tapeLength := fun m => reps * A.tapeLength m
  time := fun w => medClock 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w)
  output := medOutputJudge A judge
  runs := by
    intro w tape
    have hL : (List.ofFn tape).length = (146 + 1) * (A.tapeLength w.length) := by simp [reps]
    have hseg : ∀ i ≤ 146, ∃ g : Fin (A.tapeLength w.length) → Bool,
        List.ofFn g = chunk (A.tapeLength w.length) i (List.ofFn tape) := by
      intro i hi
      exact ⟨seg reps (A.tapeLength w.length) tape ⟨i, by simp [reps]; omega⟩,
        (CurrentAdditive.ModelEndpointReview.ofFn_chunk
          (A.tapeLength w.length) tape ⟨i, by simp [reps]; omega⟩).symm⟩
    have hE : ∀ i ≤ 146, A.machine.OutputsWithin
        (pair w (chunk (A.tapeLength w.length) i (List.ofFn tape)))
        (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))) (A.time w) := by
      intro i hi
      obtain ⟨g, hg⟩ := hseg i hi
      have := A.runs w g
      rw [hg] at this
      exact this
    have hC' : ∀ i ≤ 146, C.OutputsWithin
        (pair w (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))))
        [judge w (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))] (TC w) := by
      intro i hi
      apply hC
      have hb := output_length_bound A.machine (hE i hi)
      rw [EncodedComplexity.pair_length,
        chunk_length (A.tapeLength w.length) 146 i _ hL hi] at hb
      unfold outBound
      omega
    have hmain := med_outputs 146 A.machine C w (A.tapeLength w.length)
      (A.time w) (TC w)
      (fun i => chunk (A.tapeLength w.length) i (List.ofFn tape))
      (fun i => A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))
      (fun i => judge w (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))))
      (fun i hi => chunk_length (A.tapeLength w.length) 146 i _ hL hi) hE hC'
    rw [pref_chunks (A.tapeLength w.length) 146 _ hL, acc_eq_card] at hmain
    change (medMachine 146 A.machine C).OutputsWithin _
      (medOutputJudge A judge w (List.ofFn tape)) _
    unfold medOutputJudge
    simpa only [reps] using hmain

theorem medAlgJudge_prob (hC : CmpSpecJudge A C judge TC) (w : List Bool) :
    (medAlgJudge A C judge TC hC).prob w (· = [true]) =
      (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
        reps < 2 * Fintype.card {i : Fin reps //
          judge w (A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))) = true}) := by
  classical
  unfold PrefixAlgorithm.prob
  congr 1
  funext t
  simp only [medAlgJudge, medOutputJudge, List.cons.injEq, and_true, decide_eq_true_eq]
  simp only [CurrentAdditive.ModelEndpointReview.ofFn_chunk]

theorem medAlgJudge_polynomial (hC : CmpSpecJudge A C judge TC)
    (hA : A.Polynomial)
    (hT : ∃ cT dT : ℕ, ∀ w : List Bool,
      TC w ≤ cT * (w.length + 1) ^ dT) :
    (medAlgJudge A C judge TC hC).Polynomial := by
  obtain ⟨cA, dA, hA⟩ := hA
  obtain ⟨cT, dT, hT⟩ := hT
  refine ⟨(3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA,
    dA + dT + 1, fun w => ?_⟩
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
  have hsD : A.tapeLength w.length ≤ cA * N ^ D :=
    hs.trans (Nat.mul_le_mul_left _ hpA)
  have htD : A.time w ≤ cA * N ^ D :=
    ht.trans (Nat.mul_le_mul_left _ hpA)
  have hcD : TC w ≤ cT * N ^ D :=
    hc.trans (Nat.mul_le_mul_left _ hpT)
  have hX : w.length + A.tapeLength w.length + A.time w + TC w + 1 ≤
      (3 + 2 * cA + cT) * N ^ D := by
    have e : (3 + 2 * cA + cT) * N ^ D =
      3 * N ^ D + cA * N ^ D + cA * N ^ D + cT * N ^ D := by ring
    omega
  constructor
  · show reps * A.tapeLength w.length ≤ _
    have h := Nat.mul_le_mul_left reps hsD
    have e : ((3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA) * N ^ D =
        (3 + 2 * cA + cT) * Kc 146 A.machine C * N ^ D +
          reps * (cA * N ^ D) := by ring
    rw [e]
    exact h.trans (Nat.le_add_left _ _)
  · show medClock 146 A.machine C w.length (A.tapeLength w.length)
        (A.time w) (TC w) ≤ _
    have hm := medClock_le 146 A.machine C w.length
      (A.tapeLength w.length) (A.time w) (TC w)
    have hm2 : (w.length + A.tapeLength w.length + A.time w + TC w + 1) *
        Kc 146 A.machine C ≤
        (3 + 2 * cA + cT) * N ^ D * Kc 146 A.machine C :=
      Nat.mul_le_mul_right _ hX
    have e : ((3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA) * N ^ D =
        (3 + 2 * cA + cT) * N ^ D * Kc 146 A.machine C +
          reps * cA * N ^ D := by ring
    rw [e]
    exact hm.trans (hm2.trans (Nat.le_add_right _ _))

def RationalComparator.judgeBit {value : List Bool → ℝ}
    (R : RationalComparator value) (w out : List Bool) : Bool :=
  decide (R.output (adapt (pair w out)) = [true])

private theorem singleton_bit {value : List Bool → ℝ}
    (R : RationalComparator value) (input : List Bool) :
    R.output input = [decide (R.output input = [true])] := by
  obtain ⟨b, hb⟩ := R.singleton input
  rw [hb]
  cases b <;> simp [hb]

private theorem composed_polytime {value : List Bool → ℝ}
    (R : RationalComparator value) :
    BitMachine.Polytime (R.output ∘ adapt) :=
  BitMachineComposition.polytime_comp polytime R.physical

private noncomputable def composedMachine {value : List Bool → ℝ}
    (R : RationalComparator value) : Machine :=
  Classical.choose (composed_polytime R)

private noncomputable def composedC {value : List Bool → ℝ}
    (R : RationalComparator value) : ℕ :=
  Classical.choose (Classical.choose_spec (composed_polytime R))

private noncomputable def composedD {value : List Bool → ℝ}
    (R : RationalComparator value) : ℕ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (composed_polytime R)))

private theorem composedRuns {value : List Bool → ℝ}
    (R : RationalComparator value) (input : List Bool) :
    (composedMachine R).OutputsWithin input (R.output (adapt input))
      (composedC R * (input.length + 1) ^ composedD R) := by
  exact Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (composed_polytime R))) input

private noncomputable def estimatorC (A : PrefixAlgorithm)
    (hA : A.Polynomial) : ℕ := Classical.choose hA

private noncomputable def estimatorD (A : PrefixAlgorithm)
    (hA : A.Polynomial) : ℕ :=
  Classical.choose (Classical.choose_spec hA)

private theorem estimatorBounds (A : PrefixAlgorithm)
    (hA : A.Polynomial) (w : List Bool) :
    A.tapeLength w.length ≤ estimatorC A hA *
        (w.length + 1) ^ estimatorD A hA ∧
      A.time w ≤ estimatorC A hA *
        (w.length + 1) ^ estimatorD A hA :=
  Classical.choose_spec (Classical.choose_spec hA) w

private def clockK (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ :=
  5 + estimatorC A hA + estimatorC A hA * A.machine.pushBound

private noncomputable def cmpClock {value : List Bool → ℝ}
    (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : RationalComparator value) (w : List Bool) : ℕ :=
  composedC R * (clockK A hA *
    (w.length + 1) ^ (estimatorD A hA + 1)) ^ composedD R

private theorem cmpClock_poly {value : List Bool → ℝ}
    (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : RationalComparator value) :
    ∃ c d : ℕ, ∀ w : List Bool,
      cmpClock A hA R w ≤ c * (w.length + 1) ^ d := by
  refine ⟨composedC R * (clockK A hA) ^ composedD R,
    (estimatorD A hA + 1) * composedD R, ?_⟩
  intro w
  simp only [cmpClock]
  rw [mul_pow]
  simp only [← pow_mul]
  simp only [Nat.mul_assoc]
  exact le_rfl

private theorem cmpClock_covers {value : List Bool → ℝ}
    (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : RationalComparator value) (w out : List Bool)
    (hout : out.length ≤ outBound A.machine w.length
      (A.tapeLength w.length) (A.time w)) :
    composedC R * ((pair w out).length + 1) ^ composedD R ≤
      cmpClock A hA R w := by
  let N := w.length + 1
  let X := N ^ (estimatorD A hA + 1)
  have hN : 1 ≤ N := by omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hN
  have hpow : N ^ estimatorD A hA ≤ X :=
    Nat.pow_le_pow_right hN (by omega)
  have hw : w.length ≤ X := by
    have hp : N ≤ X := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ X := Nat.pow_le_pow_right hN (by omega)
    omega
  have hwplus : w.length + 1 ≤ X := by
    calc w.length + 1 = N := rfl
      _ ≤ X := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hs := (estimatorBounds A hA w).1
  have ht := (estimatorBounds A hA w).2
  have hsX : A.tapeLength w.length ≤ estimatorC A hA * X :=
    hs.trans (Nat.mul_le_mul_left _ hpow)
  have htX : A.time w ≤ estimatorC A hA * X :=
    ht.trans (Nat.mul_le_mul_left _ hpow)
  have hpush : A.time w * A.machine.pushBound ≤
      estimatorC A hA * X * A.machine.pushBound :=
    Nat.mul_le_mul_right _ htX
  have hlength : (pair w out).length + 1 ≤ clockK A hA * X := by
    rw [pair_length]
    unfold outBound at hout
    have e : clockK A hA * X =
        5 * X + estimatorC A hA * X +
          estimatorC A hA * X * A.machine.pushBound := by
      unfold clockK
      ring
    rw [e]
    omega
  have hp : ((pair w out).length + 1) ^ composedD R ≤
      (clockK A hA * X) ^ composedD R := by gcongr
  exact Nat.mul_le_mul_left _ hp

private theorem judgeSpec {value : List Bool → ℝ}
    (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : RationalComparator value) :
    CmpSpecJudge A (composedMachine R) R.judgeBit (cmpClock A hA R) := by
  intro w out hout
  have hr := composedRuns R (pair w out)
  rw [singleton_bit R (adapt (pair w out))] at hr
  change (composedMachine R).OutputsWithin (pair w out)
    [R.judgeBit w out] (composedC R * ((pair w out).length + 1) ^ composedD R) at hr
  exact outputsWithin_mono _ hr (cmpClock_covers A hA R w out hout)

theorem RationalComparator.judge_header {value : List Bool → ℝ}
    (R : RationalComparator value) (m : ℕ) (rest out : List Bool) :
    R.judgeBit (natField m ++ rest) out =
      decide (value out < (m : ℝ) / 2) := by
  unfold RationalComparator.judgeBit
  rw [adapt_header, ← rationalCode_half]
  rw [R.correct (m : ℤ) 1 out]
  simp

private theorem judge_prob_eq (hC : CmpSpecJudge A C judge TC)
    (dec : List Bool → Option ℝ) (w : List Bool) (θ : ℝ)
    (hjudge : ∀ out, judge w out = decide (Below dec θ out)) :
    (medAlgJudge A C judge TC hC).prob w (· = [true]) =
      (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
        MajBelow dec
          (fun i => A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))) θ) := by
  rw [medAlgJudge_prob]
  congr 1
  funext t
  simp only [MajBelow, hjudge, decide_eq_true_eq]

theorem medAlgJudge_yes (hC : CmpSpecJudge A C judge TC)
    (dec : List Bool → Option ℝ) (w : List Bool) (c : ℕ) (a : ℝ)
    (B k : ℕ) (hk : 2 * a < k)
    (hjudge : ∀ out, judge w out =
      decide (Below dec ((B : ℝ) + (k : ℝ) / 2) out))
    (hE : 2 / 3 ≤ A.prob w
      (fun out => ∃ v, dec out = some v ∧ |v - c| ≤ a))
    (hcB : c ≤ B) :
    99 / 100 ≤ (medAlgJudge A C judge TC hC).prob w (· = [true]) := by
  rw [judge_prob_eq A C judge TC hC dec w _ hjudge]
  exact (median_midpoint_testR dec (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a B k hk hE).2.1 hcB

theorem medAlgJudge_no (hC : CmpSpecJudge A C judge TC)
    (dec : List Bool → Option ℝ) (w : List Bool) (c : ℕ) (a : ℝ)
    (B k : ℕ) (hk : 2 * a < k)
    (hjudge : ∀ out, judge w out =
      decide (Below dec ((B : ℝ) + (k : ℝ) / 2) out))
    (hE : 2 / 3 ≤ A.prob w
      (fun out => ∃ v, dec out = some v ∧ |v - c| ≤ a))
    (hBc : B + k ≤ c) :
    (medAlgJudge A C judge TC hC).prob w (· = [true]) ≤ 1 / 100 := by
  rw [judge_prob_eq A C judge TC hC dec w _ hjudge]
  have h := (median_midpoint_testR dec (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a B k hk hE).2.2 hBc
  rw [Paper2.Unit4Shell.Amplification.prob_not] at h
  linarith

open CurrentAdditive.SmallBias Paper2.YaoBppDraft

/-- Literal all-signed-binary-rational comparison model. Numerical values are
semantic and total on every output word; the single comparison machine has a
global all-word polynomial clock and a Boolean output on malformed inputs.
Only accuracy is restricted to valid matrix words, exactly as in the source. -/
structure AllRationalEstimator (μ : YaoMeasure) (u : ℝ) where
  estimator : Paper2.SelectedTape.Algorithm
  value : List Bool → ℝ
  comparator : RationalComparator value
  accurate : ∀ w c, Paper2.AModel.targetYao μ w = some c →
    2 / 3 ≤ estimator.prob w (fun out => |value out - c| ≤ u)

private def AllRationalEstimator.headerEstimator {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) : PrefixAlgorithm :=
  (Paper2.HeaderStrip.selectedEstimator E.estimator).toPrefix

private theorem AllRationalEstimator.headerPoly {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) : E.headerEstimator.Polynomial :=
  Paper2.HeaderStrip.selectedEstimator_toPrefix_polynomial E.estimator

def AllRationalEstimator.median {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) : PrefixAlgorithm :=
  medAlgJudge E.headerEstimator (composedMachine E.comparator)
    E.comparator.judgeBit (cmpClock E.headerEstimator E.headerPoly E.comparator)
    (judgeSpec E.headerEstimator E.headerPoly E.comparator)

theorem AllRationalEstimator.median_poly {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) : E.median.Polynomial :=
  medAlgJudge_polynomial E.headerEstimator (composedMachine E.comparator)
    E.comparator.judgeBit (cmpClock E.headerEstimator E.headerPoly E.comparator)
    (judgeSpec E.headerEstimator E.headerPoly E.comparator)
    E.headerPoly (cmpClock_poly E.headerEstimator E.headerPoly E.comparator)

theorem AllRationalEstimator.median_tape {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (n : ℕ) :
    E.median.tapeLength n =
      (reps * (Paper2.HeaderStrip.selectedEstimator E.estimator).cR) *
        (n + 1) ^ (Paper2.HeaderStrip.selectedEstimator E.estimator).dR := by
  change reps * ((Paper2.HeaderStrip.selectedEstimator E.estimator).cR *
    (n + 1) ^ (Paper2.HeaderStrip.selectedEstimator E.estimator).dR) = _
  ring

private theorem median_shape {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) :
    ∃ c d : ℕ, ∀ n, E.median.tapeLength n = c * (n + 1) ^ d :=
  ⟨reps * (Paper2.HeaderStrip.selectedEstimator E.estimator).cR,
    (Paper2.HeaderStrip.selectedEstimator E.estimator).dR, E.median_tape⟩

def AllRationalEstimator.classifier {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) : Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.Algorithm.ofPrefixMonomial E.median E.median_poly
    (median_shape E)

theorem AllRationalEstimator.classifier_prob {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (w : List Bool) (P : List Bool → Prop) :
    E.classifier.prob w P = E.median.prob w P :=
  Paper2.SelectedTape.Algorithm.ofPrefixMonomial_prob
    E.median E.median_poly (median_shape E) w P

theorem AllRationalEstimator.header_accuracy {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (n : ℕ) (rest : List Bool) (c : ℕ)
    (hc : Paper2.AModel.targetYao μ rest = some c) :
    2 / 3 ≤ E.headerEstimator.prob (natField n ++ rest)
      (fun out => ∃ v, some (E.value out) = some v ∧ |v - c| ≤ u) := by
  rw [AllRationalEstimator.headerEstimator,
    Paper2.HeaderStrip.selectedEstimator_toPrefix_prob]
  simpa using E.accurate rest c hc

private theorem gap_ge_three (u : ℝ) (hu : 0 ≤ u) (g : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) : 3 ≤ g := by
  have h : (3 : ℝ) ≤ g := by linarith
  exact_mod_cast h

private theorem header_arithmetic (u : ℝ) (hu : 0 ≤ u) (g B : ℕ)
    (hg : 2 * u + 3 < (g : ℝ)) :
    2 * B + (g - 1) = 2 * (B + 1) + (g - 3) := by
  have := gap_ge_three u hu g hg
  omega

/-- Four-measure success law on the same indexed, nonempty source table. -/
theorem AllRationalEstimator.classifier_law {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (hu : 0 ≤ u) (g : ℕ)
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
  let m := 2 * i.threshold + (g - 1)
  let w := natField m ++ rest
  let c := μ.eval i
  let A := E.headerEstimator
  have htarget : Paper2.AModel.targetYao μ rest = some c :=
    Paper2.YaoSelected.target_matrix μ i hi
  have hacc : 2 / 3 ≤ A.prob w
      (fun out => ∃ v, some (E.value out) = some v ∧ |v - c| ≤ u) :=
    E.header_accuracy _ _ _ htarget
  have hgap : 2 * u < ((g - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (gap_ge_three u hu g hg)]
    push_cast
    linarith
  have hthr : Paper2.CmpOwner.thrW w =
      ((i.threshold + 1 : ℕ) : ℝ) + ((g - 3 : ℕ) : ℝ) / 2 := by
    unfold w m
    rw [header_arithmetic u hu g i.threshold hg]
    exact Paper2.CmpOwner.thrW_midpoint (i.threshold + 1) (g - 3) rest
  have hjudge : ∀ out, E.comparator.judgeBit w out =
      decide (Below (fun out => some (E.value out))
        (((i.threshold + 1 : ℕ) : ℝ) + ((g - 3 : ℕ) : ℝ) / 2) out) := by
    intro out
    have h := E.comparator.judge_header m rest out
    have hmid : ((m : ℕ) : ℝ) / 2 =
        ((i.threshold + 1 : ℕ) : ℝ) + ((g - 3 : ℕ) : ℝ) / 2 := by
      calc (m : ℝ) / 2 = Paper2.CmpOwner.thrW w := by
             exact (Paper2.CmpOwner.thrW_natField m rest).symm
        _ = _ := hthr
    rw [hmid] at h
    simpa [Below] using h
  constructor
  · intro hD
    have hc : c ≤ i.threshold + 1 := by
      have hw := (measure_window μ i).2
      omega
    rw [E.classifier_prob]
    exact medAlgJudge_yes A (composedMachine E.comparator)
      E.comparator.judgeBit (cmpClock A E.headerPoly E.comparator)
      (judgeSpec A E.headerPoly E.comparator)
      (fun out => some (E.value out)) w c u (i.threshold + 1) (g - 3)
      hgap hjudge hacc hc
  · intro hD
    have hc : i.threshold + 1 + (g - 3) ≤ c := by
      have hw := (measure_window μ i).1
      have hg3 := gap_ge_three u hu g hg
      omega
    rw [E.classifier_prob]
    exact medAlgJudge_no A (composedMachine E.comparator)
      E.comparator.judgeBit (cmpClock A E.headerPoly E.comparator)
      (judgeSpec A E.headerPoly E.comparator)
      (fun out => some (E.value out)) w c u (i.threshold + 1) (g - 3)
      hgap hjudge hacc hc

def AllRationalEstimator.sourceDecider {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G)) :
    Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.pullback (canonicalClassifierWord g G) hprint E.classifier

theorem AllRationalEstimator.sourceDecider_decides {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (hu : 0 ≤ u) (g : ℕ)
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
    rw [AllRationalEstimator.sourceDecider, Paper2.SelectedTape.pullback_prob]
    have hyes : 99 / 100 ≤ E.classifier.prob
        (canonicalClassifierWord g G input) (· = [true]) := by
      simpa only [canonicalClassifierWord, canonicalEstimatorWord] using h.1 hD
    linarith
  · intro hn
    have hD : i.threshold + g ≤ Paper2.Yao.Dalt .alice
        (ProtocolVerifier.tableGame i.rows i.cols i.table) := by
      rw [hthreshold]
      exact hgap.2 hn
    rw [AllRationalEstimator.sourceDecider, Paper2.SelectedTape.pullback_prob]
    have hno : E.classifier.prob
        (canonicalClassifierWord g G input) (· = [true]) ≤ 1 / 100 := by
      simpa only [canonicalClassifierWord, canonicalEstimatorWord] using h.2 hD
    linarith

theorem all_rational_np_subset_bpp {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (hu : 0 ≤ u)
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3) :
    ∀ L, InNP L → Paper2.SelectedTape.InBPP L := by
  let g := sourceEstimatorGap u
  let G := GF (v27GapParameter g)
  have hhard : NPHard G.L := by rw [hL]; exact hard
  have hencoded := physical_source_encoded_polytime g G
  have hprint : BitMachine.Polytime (canonicalClassifierWord g G) :=
    canonicalClassifierWord_polytime_of_encoded g
      (by have := gap_ge_three u hu g (sourceEstimatorGap_bound u); omega)
      G hencoded
  have hmem : Paper2.SelectedTape.InBPP G.L :=
    ⟨E.sourceDecider g G hprint,
      E.sourceDecider_decides hu g (sourceEstimatorGap_bound u) G hprint⟩
  exact Paper2.SelectedTape.np_subset_inBPP hhard hmem

#print axioms all_rational_np_subset_bpp

theorem AllRationalEstimator.classifier_tape_zero {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (hz : E.estimator.cR = 0)
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

def AllRationalEstimator.sourceDecision {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) : Bool :=
  decide ((E.sourceDecider g G hprint).output input [] = [true])

theorem AllRationalEstimator.sourceDecider_output_singleton
    {μ : YaoMeasure} {u : ℝ} (E : AllRationalEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) :
    ∃ b, (E.sourceDecider g G hprint).output input [] = [b] := by
  rw [AllRationalEstimator.sourceDecider, Paper2.SelectedTape.pullback_output]
  unfold AllRationalEstimator.classifier Paper2.SelectedTape.Algorithm.ofPrefixMonomial
  unfold AllRationalEstimator.median medAlgJudge medOutputJudge
  exact ⟨_, rfl⟩

theorem AllRationalEstimator.sourceDecider_output_bit
    {μ : YaoMeasure} {u : ℝ} (E : AllRationalEstimator μ u) (g : ℕ)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hprint : BitMachine.Polytime (canonicalClassifierWord g G))
    (input : List Bool) :
    (E.sourceDecider g G hprint).output input [] =
      [E.sourceDecision g G hprint input] := by
  obtain ⟨b, hb⟩ := E.sourceDecider_output_singleton g G hprint input
  rw [hb]
  cases b <;> simp [AllRationalEstimator.sourceDecision, hb]

theorem AllRationalEstimator.sourceDecision_polytime
    {μ : YaoMeasure} {u : ℝ} (E : AllRationalEstimator μ u)
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
    simp [A, AllRationalEstimator.sourceDecider, Paper2.SelectedTape.pullback,
      Paper2.SelectedTape.Algorithm.tapeLength, hzClass]
  have hphysical := zeroTapeOutputPolytime A hzA
  have heq : (fun input => [E.sourceDecision g G hprint input]) =
      (fun input => A.output input []) := by
    funext input
    exact (E.sourceDecider_output_bit g G hprint input).symm
  rw [heq]
  exact hphysical

theorem AllRationalEstimator.sourceDecision_correct
    {μ : YaoMeasure} {u : ℝ} (E : AllRationalEstimator μ u)
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
    simp [A, AllRationalEstimator.sourceDecider, Paper2.SelectedTape.pullback,
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
      simpa [AllRationalEstimator.sourceDecision, A] using hn
    simp [hfalse] at hyes
    norm_num at hyes
  · intro hbit
    by_contra hn
    have hno := (hd input).2 hn
    have htrue : A.output input [] = [true] := by
      simpa [AllRationalEstimator.sourceDecision, A] using hbit
    rw [hp, if_pos htrue] at hno
    norm_num at hno

theorem all_rational_p_equals_np {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (hu : 0 ≤ u)
    (hz : E.estimator.cR = 0)
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3) : PEqualsNP := by
  let g := sourceEstimatorGap u
  let G := GF (v27GapParameter g)
  have hhard : NPHard G.L := by rw [hL]; exact hard
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
    (ComplexityReductionClosure.npHard_inP_implies_np_subset_p hhard hmem)

#print axioms all_rational_p_equals_np
#print axioms RationalComparator.judge_header
#print axioms medAlgJudge_polynomial
#print axioms AllRationalEstimator.classifier_law
#print axioms AllRationalEstimator.sourceDecision_polytime

end CurrentAdditive.ModelEndpointReview.RationalEndpoint
