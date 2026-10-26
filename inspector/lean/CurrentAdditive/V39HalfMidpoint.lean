import CurrentAdditive.V39RationalMidpoint

/-!
The permitted estimator representation need only compare its numerical
outputs with ordinary polynomial-length binary rationals. Only m/2 is
used. Unlike the preserved all-dyadic interface, no binary encoding of an
arbitrarily large denominator exponent is required here. The output values
are arbitrary reals assigned to words, not dyadic estimator values.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39HalfMidpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.ModelEndpointReview
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open CurrentAdditive.ModelEndpointReview.RationalCodeAdapter
open Paper2 Paper2.Yao Paper2.YaoBppDraft
open Paper2.AModel (PrefixAlgorithm)
open Paper2.Unit4Shell.Amplification (reps)

/-- A supplied polynomial comparator from the permitted estimator model.
The canonical threshold code is false :: natField m and denotes m/2.
The physical machine is total on every word; correctness covers all
estimator output words, including inaccurate ones. This is not a universal
implementation for arbitrary numeric representations. -/
structure HalfComparator (value : List Bool → ℝ) where
  output : List Bool → Bool
  physical : BitMachine.Polytime (fun w => [output w])
  correct : ∀ (m : ℕ) (out : List Bool),
    output (pair (false :: natField m) out) = decide (value out < (m : ℝ) / 2)

def HalfComparator.judge {value : List Bool → ℝ}
    (R : HalfComparator value) (w out : List Bool) : Bool :=
  R.output (adapt (pair w out))

theorem HalfComparator.judge_header {value : List Bool → ℝ}
    (R : HalfComparator value) (m : ℕ) (rest out : List Bool) :
    R.judge (natField m ++ rest) out = decide (value out < (m : ℝ) / 2) := by
  unfold HalfComparator.judge
  rw [adapt_header, R.correct]

/-- The threshold numerator has ordinary binary length; the denominator
is the fixed constant 2. -/
theorem halfCode_length (m : ℕ) :
    (false :: natField m).length = 2 * m.bits.length + 2 := by
  simp [natField, field_length]

private theorem composedPoly {value : List Bool → ℝ} (R : HalfComparator value) :
    BitMachine.Polytime (fun input => [R.output (adapt input)]) :=
  BitMachineComposition.polytime_comp polytime R.physical

private def cmpMachine {value : List Bool → ℝ} (R : HalfComparator value) : Machine :=
  Classical.choose (composedPoly R)

private def cmpC {value : List Bool → ℝ} (R : HalfComparator value) : ℕ :=
  Classical.choose (Classical.choose_spec (composedPoly R))

private def cmpD {value : List Bool → ℝ} (R : HalfComparator value) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (composedPoly R)))

private theorem cmpRun {value : List Bool → ℝ} (R : HalfComparator value)
    (input : List Bool) :
    (cmpMachine R).OutputsWithin input [R.output (adapt input)]
      (cmpC R * (input.length + 1) ^ cmpD R) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (composedPoly R))) input

private def estC (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ := Classical.choose hA
private def estD (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ :=
  Classical.choose (Classical.choose_spec hA)
private theorem estBounds (A : PrefixAlgorithm) (hA : A.Polynomial) (w : List Bool) :
    A.tapeLength w.length ≤ estC A hA * (w.length + 1) ^ estD A hA ∧
      A.time w ≤ estC A hA * (w.length + 1) ^ estD A hA :=
  Classical.choose_spec (Classical.choose_spec hA) w

private def clockK (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ :=
  5 + estC A hA + estC A hA * A.machine.pushBound

def compareClock {value : List Bool → ℝ} (A : PrefixAlgorithm)
    (hA : A.Polynomial) (R : HalfComparator value) (w : List Bool) : ℕ :=
  cmpC R * (clockK A hA * (w.length + 1) ^ (estD A hA + 1)) ^ cmpD R

theorem compareClock_poly {value : List Bool → ℝ} (A : PrefixAlgorithm)
    (hA : A.Polynomial) (R : HalfComparator value) :
    ∃ c d : ℕ, ∀ w : List Bool,
      compareClock A hA R w ≤ c * (w.length + 1) ^ d := by
  refine ⟨cmpC R * (clockK A hA) ^ cmpD R, (estD A hA + 1) * cmpD R, ?_⟩
  intro w
  simp only [compareClock]
  rw [mul_pow]
  simp only [← pow_mul, Nat.mul_assoc]
  exact le_rfl

private theorem compareClock_covers {value : List Bool → ℝ}
    (A : PrefixAlgorithm) (hA : A.Polynomial) (R : HalfComparator value)
    (w out : List Bool)
    (hout : out.length ≤ MedianOwner.Med.outBound A.machine w.length
      (A.tapeLength w.length) (A.time w)) :
    cmpC R * ((pair w out).length + 1) ^ cmpD R ≤ compareClock A hA R w := by
  let N := w.length + 1
  let X := N ^ (estD A hA + 1)
  have hN : 1 ≤ N := by omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hN
  have hpow : N ^ estD A hA ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hwplus : w.length + 1 ≤ X := by
    calc w.length + 1 = N := rfl
      _ = N ^ 1 := (pow_one N).symm
      _ ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hs := (estBounds A hA w).1
  have ht := (estBounds A hA w).2
  have hsX : A.tapeLength w.length ≤ estC A hA * X :=
    hs.trans (Nat.mul_le_mul_left _ hpow)
  have htX : A.time w ≤ estC A hA * X :=
    ht.trans (Nat.mul_le_mul_left _ hpow)
  have hpush := Nat.mul_le_mul_right A.machine.pushBound htX
  have hlength : (pair w out).length + 1 ≤ clockK A hA * X := by
    rw [pair_length]
    unfold MedianOwner.Med.outBound at hout
    have he : clockK A hA * X =
        5 * X + estC A hA * X + estC A hA * X * A.machine.pushBound := by
      unfold clockK
      ring
    rw [he]
    omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlength (cmpD R))

/-- Concrete header projection followed by the supplied fixed comparator.
One fixed machine works on all words and on every possible estimator
output below the physical output-length bound. -/
theorem comparisonSpec {value : List Bool → ℝ} (A : PrefixAlgorithm)
    (hA : A.Polynomial) (R : HalfComparator value) :
    CmpSpecJudge A (cmpMachine R) R.judge (compareClock A hA R) := by
  intro w out hout
  exact outputsWithin_mono _ (cmpRun R (pair w out))
    (compareClock_covers A hA R w out hout)

structure HalfEstimator (μ : YaoMeasure) (u : ℝ) where
  estimator : SelectedTape.Algorithm
  value : List Bool → ℝ
  comparator : HalfComparator value
  accurate : ∀ w c, AModel.targetYao μ w = some c →
    2 / 3 ≤ estimator.prob w (fun out => |value out - (c : ℝ)| ≤ u)

private def HalfEstimator.header {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) : PrefixAlgorithm :=
  (HeaderStrip.selectedEstimator E.estimator).toPrefix
private theorem HalfEstimator.headerPoly {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) : E.header.Polynomial :=
  HeaderStrip.selectedEstimator_toPrefix_polynomial E.estimator

def HalfEstimator.majority {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) : PrefixAlgorithm :=
  medAlgJudge E.header (cmpMachine E.comparator) E.comparator.judge
    (compareClock E.header E.headerPoly E.comparator)
    (comparisonSpec E.header E.headerPoly E.comparator)

theorem HalfEstimator.majority_poly {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) : E.majority.Polynomial :=
  medAlgJudge_polynomial _ _ _ _
    (comparisonSpec E.header E.headerPoly E.comparator) E.headerPoly
    (compareClock_poly E.header E.headerPoly E.comparator)

theorem HalfEstimator.majority_tape {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (n : ℕ) :
    E.majority.tapeLength n =
      (147 * (HeaderStrip.selectedEstimator E.estimator).cR) *
        (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR := by
  change 147 * ((HeaderStrip.selectedEstimator E.estimator).cR *
    (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR) = _
  ring

private theorem HalfEstimator.shape {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) : ∃ c d : ℕ, ∀ n, E.majority.tapeLength n = c * (n + 1) ^ d :=
  ⟨147 * (HeaderStrip.selectedEstimator E.estimator).cR,
    (HeaderStrip.selectedEstimator E.estimator).dR, E.majority_tape⟩

def HalfEstimator.classifier {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) : SelectedTape.Algorithm :=
  SelectedTape.Algorithm.ofPrefixMonomial E.majority E.majority_poly E.shape

theorem HalfEstimator.classifier_prob {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (w : List Bool) (P : List Bool → Prop) :
    E.classifier.prob w P = E.majority.prob w P :=
  SelectedTape.Algorithm.ofPrefixMonomial_prob E.majority E.majority_poly E.shape w P

theorem fixed_midpoint_law {μ : YaoMeasure} {u : ℝ}
    (E : HalfEstimator μ u) (hu : 0 ≤ u) (i : Instance) (hi : i.Valid) (B k : ℕ)
    (hgap : 2 * (u + 2) < (k : ℝ)) :
    (Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ B →
      99 / 100 ≤ E.classifier.prob
        (natField (2 * B + k) ++ AModel.matrixWord i.rows i.cols i.table) (· = [true])) ∧
    (B + k ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) →
      E.classifier.prob
        (natField (2 * B + k) ++ AModel.matrixWord i.rows i.cols i.table) (· = [true]) ≤ 1 / 100) := by
  let rest := AModel.matrixWord i.rows i.cols i.table
  let w := natField (2 * B + k) ++ rest
  let c := μ.eval i
  have hk : 4 ≤ k := by
    have h : (4 : ℝ) ≤ k := by linarith
    exact_mod_cast h
  have hg : 2 * u < ((k - 4 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith
  have hm : ((2 * B + k : ℕ) : ℝ) / 2 =
      ((B + 2 : ℕ) : ℝ) + ((k - 4 : ℕ) : ℝ) / 2 := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have hj : ∀ out, E.comparator.judge w out =
      decide (MedianOwner.Below (fun out => some (E.value out))
        (((B + 2 : ℕ) : ℝ) + ((k - 4 : ℕ) : ℝ) / 2) out) := by
    intro out
    have h := E.comparator.judge_header (2 * B + k) rest out
    rw [hm] at h
    simpa [w, MedianOwner.Below] using h
  have ha : 2 / 3 ≤ E.header.prob w
      (fun out => ∃ v, some (E.value out) = some v ∧ |v - (c : ℝ)| ≤ u) := by
    change 2 / 3 ≤ (HeaderStrip.selectedEstimator E.estimator).toPrefix.prob
      (natField (2 * B + k) ++ rest) _
    rw [HeaderStrip.selectedEstimator_toPrefix_prob]
    simpa using E.accurate rest c (YaoSelected.target_matrix μ i hi)
  obtain ⟨hl, hr⟩ := measure_window μ i
  constructor
  · intro hD
    have hc : c ≤ B + 2 := by dsimp [c]; omega
    rw [E.classifier_prob]
    exact medAlgJudge_yes _ _ _ _ _ (fun out => some (E.value out))
      w c u (B + 2) (k - 4) hg hj ha hc
  · intro hD
    have hc : B + 2 + (k - 4) ≤ c := by dsimp [c]; omega
    rw [E.classifier_prob]
    exact medAlgJudge_no _ _ _ _ _ (fun out => some (E.value out))
      w c u (B + 2) (k - 4) hg hj ha hc

#print axioms comparisonSpec
#print axioms compareClock_poly
#print axioms HalfEstimator.majority_poly
#print axioms HalfEstimator.majority_tape
#print axioms fixed_midpoint_law

end CurrentAdditive.V39HalfMidpoint
