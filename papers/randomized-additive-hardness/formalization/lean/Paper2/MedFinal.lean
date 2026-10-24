import Paper2.MedMachine
import Paper2.MedianProbR
import Paper2.AModelEstimator

/-!
# WP-U18a (ii): the repeat-and-median machine as a D-A1 prefix-model algorithm, and its error

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12.

Source (lock v12 `sections/01-introduction.tex`, I:117-125): "Choose a fixed integer k>2a. Amplify
the estimator's success probability to 99/100 by a constant number of independent calls and a
median. Accept the source exactly when its estimate is below B+k/2."

Decisions implemented: D-A1 (the frozen predecessor `Paper2.AModel.PrefixAlgorithm` of lane
`a-model-owner-1`, hash-verified against its RECEIPT), D-A3 (ii) (its dyadic codec
`Paper2.AModel.decodeDyadic`, value `z / 2^j`, reused by exact name).

`medAlg A C thr TC hC` is ONE fixed machine `medMachine 146 A.machine C` (147 = `reps` runs) packaged
as a prefix-model algorithm with tape length `reps * R(|w|)`: its printed word on every tape is
`[decide (a strict majority of the 147 decoded outputs is below thr w)]`, equivalently (by
`majBelow_iff`) `[decide (lower median < thr w)]`. The comparator `C` is a HYPOTHESIS here
(`CmpSpec`: one machine printing the single bit `decide (Paper2.AModel.decodeDyadic out < thr w)` on
`pair w out`); a physical comparator for the codec is not built in this file.
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Paper2.MedianOwner.Final

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification (reps)
open Paper2.MedianOwner Paper2.MedianOwner.Med
open Paper2.AModel (PrefixAlgorithm)

/-- Segment `i` (length `s`) of a tape word. -/
def chunk (s i : ℕ) (tape : List Bool) : List Bool := (tape.drop (s * i)).take s

theorem pref_chunks_take (s : ℕ) (L : List Bool) :
    ∀ m, pref (fun i => chunk s i L) m = L.take (s * m)
  | 0 => by simp [pref]
  | m + 1 => by
    rw [pref, pref_chunks_take s L m, chunk, Nat.mul_succ, List.take_add]

theorem pref_chunks (s n : ℕ) (L : List Bool) (hL : L.length = (n + 1) * s) :
    pref (fun i => chunk s i L) (n + 1) = L := by
  rw [pref_chunks_take, List.take_of_length_le]
  rw [hL, Nat.mul_comm]

theorem chunk_length (s n i : ℕ) (L : List Bool) (hL : L.length = (n + 1) * s) (hi : i ≤ n) :
    (chunk s i L).length = s := by
  simp only [chunk, List.length_take, List.length_drop, hL]
  have : s * (i + 1) ≤ s * (n + 1) := Nat.mul_le_mul_left s (by omega)
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm (n + 1) s]
  omega

theorem acc_eq_sum (n : ℕ) (cmp : ℕ → Bool) :
    ∀ m, acc n cmp m = ∑ j ∈ Finset.range m, (if cmp (n - j) then 1 else 0)
  | 0 => by simp [acc]
  | m + 1 => by
    rw [acc, acc_eq_sum n cmp m, Finset.sum_range_succ, Nat.add_comm]

/-- The unary tally of the machine is the number of accepting runs. -/
theorem acc_eq_card (n : ℕ) (cmp : ℕ → Bool) :
    acc n cmp (n + 1) = Fintype.card {i : Fin (n + 1) // cmp i = true} := by
  rw [acc_eq_sum]
  have h := Finset.sum_range_reflect (fun j => if cmp j then 1 else 0) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, Fintype.card_subtype, Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range (fun j => if cmp j = true then 1 else 0) (n + 1)).symm

variable (A : PrefixAlgorithm) (C : Machine) (thr : List Bool → ℝ) (TC : List Bool → ℕ)

open Classical in
/-- The comparator hypothesis: `C` prints the one bit `decide (Paper2.AModel.decodeDyadic out < thr w)` on
`pair w out` within `TC w`, for every word `out` of length at most the output bound of `A`. -/
def CmpSpec : Prop :=
  ∀ w out, out.length ≤ outBound A.machine w.length (A.tapeLength w.length) (A.time w) →
    C.OutputsWithin (pair w out) [decide (Below Paper2.AModel.decodeDyadic (thr w) out)] (TC w)

open Classical in
/-- The printed word of the median machine on `pair w tape`. -/
noncomputable def medOutput (w tape : List Bool) : List Bool :=
  [decide (MajBelow Paper2.AModel.decodeDyadic
    (fun i : Fin reps => A.output w (chunk (A.tapeLength w.length) i tape)) (thr w))]

theorem ofFn_chunk (s : ℕ) (t : Fin (reps * s) → Bool) (i : Fin reps) :
    chunk s i (List.ofFn t) = List.ofFn (seg reps s t i) := by
  rw [ofFn_seg]; rfl

open Classical in
/-- **The repeat-and-median machine as a D-A1 prefix-model algorithm.** One fixed machine
`medMachine 146 A.machine C`; tape length `reps · R(|w|)`; clock
`medClock 146 A.machine C |w| R(|w|) (A.time w) (TC w)`; printed word `medOutput`. -/
noncomputable def medAlg (hC : CmpSpec A C thr TC) : PrefixAlgorithm where
  machine := medMachine 146 A.machine C
  tapeLength := fun m => reps * A.tapeLength m
  time := fun w => medClock 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w)
  output := medOutput A thr
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
        [decide (Below Paper2.AModel.decodeDyadic (thr w) (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape))))] (TC w) := by
      intro i hi
      apply hC
      have hb := output_length_bound A.machine (hE i hi)
      rw [EncodedComplexity.pair_length, chunk_length (A.tapeLength w.length) 146 i _ hL hi] at hb
      unfold outBound
      omega
    have hmain := med_outputs 146 A.machine C w (A.tapeLength w.length) (A.time w) (TC w)
      (fun i => chunk (A.tapeLength w.length) i (List.ofFn tape)) (fun i => A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))
      (fun i => decide (Below Paper2.AModel.decodeDyadic (thr w) (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))))
      (fun i hi => chunk_length (A.tapeLength w.length) 146 i _ hL hi) hE hC'
    rw [pref_chunks (A.tapeLength w.length) 146 _ hL, acc_eq_card] at hmain
    have hout : medOutput A thr w (List.ofFn tape) = [decide (146 + 1 < 2 * Fintype.card
        {i : Fin (146 + 1) // decide (Below Paper2.AModel.decodeDyadic (thr w)
          (A.output w (chunk (A.tapeLength w.length) i (List.ofFn tape)))) = true})] := by
      unfold medOutput
      simp only [List.cons.injEq, and_true]
      apply decide_eq_decide.mpr
      simp only [decide_eq_true_eq]
      exact Iff.rfl
    change (medMachine 146 A.machine C).OutputsWithin _ (medOutput A thr w (List.ofFn tape)) _
    rw [hout]
    exact hmain

/-- The acceptance probability of `medAlg` is the probability of the majority event over the
uniform tape of length `reps · R(|w|)`, run `i` reading segment `i`. -/
theorem medAlg_prob (hC : CmpSpec A C thr TC) (w : List Bool) :
    (medAlg A C thr TC hC).prob w (· = [true]) =
      (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
        MajBelow Paper2.AModel.decodeDyadic
          (fun i => A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))) (thr w)) := by
  classical
  unfold PrefixAlgorithm.prob
  congr 1
  funext t
  simp only [medAlg, medOutput, List.cons.injEq, and_true, decide_eq_true_eq]
  simp only [ofFn_chunk]

/-- **YES side** (I:120-122): if one run of the estimator is within `a` of `c ≤ B` with probability
`≥ 2/3` and the threshold is `B + k/2` with `2a < k`, the median machine accepts with probability
`≥ 99/100`. -/
theorem medAlg_yes (hC : CmpSpec A C thr TC) (w : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k) (hthr : thr w = (B : ℝ) + (k : ℝ) / 2)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hcB : c ≤ B) : 99 / 100 ≤ (medAlg A C thr TC hC).prob w (· = [true]) := by
  rw [medAlg_prob, hthr]
  exact (median_midpoint_testR Paper2.AModel.decodeDyadic (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a B k hk hE).2.1 hcB

/-- **NO side** (I:120-122): with `B + k ≤ c`, the median machine accepts with probability
`≤ 1/100`. -/
theorem medAlg_no (hC : CmpSpec A C thr TC) (w : List Bool) (c : ℕ) (a : ℝ) (B k : ℕ)
    (hk : 2 * a < k) (hthr : thr w = (B : ℝ) + (k : ℝ) / 2)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hBc : B + k ≤ c) : (medAlg A C thr TC hC).prob w (· = [true]) ≤ 1 / 100 := by
  rw [medAlg_prob, hthr]
  have h := (median_midpoint_testR Paper2.AModel.decodeDyadic (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a B k hk hE).2.2 hBc
  rw [Paper2.Unit4Shell.Amplification.prob_not] at h
  linarith

/-- **Median window** (I:118-119, "amplify ... to 99/100"): the lower median of the 147 decoded
outputs is within `a` of `c` with probability `≥ 99/100`. -/
theorem medAlg_median_window (w : List Bool) (c : ℕ) (a : ℝ)
    (hE : 2 / 3 ≤ A.prob w (fun out => ∃ v, Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a)) :
    99 / 100 ≤ (uniformTape (reps * A.tapeLength w.length)).prob (fun t =>
      WindowR c a (Paper2.Unit4Shell.Amplification.lowerMedian (by decide : 0 < reps)
        (fun i => topValR (Paper2.AModel.decodeDyadic
          (A.output w (List.ofFn (seg reps (A.tapeLength w.length) t i))))))) :=
  (median_midpoint_testR Paper2.AModel.decodeDyadic (A.tapeLength w.length)
    (fun g => A.output w (List.ofFn g)) c a 0 (⌈2 * a⌉₊ + 1) (by
      have := Nat.le_ceil (2 * a)
      push_cast
      linarith) hE).1

end Paper2.MedianOwner.Final
