import Paper2.MedRound

/-!
# WP-U18a (ii), machine half, part 4: the ONE fixed repeat-and-median machine `medMachine n E C`

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12, I:117-125, E:119-125.

`medMachine n E C` (`r = n + 1` repetitions) on input `pair w tape`:
1. moves `field w` to the work stack `fwr` (reversed), charged cell by cell;
2. moves the tape to `tr` (reversed) and, counting in finite control modulo `r`, pushes one mark
   per `r` cells onto `sc`, so `sc = 1^s` when `|tape| = r·s` (no length is supplied);
3. pushes `r` marks onto the loop counter `rc` (one transition);
4. runs `round E C` (MedRound) `r` times under the admitted counted loop: round `i` reads the
   disjoint segment `r-1-i` of the tape, runs `E` on `pair w segment`, runs the comparator `C` on
   `pair w out`, tallies `C`'s bit;
5. counts the tally and prints `[decide (r < 2·count)]` on its output stack.
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Paper2.MedianOwner.Med

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.MedianOwner.Phases Paper2.MedianOwner.Phases.Phase
open EthInapproximability.CurrentPaper.EncodedCommunication (field)
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)

/-- The tape word made of the first `m` segments, in order. -/
def pref (segs : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | m + 1 => pref segs m ++ segs m

/-- The tally after `i` rounds (round `i` reads segment `n - i`). -/
def acc (n : ℕ) (cmp : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (if cmp (n - i) then 1 else 0) + acc n cmp i

theorem acc_le (n : ℕ) (cmp : ℕ → Bool) : ∀ i, acc n cmp i ≤ i
  | 0 => le_rfl
  | i + 1 => by
    have := acc_le n cmp i
    simp only [acc]
    split <;> omega

theorem pref_length (segs : ℕ → List Bool) (s : ℕ) :
    ∀ m, (∀ i < m, (segs i).length = s) → (pref segs m).length = m * s
  | 0, _ => by simp [pref]
  | m + 1, h => by
    simp only [pref, List.length_append]
    rw [pref_length segs s m (fun i hi => h i (by omega)), h m (by omega)]
    ring

variable (n : ℕ) (E C : Machine)

def q1 : Phase (K E C) := ofProg (fieldScan (ax E C .inp) (ax E C .fwr)) () none
def q2 : Phase (K E C) := ofProg (countMove n (ax E C .inp) (ax E C .tr) (ax E C .sc)) ()
  ((none : Option Bool), (0 : Fin (n + 1)))
def q3 : Phase (K E C) := ofProg (pushN (ax E C .rc) (n + 1)) () none
def fin : Phase (K E C) := ofProg (final n (ax E C .cnt) (ax E C .outp)) ()
  ((none : Option Bool), (0 : Fin (n + 2)))

/-- The whole program: preparation, `n+1` rounds, final majority. -/
def top : Phase (K E C) :=
  seq (seq (q1 E C) (seq (q2 n E C) (q3 n E C))) (seq (loop (round E C) (ax E C .rc)) (fin n E C))

/-- **The fixed repeat-and-median machine** for estimator machine `E`, comparator machine `C`,
`n + 1` repetitions. -/
noncomputable def medMachine : Machine := by
  haveI := (top n E C).fL
  haveI := (top n E C).fV
  exact ofFinite (ax E C .inp) (ax E C .outp) (top n E C).l0 (top n E C).v0 (top n E C).P

/-- Bound on the length of `E`'s output on `pair w g`, `|g| = s` (production `output_length_bound`). -/
def outBound (E : Machine) (wl s TE : ℕ) : ℕ := 2 * wl + 1 + s + TE * E.pushBound

/-- Per-round clock. -/
def bodyClock (wl s TE TC : ℕ) : ℕ :=
  roundClock s wl (outBound E wl s TE)
    (BitMachineIteration.roundBound E (2 * wl + 1 + s) TE)
    (BitMachineIteration.roundBound C (2 * wl + 1 + outBound E wl s TE) TC)

/-- The clock of `medMachine`: `(n+1)` rounds of `bodyClock` plus a linear preparation. -/
def medClock (wl s TE TC : ℕ) : ℕ :=
  (wl + 1) + ((n + 1) * s + 1) + 1 + 2 + ((n + 1) * (bodyClock E C wl s TE TC + 2) + 1) +
    (n + 2) + 2

theorem init_bank (input : List Bool) :
    (fun k : K E C => if k = ax E C .inp then input else []) =
      G E C (eb E [] []) (eb C [] []) (A10 input [] [] [] [] [] [] [] [] []) := by
  funext k
  rcases k with (k | k) | ((k | k) | k)
  · simp [ax, G, eb, Machine.init]
  · fin_cases k <;> simp [ax, G, eb, BitMachineIteration.foreign]
  · simp [ax, G, eb, Machine.init]
  · fin_cases k <;> simp [ax, G, eb, BitMachineIteration.foreign]
  · cases k <;> simp [ax, G, A10]

/-- **Exact output and clock of the repeat-and-median machine.** For every word `w`, segment
length `s` and segments `segs 0, …, segs n` of length `s`: if `E` outputs `out i` on
`pair w (segs i)` within `TE` and `C` outputs the single bit `[cmp i]` on `pair w (out i)` within
`TC`, then `medMachine n E C` on `pair w (segs 0 ++ … ++ segs n)` outputs exactly
`[decide (n + 1 < 2 * acc n cmp (n + 1))]` within `medClock n E C |w| s TE TC` steps. -/
theorem med_outputs (w : List Bool) (s TE TC : ℕ) (segs out : ℕ → List Bool) (cmp : ℕ → Bool)
    (hs : ∀ i ≤ n, (segs i).length = s)
    (hE : ∀ i ≤ n, E.OutputsWithin (pair w (segs i)) (out i) TE)
    (hC : ∀ i ≤ n, C.OutputsWithin (pair w (out i)) [cmp i] TC) :
    (medMachine n E C).OutputsWithin (pair w (pref segs (n + 1)))
      [decide (n + 1 < 2 * acc n cmp (n + 1))] (medClock n E C w.length s TE TC) := by
  set tape := pref segs (n + 1) with htape
  have htl : tape.length = (n + 1) * s :=
    pref_length segs s (n + 1) (fun i hi => hs i (by omega))
  -- preparation
  have hq1 : (q1 E C).Runs
      (G E C (eb E [] []) (eb C [] []) (A10 (pair w tape) [] [] [] [] [] [] [] [] []))
      (G E C (eb E [] []) (eb C [] []) (A10 tape (field w).reverse [] [] [] [] [] [] [] []))
      (w.length + 1) := by
    have h := fieldScan_run (ax E C .inp) (ax E C .fwr) (by simp [ax]) tape w
      (G E C (eb E [] []) (eb C [] []) (A10 (pair w tape) [] [] [] [] [] [] [] [] []))
      none (by simp [ax, A10, pair])
    refine ofProg_runs _ _ _ _ (some false) (h.trans ?_)
    simp only [ax, G_upd_ax, G_ax, A10_upd, A10, List.append_nil]
  have hq2 : (q2 n E C).Runs
      (G E C (eb E [] []) (eb C [] []) (A10 tape (field w).reverse [] [] [] [] [] [] [] []))
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse tape.reverse (List.replicate s true) [] [] [] [] [] []))
      ((n + 1) * s + 1) := by
    obtain ⟨c, h⟩ := countMove_run n (ax E C .inp) (ax E C .tr) (ax E C .sc) (by simp [ax])
      (by simp [ax]) (by simp [ax]) tape
      (G E C (eb E [] []) (eb C [] []) (A10 tape (field w).reverse [] [] [] [] [] [] [] []))
      none 0 (by simp [ax, A10])
    have hdiv : ((0 : Fin (n + 1)).val + tape.length) / (n + 1) = s := by
      rw [htl, Fin.val_zero, zero_add, Nat.mul_div_cancel_left _ (by omega)]
    rw [hdiv, htl] at h
    refine ⟨(n + 1) * s + 1, le_rfl, c, h.trans ?_⟩
    simp only [ax, G_upd_ax, G_ax, A10_upd, A10, List.append_nil]
    try rfl
  have hq3 : (q3 n E C).Runs
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse tape.reverse (List.replicate s true) [] [] [] [] [] []))
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse tape.reverse (List.replicate s true) [] [] [] []
          (List.replicate (n + 1) true) [])) 1 := by
    refine ofProg_runs _ _ _ _ none ((pushN_run _ (n + 1) _ none).trans ?_)
    simp only [ax, G_upd_ax, G_ax, A10_upd, A10, List.append_nil]
  -- the rounds
  let S : ℕ → K E C → List Bool := fun i =>
    G E C (eb E [] []) (eb C [] [])
      (A10 [] (field w).reverse (pref segs (n + 1 - i)).reverse (List.replicate s true) [] [] []
        (List.replicate (acc n cmp i) true) (List.replicate (n + 1 - i) true) [])
  have hloop : (loop (round E C) (ax E C .rc)).Runs (S 0) (S (n + 1))
      ((n + 1) * (bodyClock E C w.length s TE TC + 2) + 1) := by
    refine loop_runs (round E C) (ax E C .rc) (n + 1) _ S ?_ ?_
    · intro i _
      simp [S, ax, A10]
    · intro i hi
      have hni : n + 1 - i = (n - i) + 1 := by omega
      have hstart : Function.update (S i) (ax E C .rc) (List.replicate (n + 1 - i - 1) true) =
          G E C (eb E [] []) (eb C [] [])
            (A10 [] (field w).reverse ((segs (n - i)).reverse ++ (pref segs (n - i)).reverse)
              (List.replicate s true) [] [] [] (List.replicate (acc n cmp i) true)
              (List.replicate (n - i) true) []) := by
        simp only [S, ax, G_upd_ax, A10_upd]
        rw [hni, pref, List.reverse_append, Nat.add_sub_cancel]
      have hend : S (i + 1) =
          G E C (eb E [] []) (eb C [] [])
            (A10 [] (field w).reverse (pref segs (n - i)).reverse (List.replicate s true) [] [] []
              (List.replicate (if cmp (n - i) then 1 else 0) true ++
                List.replicate (acc n cmp i) true) (List.replicate (n - i) true) []) := by
        simp only [S, acc, List.replicate_append_replicate]
        rw [show n + 1 - (i + 1) = n - i by omega]
      rw [hstart, hend]
      have hlo : (out (n - i)).length ≤ outBound E w.length s TE := by
        have := output_length_bound E (hE (n - i) (by omega))
        rw [EncodedComplexity.pair_length, hs (n - i) (by omega)] at this
        unfold outBound
        omega
      exact round_runs E C w (segs (n - i)) (out (n - i)) (cmp (n - i)) s TE TC
        (outBound E w.length s TE) _ _ _ (hs (n - i) (by omega)) (hE (n - i) (by omega))
        (hC (n - i) (by omega)) hlo
  -- the final majority
  have hfin : (fin n E C).Runs (S (n + 1))
      (G E C (eb E [] []) (eb C [] [])
        (A10 [] (field w).reverse [] (List.replicate s true) [] [] [] [] []
          [decide (n + 1 < 2 * acc n cmp (n + 1))])) (n + 2) := by
    obtain ⟨v, h⟩ := final_run n (ax E C .cnt) (ax E C .outp) (by simp [ax]) (acc n cmp (n + 1))
      (S (n + 1)) none 0 (by simp [S, ax, A10]) (by simp [acc_le])
    refine ⟨acc n cmp (n + 1) + 1, by have := acc_le n cmp (n + 1); omega, v, h.trans ?_⟩
    simp only [S, ax, G_upd_ax, G_ax, A10_upd, A10, Nat.sub_self, pref, List.reverse_nil,
      List.replicate_zero, Fin.val_zero, zero_add, List.append_nil]
    try rfl
  have hS0 : S 0 = G E C (eb E [] []) (eb C [] [])
      (A10 [] (field w).reverse tape.reverse (List.replicate s true) [] [] [] []
        (List.replicate (n + 1) true) []) := by
    simp only [S, acc, List.replicate_zero, Nat.sub_zero, htape]
  rw [← hS0] at hq3
  have hall := seq_runs (seq_runs hq1 (seq_runs hq2 hq3)) (seq_runs hloop hfin)
  obtain ⟨t, ht, v, hrun⟩ := hall
  letI := (top n E C).fL
  letI := (top n E C).fV
  unfold medMachine
  refine outputsWithin_of_raw_run (ax E C .inp) (ax E C .outp) (top n E C).l0 (top n E C).v0
    (top n E C).P (pair w tape) [decide (n + 1 < 2 * acc n cmp (n + 1))] t
    (medClock n E C w.length s TE TC) ?_ ?_ ?_
  · unfold medClock; omega
  · unfold rawInit
    rw [init_bank]
    exact congrArg (fun c => c.l) hrun
  · unfold rawInit
    rw [init_bank]
    rw [show ((advance (top n E C).P)^[t])
        (⟨some (top n E C).l0, (top n E C).v0,
          G E C (eb E [] []) (eb C [] []) (A10 (pair w tape) [] [] [] [] [] [] [] [] [])⟩ :
          Cfg (K E C) (top n E C).L (top n E C).V) = _ from hrun]
    simp [ax, G, A10]

end Paper2.MedianOwner.Med
