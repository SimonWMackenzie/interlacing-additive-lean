import Mathlib

/-!
# Current paper: the executable bounded prefix clock

Source: v8 `sections/05-iteration.tex`, `eq:paper-slow-clock` and
`lem:paper-slow-diagonal`. This is the actual forward scan of cutoff runs
`1,...,n`, with fuel `n` per run and immediate stop at the first failure.
It is not the older route's noncomputable threshold maximum.

The machine interface exposes its transition, initialization and output
functions. All definitions below are executable relative to these fields.
The transition-count bound is proved for the instrumented simulator, not
mistaken for a bit-time bound for arbitrary transition oracles. Instantiating
the paper's cutoff algorithm and charging a concrete encoded simulation are
separate obligations. In particular this file does not assume those parts
of the paper have been formalized.
-/

namespace EthInapproximability.CurrentPaper.SlowClock

/-- A deterministic cutoff machine, with absorbing halting configurations. -/
structure Machine (State : Type*) where
  initial : ℕ → State
  step : State → State
  output : State → Option ℕ
  halted : ∀ s u, output s = some u → step s = s

variable {State : Type*}

/-- Exactly `fuel` transitions, with the original input fixed throughout. -/
def run (M : Machine State) (fuel input : ℕ) : State :=
  (M.step^[fuel]) (M.initial input)

/-- The same simulation with its actual transition calls counted. -/
def simulate (M : Machine State) (input : ℕ) : ℕ → State × ℕ
  | 0 => (M.initial input, 0)
  | fuel + 1 =>
    let previous := simulate M input fuel
    (M.step previous.1, previous.2 + 1)

theorem simulate_state (M : Machine State) (input fuel : ℕ) :
    (simulate M input fuel).1 = run M fuel input := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [simulate, run, Function.iterate_succ_apply', ih]

theorem simulate_steps (M : Machine State) (input fuel : ℕ) :
    (simulate M input fuel).2 = fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [simulate, ih]

theorem run_persistent (M : Machine State) {input fuel later u : ℕ}
    (h : M.output (run M fuel input) = some u) (hle : fuel ≤ later) :
    run M later input = run M fuel input := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [run, Nat.add_comm fuel extra, Function.iterate_add_apply]
  exact Function.iterate_fixed (M.halted _ u h) extra

/-- Success means a halted output at most the numerical source budget. -/
def succeeds (M : Machine State) (budget input : ℕ) : Bool :=
  match M.output (run M budget input) with
  | none => false
  | some cutoff => decide (cutoff ≤ budget)

theorem succeeds_iff (M : Machine State) (budget input : ℕ) :
    succeeds M budget input = true ↔
      ∃ cutoff, M.output (run M budget input) = some cutoff ∧ cutoff ≤ budget := by
  unfold succeeds
  cases h : M.output (run M budget input) with
  | none => simp
  | some cutoff => simp

theorem succeeds_mono (M : Machine State) {small large input : ℕ}
    (hle : small ≤ large) (h : succeeds M small input = true) :
    succeeds M large input = true := by
  obtain ⟨u, hu, hub⟩ := (succeeds_iff M small input).1 h
  apply (succeeds_iff M large input).2
  exact ⟨u, by rw [run_persistent M hu hle]; exact hu, hub.trans hle⟩

/-- A literal left-to-right short-circuit scan. -/
def prefixCount (test : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, fuel + 1 =>
    if test start then 1 + prefixCount test (start + 1) fuel else 0

theorem prefixCount_le (test : ℕ → Bool) (start fuel : ℕ) :
    prefixCount test start fuel ≤ fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    simp only [prefixCount]
    split
    · have := ih (start + 1); omega
    · omega

theorem prefixCount_success (test : ℕ → Bool) (start fuel : ℕ) :
    ∀ i < prefixCount test start fuel, test (start + i) = true := by
  induction fuel generalizing start with
  | zero => simp [prefixCount]
  | succ fuel ih =>
    intro i hi
    by_cases h : test start = true
    · simp only [prefixCount, h, ite_true] at hi
      cases i with
      | zero => simpa using h
      | succ i =>
        have hh := ih (start + 1) i (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · simp [prefixCount, h] at hi

theorem le_prefixCount (test : ℕ → Bool) (start fuel k : ℕ) (hk : k ≤ fuel)
    (h : ∀ i < k, test (start + i) = true) :
    k ≤ prefixCount test start fuel := by
  induction k generalizing start fuel with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hstart : test start = true := by simpa using h 0 (by omega)
      rw [prefixCount, if_pos hstart]
      have htail : k ≤ prefixCount test (start + 1) fuel := by
        apply ih (start + 1) fuel (by omega)
        intro i hi
        have hh := h (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      omega

theorem prefixCount_failure (test : ℕ → Bool) (start fuel : ℕ)
    (h : prefixCount test start fuel < fuel) :
    test (start + prefixCount test start fuel) = false := by
  induction fuel generalizing start with
  | zero => simp [prefixCount] at h
  | succ fuel ih =>
    by_cases hs : test start = true
    · simp only [prefixCount, hs, ite_true] at h ⊢
      have hh := ih (start + 1) (by omega)
      simpa [Nat.add_assoc] using hh
    · simp [prefixCount, hs]

theorem prefixCount_mono {smallTest largeTest : ℕ → Bool} {start small large : ℕ}
    (h : ∀ k, smallTest k = true → largeTest k = true) (hle : small ≤ large) :
    prefixCount smallTest start small ≤ prefixCount largeTest start large := by
  apply le_prefixCount
  · exact (prefixCount_le smallTest start small).trans hle
  · intro i hi
    exact h _ (prefixCount_success smallTest start small i hi)

/-- The exact repetition count of the paper's sequential clock. -/
def repetitions (M : Machine State) (n : ℕ) : ℕ :=
  prefixCount (succeeds M n) 1 n

theorem repetitions_le (M : Machine State) (n : ℕ) : repetitions M n ≤ n :=
  prefixCount_le _ _ _

theorem repetitions_mono (M : Machine State) : Monotone (repetitions M) := by
  intro n m hnm
  exact prefixCount_mono (fun k hk => succeeds_mono M hnm hk) hnm

/-- Every selected level, not merely the last, has a bounded completed run. -/
theorem selected_run (M : Machine State) (n k : ℕ)
    (hk0 : 1 ≤ k) (hk : k ≤ repetitions M n) :
    ∃ cutoff, M.output (run M n k) = some cutoff ∧ cutoff ≤ n := by
  have hs := prefixCount_success (succeeds M n) 1 n (k - 1) (by
    change k - 1 < repetitions M n
    omega)
  have heq : 1 + (k - 1) = k := by omega
  rw [heq] at hs
  exact (succeeds_iff M n k).1 hs

theorem next_run_failure (M : Machine State) (n : ℕ)
    (h : repetitions M n < n) :
    succeeds M n (repetitions M n + 1) = false := by
  have hh := prefixCount_failure (succeeds M n) 1 n h
  simpa [repetitions, Nat.add_comm] using hh

/-- Pointwise termination of the explicitly supplied cutoff machine. -/
def Terminates (M : Machine State) : Prop :=
  ∀ k, 1 ≤ k → ∃ fuel cutoff, M.output (run M fuel k) = some cutoff

theorem finite_prefix_eventually_successful (M : Machine State) (hterm : Terminates M)
    (K : ℕ) : ∃ N, K ≤ N ∧ ∀ k, 1 ≤ k → k ≤ K → succeeds M N k = true := by
  induction K with
  | zero => exact ⟨0, le_rfl, by intro k hk hk0; omega⟩
  | succ K ih =>
    obtain ⟨N, hKN, hN⟩ := ih
    obtain ⟨fuel, cutoff, hout⟩ := hterm (K + 1) (by omega)
    let N' := max N (max (K + 1) (max fuel cutoff))
    have hNN : N ≤ N' := le_max_left _ _
    have hK : K + 1 ≤ N' := (le_max_left _ _).trans (le_max_right _ _)
    have hf : fuel ≤ N' :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hc : cutoff ≤ N' :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    refine ⟨N', hK, ?_⟩
    intro k hk0 hk
    by_cases hkK : k ≤ K
    · exact succeeds_mono M hNN (hN k hk0 hkK)
    · have hkeq : k = K + 1 := by omega
      subst k
      apply (succeeds_iff M N' (K + 1)).2
      exact ⟨cutoff, by rw [run_persistent M hout hf]; exact hout, hc⟩

theorem repetitions_unbounded (M : Machine State) (hterm : Terminates M) (K : ℕ) :
    ∃ N, ∀ n, N ≤ n → K ≤ repetitions M n := by
  obtain ⟨N, hKN, hN⟩ := finite_prefix_eventually_successful M hterm K
  have hcount : K ≤ repetitions M N := by
    apply le_prefixCount _ 1 N K hKN
    intro i hi
    exact hN (1 + i) (by omega) (by omega)
  exact ⟨N, fun n hn => hcount.trans (repetitions_mono M hn)⟩

/-- The finite-prefix argument gives convergence of the actual executable
scan, without replacing it by a separately chosen increasing function. -/
theorem repetitions_tendsto_atTop (M : Machine State) (hterm : Terminates M) :
    Filter.Tendsto (repetitions M) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr (repetitions_unbounded M hterm)

/-- The numerical upper bound in `lem:paper-slow-diagonal` tends to zero.
Applying this to a matrix quantity still requires the paper's fixed-level
cutoff correctness and the corresponding inequality. -/
theorem reciprocal_repetitions_tendsto_zero (M : Machine State)
    (hterm : Terminates M) :
    Filter.Tendsto (fun n => 1 / (2 * (repetitions M n : ℝ)))
      Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n => (repetitions M n : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat.comp (repetitions_tendsto_atTop M hterm)
  simpa only [one_div, mul_inv_rev, zero_mul] using h.mul_const (2 : ℝ)⁻¹

/-- Number of runs actually inspected by the same short-circuit scan. -/
def inspected (test : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, fuel + 1 =>
    if test start then 1 + inspected test (start + 1) fuel else 1

theorem inspected_le (test : ℕ → Bool) (start fuel : ℕ) :
    inspected test start fuel ≤ fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    simp only [inspected]
    split
    · have := ih (start + 1); omega
    · omega

/-- The counted wrapper runs `simulate` once per inspected input, stopping
at exactly the same failure as `prefixCount`. Initialization/output tests and
loop arithmetic are not counted as machine transitions. -/
def countedScan (M : Machine State) (budget : ℕ) : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (0, 0)
  | start, fuel + 1 =>
    let current := simulate M start budget
    match M.output current.1 with
    | none => (0, current.2)
    | some cutoff =>
      if cutoff ≤ budget then
        let later := countedScan M budget (start + 1) fuel
        (1 + later.1, current.2 + later.2)
      else (0, current.2)

theorem countedScan_correct (M : Machine State) (budget start fuel : ℕ) :
    countedScan M budget start fuel =
      (prefixCount (succeeds M budget) start fuel,
        budget * inspected (succeeds M budget) start fuel) := by
  induction fuel generalizing start with
  | zero => simp [countedScan, prefixCount, inspected]
  | succ fuel ih =>
    simp only [countedScan, simulate_state, simulate_steps, ih]
    cases hout : M.output (run M budget start) with
    | none => simp [prefixCount, inspected, succeeds, hout]
    | some cutoff =>
      by_cases hc : cutoff ≤ budget
      · simp [prefixCount, inspected, succeeds, hout, hc, Nat.mul_add]
      · simp [prefixCount, inspected, succeeds, hout, hc]

/-- Literal bounded simulation: at most `n²` cutoff-machine transitions. -/
theorem clock_transition_bound (M : Machine State) (n : ℕ) :
    (countedScan M n 1 n).1 = repetitions M n ∧
    (countedScan M n 1 n).2 ≤ n ^ 2 := by
  rw [countedScan_correct]
  refine ⟨rfl, ?_⟩
  simpa [pow_two] using Nat.mul_le_mul_left n (inspected_le (succeeds M n) 1 n)

end EthInapproximability.CurrentPaper.SlowClock
