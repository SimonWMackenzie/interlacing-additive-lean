import EthInapproximability.CurrentPaper.SlowClock

/-!
# The state invariant of the bounded cutoff prefix loop

Source: frozen v8 `05-iteration.tex`, `eq:paper-slow-clock`. This is the
semantic invariant used by the finite driver: after a failed test the
successful prefix stays unchanged, and no later test can revive it. The
definitions here are not a substitute for the driver's stack instructions.
-/

namespace EthInapproximability.CurrentPaper.SlowClockPrefixLoop

open SlowClock

theorem prefixCount_append (test : ℕ → Bool) (start n m : ℕ) :
    prefixCount test start (n + m) =
      if prefixCount test start n < n then prefixCount test start n
      else n + prefixCount test (start + n) m := by
  induction n generalizing start with
  | zero => simp [prefixCount]
  | succ n ih =>
      by_cases h : test start = true
      · have hshape : n + 1 + m = (n + m) + 1 := by omega
        rw [hshape, prefixCount, if_pos h, ih, prefixCount, if_pos h]
        by_cases hn : prefixCount test (start + 1) n < n
        · have hh : 1 + prefixCount test (start + 1) n < n + 1 := by omega
          simp only [hn, hh, if_true]
        · have hh : ¬ 1 + prefixCount test (start + 1) n < n + 1 := by omega
          simp only [hn, hh, if_false]
          simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · have hshape : n + 1 + m = (n + m) + 1 := by omega
        simp only [hshape, prefixCount, h, if_false]
        simp

theorem prefixCount_step (test : ℕ → Bool) (start n : ℕ) :
    prefixCount test start (n + 1) =
      if prefixCount test start n = n ∧ test (start + n) = true then n + 1
      else prefixCount test start n := by
  rw [prefixCount_append]
  have hb := prefixCount_le test start n
  by_cases he : prefixCount test start n = n
  · rw [he]
    by_cases ht : test (start + n) = true <;> simp [prefixCount, ht]
  · have hlt : prefixCount test start n < n := by omega
    simp [hlt, he]

structure State where
  accepted : ℕ
  active : Bool
  deriving DecidableEq

def initial : State := ⟨0, true⟩

def step (test : ℕ → Bool) (s : State) : State :=
  if s.active && test (s.accepted + 1) then ⟨s.accepted + 1, true⟩
  else ⟨s.accepted, false⟩

def stateAt (test : ℕ → Bool) (n : ℕ) : State :=
  ⟨prefixCount test 1 n, decide (prefixCount test 1 n = n)⟩

theorem stateAt_zero (test : ℕ → Bool) : stateAt test 0 = initial := rfl

theorem stateAt_step (test : ℕ → Bool) (n : ℕ) :
    step test (stateAt test n) = stateAt test (n + 1) := by
  have hb := prefixCount_le test 1 n
  have hp := prefixCount_step test 1 n
  by_cases he : prefixCount test 1 n = n
  · by_cases ht : test (n + 1) = true
    · have hn : prefixCount test 1 (n + 1) = n + 1 := by simpa [he, Nat.add_comm, ht] using hp
      simp [step, stateAt, he, ht, hn]
    · have hn : prefixCount test 1 (n + 1) = n := by simpa [he, Nat.add_comm, ht] using hp
      have hf : test (n + 1) = false := by cases h : test (n + 1) <;> simp_all
      simp [step, stateAt, he, hf, hn]
  · have hn : prefixCount test 1 (n + 1) = prefixCount test 1 n := by simp [he] at hp; exact hp
    have hne : prefixCount test 1 n ≠ n + 1 := by omega
    simp [step, stateAt, he, hn, hne]

theorem iterate_state (test : ℕ → Bool) (n : ℕ) :
    (step test)^[n] initial = stateAt test n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, stateAt_step]

theorem iterate_clock {S : Type*} (M : SlowClock.Machine S) (n : ℕ) :
    ((step (succeeds M n))^[n] initial).accepted = repetitions M n := by
  rw [iterate_state]
  rfl

theorem stateAt_accepted_le (test : ℕ → Bool) (n : ℕ) :
    (stateAt test n).accepted ≤ n := prefixCount_le test 1 n

theorem inactive_fixed (test : ℕ → Bool) (s : State) (h : s.active = false) :
    step test s = s := by
  cases s with
  | mk a active => cases active <;> simp_all [step]

end EthInapproximability.CurrentPaper.SlowClockPrefixLoop
