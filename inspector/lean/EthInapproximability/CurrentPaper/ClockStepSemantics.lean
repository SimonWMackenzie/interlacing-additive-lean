import EthInapproximability.CurrentPaper.ClockStepMachine
import EthInapproximability.CurrentPaper.CutoffProbe

/-!
# Identifying the literal clock step with the consecutive-prefix clock

Source: frozen v8 `05-iteration.tex`, `eq:paper-slow-clock` and
`lem:paper-slow-diagonal`. This file identifies the already proved physical
step with the mathematical state transition; it assumes no cutoff runtime
or successful-output certificate.
-/

namespace EthInapproximability.CurrentPaper.ClockStepSemantics

noncomputable section

variable (M : BitMachine.Machine)

def bankState (budget : List Bool) (s : SlowClockPrefixLoop.State) :
    ClockStepMachine.Stack M → List Bool :=
  ClockInputPreparation.readyBank M [s.active] budget s.accepted.bits

theorem test_bits (budget : List Bool) (k : ℕ) :
    ClockStepMachine.test M budget k.bits =
      SlowClock.succeeds (CutoffBitMachine.clock M) budget.length (k+1) := by
  calc
    ClockStepMachine.test M budget k.bits =
        CutoffProbe.interpret budget.length (CutoffProbe.report M budget.length (k+1)) := by
      rw [CutoffProbe.report_eq]
      simp only [ClockStepMachine.test, CutoffInputEncoding.nextInput_bits, CutoffProbe.interpret]
    _ = _ := CutoffProbe.interpret_report M budget.length (k+1)

theorem result_state (budget : List Bool) (s : SlowClockPrefixLoop.State) :
    ClockStepMachine.result M [s.active] budget s.accepted.bits =
      bankState M budget (SlowClockPrefixLoop.step
        (SlowClock.succeeds (CutoffBitMachine.clock M) budget.length) s) := by
  cases s with
  | mk accepted active =>
      cases active <;>
        simp [ClockStepMachine.result, bankState, SlowClockPrefixLoop.step,
          test_bits, BinarySuccessorMachine.successor_bits]
      split <;> rfl

theorem stateAt_step (budget : List Bool) (j : ℕ) :
    let test := SlowClock.succeeds (CutoffBitMachine.clock M) budget.length
    ClockStepMachine.result M [(SlowClockPrefixLoop.stateAt test j).active] budget
        (SlowClockPrefixLoop.stateAt test j).accepted.bits =
      bankState M budget (SlowClockPrefixLoop.stateAt test (j+1)) := by
  dsimp only
  rw [result_state, SlowClockPrefixLoop.stateAt_step]

theorem stateAt_accepted_le (budget : List Bool) (j : ℕ) :
    (SlowClockPrefixLoop.stateAt
      (SlowClock.succeeds (CutoffBitMachine.clock M) budget.length) j).accepted ≤ j :=
  SlowClockPrefixLoop.stateAt_accepted_le _ j

theorem bits_length_le (k : ℕ) : k.bits.length ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← BinarySuccessorMachine.successor_bits]
      exact (CutoffInputEncoding.successor_length_le k.bits).trans (Nat.add_le_add_right ih 1)

theorem stateAt_counter_length (budget : List Bool) (j : ℕ) :
    (SlowClockPrefixLoop.stateAt
      (SlowClock.succeeds (CutoffBitMachine.clock M) budget.length) j).accepted.bits.length ≤ j :=
  (bits_length_le _).trans (stateAt_accepted_le M budget j)

theorem bankState_word_length (budget : List Bool) (s : SlowClockPrefixLoop.State)
    (i : ClockStepMachine.Stack M) :
    (bankState M budget s i).length ≤ budget.length+s.accepted+1 := by
  have h := bits_length_le s.accepted
  cases i with
  | inl i => fin_cases i <;> simp [bankState, ClockInputPreparation.readyBank] <;> omega
  | inr i => simp [bankState, ClockInputPreparation.readyBank]

theorem stateAt_word_length (budget : List Bool) (j : ℕ) (i : ClockStepMachine.Stack M) :
    (bankState M budget (SlowClockPrefixLoop.stateAt
      (SlowClock.succeeds (CutoffBitMachine.clock M) budget.length) j) i).length ≤
        budget.length+j+1 := by
  have h := bankState_word_length M budget
    (SlowClockPrefixLoop.stateAt (SlowClock.succeeds (CutoffBitMachine.clock M) budget.length) j) i
  have ha := stateAt_accepted_le M budget j
  omega

theorem final_accepted (budget : List Bool) :
    (SlowClockPrefixLoop.stateAt
      (SlowClock.succeeds (CutoffBitMachine.clock M) budget.length) budget.length).accepted =
      SlowClock.repetitions (CutoffBitMachine.clock M) budget.length := rfl

end
end EthInapproximability.CurrentPaper.ClockStepSemantics
