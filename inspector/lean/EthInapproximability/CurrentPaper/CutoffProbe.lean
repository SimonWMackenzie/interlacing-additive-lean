import EthInapproximability.CurrentPaper.FlaggedBoundedBitMachine
import EthInapproximability.CurrentPaper.CutoffBudgetTest

/-!
# Identifying bounded machine reports with the paper's cutoff test

Source: frozen v8 `05-iteration.tex`, `eq:paper-slow-clock`. This connects
the actual simulator's returned bits to the already-defined slow-clock
success predicate, including timeouts. The outer repeated caller and its
packing/transfers are not silently treated as free by this interface.
-/

namespace EthInapproximability.CurrentPaper.CutoffProbe

open BitMachine

variable (M : Machine)

def input (n k : ℕ) : List Bool :=
  BoundedBitMachine.packed n (CutoffBitMachine.encodedNat k)

noncomputable def report (n k : ℕ) : List Bool :=
  FlaggedBoundedBitMachine.report M (input n k)

def interpret (budget : ℕ) (report : List Bool) : Bool :=
  match report with
  | [] => false
  | halted :: payload => halted && decide (CutoffBitMachine.decodedNat payload ≤ budget)

theorem report_eq (n k : ℕ) : report M n k =
    decide ((M.run n (M.init (CutoffBitMachine.encodedNat k))).l = none) ::
      (M.run n (M.init (CutoffBitMachine.encodedNat k))).stk M.output :=
  FlaggedBoundedBitMachine.report_packed M n (CutoffBitMachine.encodedNat k)

theorem interpret_report (n k : ℕ) :
    interpret n (report M n k) = SlowClock.succeeds (CutoffBitMachine.clock M) n k := by
  rw [report_eq]
  unfold interpret SlowClock.succeeds
  rw [CutoffBitMachine.clock_run]
  unfold CutoffBitMachine.clock
  by_cases h : (M.run n (M.init (CutoffBitMachine.encodedNat k))).l = none <;> simp [h]

theorem input_length (n k : ℕ) : (input n k).length ≤ n + 2 * (k + 1) + 1 := by
  have h := CutoffBitMachine.encodedNat_length k
  simp only [input, BoundedBitMachine.packed, List.length_append,
    List.length_replicate, List.length_cons]
  omega

theorem report_outputs (n k : ℕ) :
    (FlaggedBoundedBitMachine.machine M).OutputsWithin (input n k) (report M n k)
      (2 * (n + 2 * (k + 1) + 2) + 1) := by
  exact outputsWithin_mono _
    (FlaggedBoundedBitMachine.outputs_all M (input n k))
    (by have := input_length n k; omega)

theorem report_outputs_in_prefix (n k : ℕ) (hk : k ≤ n) :
    (FlaggedBoundedBitMachine.machine M).OutputsWithin (input n k) (report M n k)
      (6 * n + 9) :=
  outputsWithin_mono _ (report_outputs M n k) (by omega)

/-- This bound concerns physical bits even if the cutoff number encoded by
them is enormous. It is what permits a budget-limited comparison. -/
theorem payload_length (n k : ℕ) :
    ((report M n k).tail).length ≤ 2 * (k + 1) + n * M.pushBound := by
  rw [report_eq]
  simp only [List.tail_cons]
  exact CutoffBitMachine.clock_run_stack_length M n k M.output

theorem payload_length_in_prefix (n k : ℕ) (hk : k ≤ n) :
    ((report M n k).tail).length ≤ (M.pushBound + 2) * (n + 1) := by
  have h := payload_length M n k
  nlinarith

/-- A concrete quadratic upper bound for the comparison phase of every
bounded simulation occurring in the first n tests. Caller transfers remain
distinct; this is not yet a runtime theorem for the entire prefix loop. -/
theorem comparison_time_in_prefix (n k : ℕ) (hk : k ≤ n) :
    ∃ t ≤ (5 * (M.pushBound + 2) + 7) * (n + 1) ^ 2,
      (CutoffBudgetTest.machine.run t
        (CutoffBudgetTest.encode (CutoffBudgetTest.start (report M n k).tail
          (List.replicate n true) []))).l = none ∧
      (CutoffBudgetTest.machine.run t
        (CutoffBudgetTest.encode (CutoffBudgetTest.start (report M n k).tail
          (List.replicate n true) []))).stk CutoffBudgetTest.machine.output =
        decide (CutoffBitMachine.decodedNat (report M n k).tail ≤ n) ::
          List.replicate (min (CutoffBitMachine.decodedNat (report M n k).tail) n) true := by
  obtain ⟨t, ht, hh, ho⟩ := CutoffBudgetTest.machine_test_run
    (report M n k).tail (List.replicate n true) []
  refine ⟨t, ht.trans ?_, hh, ?_⟩
  · have hlen := payload_length_in_prefix M n k hk
    simp only [List.length_replicate]
    have hn : 1 ≤ n + 1 := by omega
    have hprod := Nat.mul_le_mul_left (n + 1)
      (show 4 * ((report M n k).tail).length + 5 ≤
        4 * ((M.pushBound + 2) * (n + 1)) + 5 by omega)
    nlinarith
  · simpa only [List.length_replicate, List.append_nil] using ho

end EthInapproximability.CurrentPaper.CutoffProbe
