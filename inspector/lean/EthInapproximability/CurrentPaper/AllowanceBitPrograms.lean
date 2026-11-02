import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.ClockRuntime
import EthInapproximability.CurrentPaper.SourceFieldWriter
import EthInapproximability.CurrentPaper.FinalPadding
import EthInapproximability.CurrentPaper.ETHTailGrowth
import EthInapproximability.CurrentPaper.ClockedPadding

namespace EthInapproximability.CurrentPaper.AllowanceBitPrograms

open Turing TM2.Stmt BitMachine BitMachineEncoding

/-- Delete the least significant bit, but retain a one-bit simulation budget
when there is no remaining bit. Only the output length is used downstream. -/
def positiveTail : List Bool → List Bool
  | _ :: b :: bs => b :: bs
  | _ => [false]

def tailProgram (_ : Unit) : TM2.Stmt (fun _ : Unit => Bool) Unit (Option Bool) :=
  pop () (fun v _ => v) (pop () (fun _ b => b)
    (push () (fun v => v.getD false) halt))

noncomputable def tailMachine : Machine := ofFinite () () () none tailProgram

theorem tail_outputs (input : List Bool) :
    tailMachine.OutputsWithin input (positiveTail input) 1 := by
  apply outputsWithin_of_raw_run () () () none tailProgram input (positiveTail input)
    1 1 (by omega)
  · rfl
  · cases input with
    | nil => rfl
    | cons b bs => cases bs <;> rfl

theorem tail_polytime : Polytime positiveTail := by
  refine ⟨tailMachine, 1, 0, ?_⟩
  intro input
  simpa using tail_outputs input

theorem positiveTail_length (input : List Bool) :
    (positiveTail input).length = max 1 (input.length - 1) := by
  cases input with
  | nil => rfl
  | cons b bs =>
    cases bs with
    | nil => rfl
    | cons b' bs => simp [positiveTail]

def dropProgram (_ : Unit) : TM2.Stmt (fun _ : Unit => Bool) Unit Unit :=
  pop () (fun v _ => v) (pop () (fun v _ => v) halt)

noncomputable def dropMachine : Machine := ofFinite () () () () dropProgram

theorem drop_outputs (input : List Bool) :
    dropMachine.OutputsWithin input (input.drop 2) 1 := by
  apply outputsWithin_of_raw_run () () () () dropProgram input (input.drop 2)
    1 1 (by omega)
  · rfl
  · cases input with
    | nil => rfl
    | cons b bs => cases bs <;> rfl

theorem drop_polytime : Polytime (fun input => input.drop 2) := by
  refine ⟨dropMachine, 1, 0, ?_⟩
  intro input
  simpa using drop_outputs input

theorem positiveTail_bits_length (n : Nat) :
    (positiveTail n.bits).length = Nat.log 2 (max n 2) := by
  rw [positiveTail_length, Nat.size_eq_bits_len]
  by_cases hn : n < 2
  · interval_cases n <;> decide
  · have hn2 : 2 ≤ n := by omega
    have hs : 1 < n.size := Nat.lt_size.mpr (by simpa using hn2)
    have hp : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    have hq : n < 2 ^ (n.size - 1 + 1) := by
      simpa only [show n.size - 1 + 1 = n.size by omega] using Nat.lt_size_self n
    rw [max_eq_left hn2, Nat.log_eq_of_pow_le_of_lt_pow hp hq,
      max_eq_right (by omega : 1 ≤ n.size - 1)]

theorem drop_bits_div_four (n : Nat) : n.bits.drop 2 = (n / 4).bits := by
  have ht (w : List Bool) : w.drop 2 = w.tail.tail := by
    cases w with
    | nil => rfl
    | cons b bs => cases bs <;> rfl
  rw [ht, ← Nat.div2_bits_eq_tail, ← Nat.div2_bits_eq_tail,
    Nat.div2_val, Nat.div2_val, Nat.div_div_eq_div_mul]

theorem project_natField (n : Nat) :
    BankFieldProjection.result (0 : Fin 1) (EncodedCommunication.natField n) = n.bits := by
  have he : BitMachineBankCodec.encode (fun _ : Fin 1 => n.bits) =
      EncodedCommunication.natField n := by
    simp [BitMachineBankCodec.encode_eq_list, List.ofFn_succ, EncodedCommunication.natField]
  rw [← he, BankFieldProjection.result_encode]

/-- Total bit-string map: parse, form the logarithmic simulation budget,
run the bounded clock, divide its binary result by four, and frame it. -/
noncomputable def codedAllowance (c A d : Nat) (input : List Bool) : List Bool :=
  EncodedCommunication.field
    ((SlowClock.repetitions (CutoffBitMachine.actualClock c A d)
      (positiveTail (BankFieldProjection.result (0 : Fin 1) input)).length).bits.drop 2)

theorem codedAllowance_polytime (c A d : Nat) : Polytime (codedAllowance c A d) := by
  have h0 := BankFieldProjection.polytime (0 : Fin 1)
  have h1 := BitMachineComposition.polytime_comp h0 tail_polytime
  have h2 := BitMachineComposition.polytime_comp h1 (ClockRuntime.actualClock_polytime c A d)
  have h3 := BitMachineComposition.polytime_comp h2 drop_polytime
  have h4 := BitMachineComposition.polytime_comp h3 SourceFieldWriter.field_polytime
  simpa only [Function.comp_def, codedAllowance] using h4

theorem codedAllowance_natField (c A d T : Nat) :
    codedAllowance c A d (EncodedCommunication.natField T) =
      EncodedCommunication.natField
        (FinalPadding.allowance (ETHTailGrowth.repetitions c A d) T) := by
  unfold codedAllowance
  rw [project_natField, positiveTail_bits_length, drop_bits_div_four]
  rfl

/-- One actual machine, fixed before the numeric input, computes the exact
allowance on the repository codec; all composition and parsing costs count. -/
theorem allowance_natField_polytime (c A d : Nat) :
    ∃ (M : Machine) (C E : Nat), ∀ T : Nat,
      M.OutputsWithin (EncodedCommunication.natField T)
        (EncodedCommunication.natField
          (FinalPadding.allowance (ETHTailGrowth.repetitions c A d) T))
        (C * ((EncodedCommunication.natField T).length + 1) ^ E) := by
  obtain ⟨M, C, E, hM⟩ := codedAllowance_polytime c A d
  refine ⟨M, C, E, ?_⟩
  intro T
  simpa only [codedAllowance_natField] using hM (EncodedCommunication.natField T)

theorem allowance_monotone (c A d : Nat) :
    Monotone (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)) :=
  ClockedPadding.allowance_monotone (CutoffBitMachine.actualClock c A d)

theorem allowance_unbounded (c A d : Nat) :
    Filter.Tendsto (FinalPadding.allowance (ETHTailGrowth.repetitions c A d))
      Filter.atTop Filter.atTop :=
  ClockedPadding.allowance_tendsto_atTop (CutoffBitMachine.actualClock c A d)
    (CutoffBitMachine.actualClock_terminates c A d)

#print axioms tail_outputs
#print axioms drop_outputs
#print axioms positiveTail_bits_length
#print axioms drop_bits_div_four
#print axioms allowance_natField_polytime
#print axioms allowance_monotone
#print axioms allowance_unbounded

end EthInapproximability.CurrentPaper.AllowanceBitPrograms
