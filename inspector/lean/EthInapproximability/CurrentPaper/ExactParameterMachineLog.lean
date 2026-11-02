import EthInapproximability.CurrentPaper.UnaryBinaryEncoding
import EthInapproximability.CurrentPaper.BitMachineComposition
import Mathlib.Tactic

/-!
# A physical unary ceiling-logarithm primitive

The exact source padding and the two sampler degrees use `Nat.clog 2`.
On a positive unary input of length `n`, remove one unary cell, count the
remaining `n-1` cells into canonical binary, then count that binary word's
length into unary. Each stage is a finite Boolean-stack program, and both
intermediate transfers are charged by `BitMachineComposition`.

Source: frozen v8 `E-exact-details.tex`, scalar formulas, and
`B-effectivity-details.tex`, fixed finite Boolean-stack runtime convention.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineLog

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

/-- Removing the first unary cell implements predecessor, including zero. -/
def predecessorProgram : Fin 1 → TM2.Stmt (fun _ : Fin 1 => Bool) (Fin 1) Unit
  | _ => pop 0 (fun _ _ => ()) halt

noncomputable def predecessorMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) () predecessorProgram

theorem predecessor_outputs (input : List Bool) :
    predecessorMachine.OutputsWithin input input.tail 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 1) (0 : Fin 1) (0 : Fin 1) ()
    predecessorProgram input input.tail 1 1 (by omega)
  · simp [rawInit, predecessorProgram, advance, TM2.step, TM2.stepAux]
  · simp [rawInit, predecessorProgram, advance, TM2.step, TM2.stepAux]

/-- One physical transition consumes a binary digit and appends one unary cell. -/
def bitLengthProgram : Fin 1 → TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 1) Bool
  | _ => pop 0 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (load (fun _ => false) (goto (fun _ => 0)))) halt)

abbrev BitLengthConfig := TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) Bool

def bitLengthCfg (q : List Bool) (out : List Bool) : BitLengthConfig :=
  ⟨some 0, false, ![q, out]⟩

def bitLengthRun (t : ℕ) (c : BitLengthConfig) : BitLengthConfig :=
  ((advance bitLengthProgram)^[t]) c

private theorem bitLength_cons (b : Bool) (q out : List Bool) :
    advance bitLengthProgram (bitLengthCfg (b :: q) out) =
      bitLengthCfg q (true :: out) := by
  simp [advance, bitLengthProgram, bitLengthCfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem bitLength_nil (out : List Bool) :
    advance bitLengthProgram (bitLengthCfg [] out) =
      (⟨none, false, ![[], out]⟩ : BitLengthConfig) := by
  simp [advance, bitLengthProgram, bitLengthCfg, TM2.step, TM2.stepAux]

theorem bitLength_run (q out : List Bool) :
    bitLengthRun (q.length + 1) (bitLengthCfg q out) =
      (⟨none, false, ![[], List.replicate q.length true ++ out]⟩ : BitLengthConfig) := by
  induction q generalizing out with
  | nil => simp [bitLengthRun, bitLength_nil]
  | cons b q ih =>
      rw [List.length_cons, bitLengthRun, Function.iterate_succ_apply,
        bitLength_cons]
      simpa [bitLengthRun, List.replicate_succ', List.append_assoc] using ih (true :: out)

noncomputable def bitLengthMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) false bitLengthProgram

theorem bitLength_outputs (q : List Bool) :
    bitLengthMachine.OutputsWithin q (List.replicate q.length true) (q.length + 1) := by
  have hi : rawInit (0 : Fin 2) (0 : Fin 1) false q = bitLengthCfg q [] := by
    simp [rawInit, bitLengthCfg]
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 2) (1 : Fin 2) (0 : Fin 1) false
    bitLengthProgram q (List.replicate q.length true) (q.length + 1) (q.length + 1)
    (by omega)
  · rw [hi]; exact congrArg TM2.Cfg.l (bitLength_run q [])
  · rw [hi]; simpa using congrArg (fun c : BitLengthConfig => c.stk 1) (bitLength_run q [])

/-- The binary size of the predecessor is exactly ceiling log, even at zero. -/
theorem clog_eq_pred_bits_length (n : ℕ) :
    Nat.clog 2 n = (n - 1).bits.length := by
  cases n with
  | zero => rfl
  | succ k =>
      simp only [Nat.succ_sub_one]
      rw [Nat.size_eq_bits_len]
      apply Nat.le_antisymm
      · exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
          (Nat.succ_le_of_lt (Nat.lt_size_self k))
      · apply Nat.size_le.mpr
        exact lt_of_lt_of_le (Nat.lt_succ_self k)
          (Nat.le_pow_clog (by decide : 1 < 2) (k + 1))

noncomputable def machine : BitMachine.Machine :=
  composition (composition predecessorMachine UnaryBinaryEncoding.machine) bitLengthMachine

theorem outputs (n : ℕ) :
    machine.OutputsWithin (List.replicate n true)
      (List.replicate (Nat.clog 2 n) true)
      ((UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2) := by
  have hpred := predecessor_outputs (List.replicate n true)
  have hbin := UnaryBinaryEncoding.outputs (List.replicate n true |>.tail)
  have hfirst := composition_outputsWithin predecessorMachine UnaryBinaryEncoding.machine
    hpred hbin
  have htail : (List.replicate n true).tail = List.replicate (n - 1) true := by
    cases n <;> rfl
  rw [htail] at hfirst
  simp only [List.length_replicate] at hfirst
  have hsecond := bitLength_outputs (n - 1).bits
  have hcomp := composition_outputsWithin
    (composition predecessorMachine UnaryBinaryEncoding.machine) bitLengthMachine
    hfirst hsecond
  change machine.OutputsWithin (List.replicate n true)
    (List.replicate (n - 1).bits.length true) _ at hcomp
  rw [← clog_eq_pred_bits_length] at hcomp
  apply BitMachine.outputsWithin_mono _ hcomp
  have hlen : (n - 1).bits.length ≤ n :=
    (UnaryBinaryEncoding.bits_length_le _).trans (Nat.sub_le n 1)
  rw [← clog_eq_pred_bits_length] at hlen
  simp only [List.length_replicate, htail] at *
  have hp : (n - 1 + 1) ^ 2 ≤ (n + 1) ^ 2 := by gcongr; omega
  have hc := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hp
  have hlin : 1 + 2 * (n - 1) + 2 + 2 * Nat.clog 2 n + 2 +
      (Nat.clog 2 n + 1) ≤ 6 * (n + 1) := by omega
  have hquad : 6 * (n + 1) ≤ 6 * (n + 1) ^ 2 := by nlinarith
  rw [Nat.add_mul]
  omega

end EthInapproximability.CurrentPaper.ExactParameterMachineLog
