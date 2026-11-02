import EthInapproximability.CurrentPaper.AllowanceBitPrograms
import EthInapproximability.CurrentPaper.WeightedRawWordsFuel
import EthInapproximability.CurrentPaper.MatrixBinaryAddress
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.ExactParameterMachineLog

/-!
# Physical dimension-field decoding to a unary counter

This is the first stage of an all-dimension family printer. One fixed
machine reads `natField d` and outputs `true^d`, with a clock linear in
the numerical dimension. It composes the production field projection,
a two-stack reversal, and the production binary-to-unary address machine.
Malformed inputs are not yet rejected by this stage.
-/

namespace DimensionNatUnary

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

def reverseProgram : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool)
  | () => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun v => v.getD false) (goto (fun _ => ()))) halt)

def reverseCfg (l : Option Unit) (v : Option Bool)
    (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool) :=
  ⟨l, v, ![input, output]⟩

private theorem reverse_cons (b : Bool) (q out : List Bool) (v : Option Bool) :
    advance reverseProgram (reverseCfg (some ()) v (b :: q) out) =
      reverseCfg (some ()) (some b) q (b :: out) := by
  simp [advance, reverseProgram, reverseCfg, TM2.step, TM2.stepAux]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem reverse_nil (out : List Bool) (v : Option Bool) :
    advance reverseProgram (reverseCfg (some ()) v [] out) =
      reverseCfg none none [] out := by
  simp [advance, reverseProgram, reverseCfg, TM2.step, TM2.stepAux]

theorem reverse_run (q out : List Bool) (v : Option Bool) :
    ((advance reverseProgram)^[q.length + 1])
      (reverseCfg (some ()) v q out) =
        reverseCfg none none [] (q.reverse ++ out) := by
  induction q generalizing out v with
  | nil => simp [reverse_nil]
  | cons b q ih =>
      rw [List.length_cons, Function.iterate_succ_apply, reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (b :: out) (some b)

noncomputable def reverseMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) (1 : Fin 2) () none reverseProgram

theorem reverse_outputs (q : List Bool) :
    reverseMachine.OutputsWithin q q.reverse (q.length + 1) := by
  have hi : rawInit (0 : Fin 2) () none q = reverseCfg (some ()) none q [] := by
    unfold rawInit reverseCfg
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 2) (1 : Fin 2) () none
    reverseProgram q q.reverse (q.length + 1) (q.length + 1) (by omega)
  · rw [hi, reverse_run]
    rfl
  · rw [hi, reverse_run]
    simp [reverseCfg]

noncomputable def bitsMachine : BitMachine.Machine :=
  composition reverseMachine MatrixBinaryAddress.bitMachine

theorem bits_outputs (d : ℕ) :
    bitsMachine.OutputsWithin d.bits (List.replicate d true)
      (4 * d + 6 * d.bits.length + 5) := by
  have h₁ := reverse_outputs d.bits
  have h₂ := MatrixBinaryAddress.bitMachine_outputs d.bits.reverse
  rw [WeightedRawWords.valueFrom_bits_reverse] at h₂
  have h := composition_outputsWithin reverseMachine
    MatrixBinaryAddress.bitMachine h₁ h₂
  apply BitMachine.outputsWithin_mono bitsMachine
    (by simpa only [bitsMachine] using h)
  simp only [List.length_reverse]
  omega

noncomputable def dimensionMachine : BitMachine.Machine :=
  composition (BankFieldProjection.machine (0 : Fin 1)) bitsMachine

theorem field_outputs (d : ℕ) :
    dimensionMachine.OutputsWithin (EncodedCommunication.natField d)
      (List.replicate d true)
      (6 * ((EncodedCommunication.natField d).length + 1) +
        2 * d.bits.length + 2 + (4 * d + 6 * d.bits.length + 5)) := by
  have h₁ := BankFieldProjection.outputs (0 : Fin 1)
    (EncodedCommunication.natField d)
  rw [AllowanceBitPrograms.project_natField] at h₁
  have h₂ := bits_outputs d
  have h := composition_outputsWithin (BankFieldProjection.machine (0 : Fin 1))
    bitsMachine h₁ h₂
  simpa only [dimensionMachine] using h

theorem field_outputs_linear (d : ℕ) :
    dimensionMachine.OutputsWithin (EncodedCommunication.natField d)
      (List.replicate d true) (24 * (d + 1)) := by
  have h := field_outputs d
  have hb := UnaryBinaryEncoding.bits_length_le d
  have hf : (EncodedCommunication.natField d).length =
      2 * d.bits.length + 1 := by
    exact EncodedCommunication.field_length d.bits
  apply BitMachine.outputsWithin_mono dimensionMachine h
  rw [hf]
  omega

noncomputable def dimensionLogMachine : BitMachine.Machine :=
  composition dimensionMachine ExactParameterMachineLog.machine

theorem dimension_log_outputs (r : ℕ) :
    let d := 2 ^ r
    dimensionLogMachine.OutputsWithin (EncodedCommunication.natField d)
      (List.replicate r true)
      ((UnaryBinaryEncoding.coefficient + 32) * (d + 1) ^ 2) := by
  dsimp
  let d := 2 ^ r
  have h₁ := field_outputs_linear d
  have h₂ := ExactParameterMachineLog.outputs d
  rw [Nat.clog_pow 2 r (by decide : 1 < 2)] at h₂
  have h := composition_outputsWithin dimensionMachine
    ExactParameterMachineLog.machine h₁ h₂
  apply BitMachine.outputsWithin_mono dimensionLogMachine
    (by simpa only [dimensionLogMachine] using h)
  simp only [List.length_replicate]
  have hd : 1 ≤ d := Nat.one_le_pow _ _ (by decide)
  have h1 : d + 1 ≤ (d + 1) ^ 2 := by nlinarith
  change 24 * (d + 1) + 2 * d + 2 +
    (UnaryBinaryEncoding.coefficient + 6) * (d + 1) ^ 2 ≤
      (UnaryBinaryEncoding.coefficient + 32) * (d + 1) ^ 2
  nlinarith [Nat.mul_le_mul_left 26 h1]

#print axioms DimensionNatUnary.field_outputs
#print axioms DimensionNatUnary.field_outputs_linear
#print axioms DimensionNatUnary.dimension_log_outputs

end DimensionNatUnary
