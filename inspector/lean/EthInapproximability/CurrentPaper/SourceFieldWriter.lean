import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-!
# Writing the source adapter's canonical numeric fields

Source: frozen v8 `06-eth.tex`, the literal bit encoding in the source
reduction. Framing uses the existing physical bank serializer, and unary
counts use the actual binary-successor iteration. The final composition
charges both transfers. No natural-number register is a machine primitive.
-/

namespace EthInapproximability.CurrentPaper.SourceFieldWriter

open Turing BitMachineEncoding EncodedCommunication

noncomputable def fieldMachine : BitMachine.Machine :=
  ofFinite (Sum.inl (0 : Fin 1) : BitMachineBankSerialize.Stack 1) (.inr 2)
    (.emit 0) (none : Option Bool) (BitMachineBankSerialize.program 1)

theorem field_initial (word : List Bool) :
    rawInit (Sum.inl (0 : Fin 1) : BitMachineBankSerialize.Stack 1)
      (.emit 0) (none : Option Bool) word =
    BitMachineBankSerialize.cfg (some (.emit 0)) none (fun _ : Fin 1 => word) [] [] [] := by
  simp only [rawInit, BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents]
  congr 1
  funext j
  cases j with
  | inl j => fin_cases j; rfl
  | inr j => fin_cases j <;> rfl

theorem field_outputs (word : List Bool) :
    fieldMachine.OutputsWithin word (field word) (4 * word.length + 4) := by
  obtain ⟨t, S, ht, hr⟩ := BitMachineBankSerialize.serialize (fun _ : Fin 1 => word) [] []
  have hencode : BitMachineBankSerialize.encode (List.ofFn fun _ : Fin 1 => word) =
      field word := by simp [BitMachineBankSerialize.encode, List.ofFn_succ]
  rw [hencode, List.append_nil] at hr
  rw [hencode, field_length] at ht
  apply outputsWithin_of_raw_run (Sum.inl (0 : Fin 1) : BitMachineBankSerialize.Stack 1)
    (.inr 2) (.emit 0) (none : Option Bool) (BitMachineBankSerialize.program 1)
    word (field word) t _ (by omega)
  · rw [field_initial]
    change (BitMachineBankSerialize.run t _).l = none
    rw [hr]
    rfl
  · rw [field_initial]
    change (BitMachineBankSerialize.run t _).stk (.inr 2) = _
    rw [hr]
    rfl

theorem field_polytime : BitMachine.Polytime field := by
  refine ⟨fieldMachine, 4, 1, fun word => ?_⟩
  simpa only [pow_one, Nat.mul_add, Nat.mul_one] using field_outputs word

noncomputable def unaryFieldMachine : BitMachine.Machine :=
  BitMachineComposition.composition UnaryBinaryEncoding.machine fieldMachine

theorem unary_field_outputs (input : List Bool) :
    unaryFieldMachine.OutputsWithin input (natField input.length)
      ((UnaryBinaryEncoding.coefficient + 10) * (input.length + 1) ^ 2) := by
  have h := BitMachineComposition.composition_outputsWithin UnaryBinaryEncoding.machine
    fieldMachine (UnaryBinaryEncoding.outputs input) (field_outputs input.length.bits)
  apply BitMachine.outputsWithin_mono _ h
  have hb := UnaryBinaryEncoding.bits_length_le input.length
  nlinarith

theorem unary_field_polytime : BitMachine.Polytime (fun input => natField input.length) :=
  ⟨unaryFieldMachine, UnaryBinaryEncoding.coefficient + 10, 2, unary_field_outputs⟩

end EthInapproximability.CurrentPaper.SourceFieldWriter
