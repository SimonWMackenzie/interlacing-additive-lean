import CurrentAdditive.UnsignedCompare

/-! Framed, all-input physical variable-width unsigned comparator. -/

namespace EthInapproximability.CurrentPaper.UnsignedComparePacket

open UnsignedCompare
open Turing
open BitMachineEncoding

def finalBank (S : Fin 3 → List Bool) : Fin 3 → List Bool :=
  bank ((S 2).reverse ++ (BitMachineBinaryDivision.subAny (S 0) (S 1) false).1)
    [(BitMachineBinaryDivision.subAny (S 0) (S 1) false).2] []

def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result finalBank input

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program .scan initial

theorem local_run (S : Fin 3 → List Bool) :
    ((advance program)^[2 * max (S 0).length (S 1).length + (S 2).length + 2])
      (⟨some .scan, initial, S⟩ :
        Turing.TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) =
      ⟨none, initial, finalBank S⟩ := by
  have h := UnsignedCompare.scan_correct (S 0) (S 1) false (S 2)
  have hbank : UnsignedCompare.bank (S 0) (S 1) (S 2) = S := by
    funext k; fin_cases k <;> rfl
  rw [UnsignedCompare.run, UnsignedCompare.cfg, hbank] at h
  simpa [UnsignedCompare.run, UnsignedCompare.cfg, UnsignedCompare.bank,
    UnsignedCompare.initial, finalBank] using h

theorem time_bound (S : Fin 3 → List Bool) :
    2 * max (S 0).length (S 1).length + (S 2).length + 2 ≤
      3 * ((BitMachineBankCodec.encode S).length + 1) := by
  have h0 := BitMachineBankCodec.word_length_le_encode S (0 : Fin 3)
  have h1 := BitMachineBankCodec.word_length_le_encode S (1 : Fin 3)
  have h2 := BitMachineBankCodec.word_length_le_encode S (2 : Fin 3)
  omega

theorem size_bound (S : Fin 3 → List Bool) :
    (BitMachineBankCodec.encode (finalBank S)).length ≤
      6 * ((BitMachineBankCodec.encode S).length + 1) := by
  have h0 := BitMachineBankCodec.word_length_le_encode S (0 : Fin 3)
  have h1 := BitMachineBankCodec.word_length_le_encode S (1 : Fin 3)
  have h2 := BitMachineBankCodec.word_length_le_encode S (2 : Fin 3)
  have hl := BitMachineBinaryDivision.subAny_length (S 0) (S 1) false
  have hlen : (BitMachineBankCodec.encode (finalBank S)).length =
      2 * ((S 2).length + max (S 0).length (S 1).length + 1) + 3 := by
    rw [BitMachineBankCodec.encode_length]
    simp [Fin.sum_univ_succ, finalBank, UnsignedCompare.bank,
      BitMachineBinaryDivision.subAny_length]
  rw [hlen]
  omega

theorem polytime : BitMachine.Polytime result := by
  exact BitMachineBankWrapper.polytime program .scan initial finalBank 3 1 6 1
    (by
      intro S
      refine ⟨2 * max (S 0).length (S 1).length + (S 2).length + 2,
        ⟨none, initial, finalBank S⟩, ?_, local_run S, rfl, rfl⟩
      simpa using time_bound S)
    (by intro S; simpa using size_bound S)

def packedInput (a b : List Bool) : List Bool :=
  BitMachineBankCodec.encode (bank a b [])

def decodeBorrow (output : List Bool) : Option Bool := do
  let S ← BitMachineBankCodec.decode 3 output
  match S 1 with
  | [v] => some v
  | _ => none

def decodeDifference (output : List Bool) : Option ℕ := do
  let S ← BitMachineBankCodec.decode 3 output
  pure (EncodedCommunication.bitsValue (S 0))

theorem packed_result (a b : List Bool) :
    result (packedInput a b) =
      BitMachineBankCodec.encode (finalBank (bank a b [])) := by
  simp [result, packedInput, BitMachineBankWrapper.result]

theorem packed_borrow (a b : List Bool) :
    decodeBorrow (result (packedInput a b)) =
      some (decide (EncodedCommunication.bitsValue a <
        EncodedCommunication.bitsValue b)) := by
  rw [packed_result]
  simp [decodeBorrow, finalBank, bank,
    (BitMachineBinaryDivision.subAny_spec a b).1]

theorem malformed_result (input : List Bool)
    (h : BitMachineBankCodec.decode 3 input = none) :
    result input = [] := by
  simp [result, BitMachineBankWrapper.result, h]

#print axioms polytime
#print axioms packed_borrow

end EthInapproximability.CurrentPaper.UnsignedComparePacket
