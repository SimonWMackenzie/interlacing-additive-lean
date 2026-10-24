import CurrentAdditive.RationalProductCore
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-!
Packed, all-input physical rational product. The public packet has twelve
framed fields: positions 3,4,9,10 carry the four operands; the remaining
positions are scratch and are physically cleared on every decoded packet.
Positions 0 and 6 of the output contain the two unreduced products.
-/

namespace EthInapproximability.CurrentPaper.RationalProductPacket

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open RationalProductCore
open scoped BigOperators

abbrev Label := RationalProductCore.Label ⊕ Fin 9
abbrev Control := RationalProductCore.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : RationalProductCore.Stack => Bool) Label Control

def clearSlot : Fin 8 → RationalProductCore.Stack := ![0,1,2,5,6,7,8,11]

def rawStart : RationalProductCore.Label :=
  BitMachineRawSequence.leftLabel halfStart

def initial : Control := ((halfInitial, halfInitial), none)

def program : Label → TM2.Stmt (fun _ : RationalProductCore.Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl (fun v => (v, none)) Prod.fst none
      (RationalProductCore.program l)
  | .inr i =>
      if h : i.val < 8 then
        BitMachineClearBank.clearStep (clearSlot ⟨i.val,h⟩) (.inr i)
          (.inr ⟨i.val+1,by omega⟩)
      else
        BitMachineClearBank.finishStep (fun _ => (halfInitial, halfInitial))
          (.inl rawStart)

def operands (S : RationalProductCore.Bank) :
    List Bool × List Bool × List Bool × List Bool :=
  (S 3, S 9, S 4, S 10)

def normalized (S : RationalProductCore.Bank) : RationalProductCore.Bank :=
  inputBank (S 3) (S 9) (S 4) (S 10)

def resultBank (S : RationalProductCore.Bank) : RationalProductCore.Bank :=
  outputBank (S 3) (S 9) (S 4) (S 10)

def clearTime (S : RationalProductCore.Bank) : ℕ :=
  (∑ i : Fin 8, (S (clearSlot i)).length) + 9

theorem cleared_eq_normalized (S : RationalProductCore.Bank) :
    BitMachineClearBank.cleared clearSlot S = normalized S := by
  funext k
  fin_cases k <;>
    simp [BitMachineClearBank.cleared, clearSlot, normalized, inputBank,
      firstBank, BitMachineBinaryMultiply.initialBank,
      BitMachineBinaryMultiply.finBank, BitMachineBinaryMultiply.finStack,
      BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank,
      BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank,
      firstStacks, finSumFinEquiv, Fin.addCases, Fin.exists_fin_succ]

theorem clear_run (S : RationalProductCore.Bank) :
    ((advance program)^[clearTime S])
      (⟨some (.inr 0), initial, S⟩ : Config) =
      ⟨some (.inl rawStart), initial, normalized S⟩ := by
  have h := BitMachineClearBank.clear_bank_run program
    (fun _ : RationalProductCore.Control => (halfInitial, halfInitial))
    (.inl rawStart) 8 clearSlot (by decide)
    (fun i : Fin 9 => (.inr i : Label))
    (by intro i; fin_cases i <;> rfl)
    (by rfl) (halfInitial, halfInitial) S
  simpa only [clearTime, initial, cleared_eq_normalized] using h

def rawTime (S : RationalProductCore.Bank) : ℕ :=
  ((S 4).length + 1) * (4 * ((S 3).length + 2 * (S 4).length) + 7) +
  ((S 10).length + 1) * (4 * ((S 9).length + 2 * (S 10).length) + 7) + 1

theorem compute_run (S : RationalProductCore.Bank) :
    ∃ t ≤ rawTime S,
      ((advance program)^[t])
        (⟨some (.inl rawStart), initial, normalized S⟩ : Config) =
      ⟨none, initial, resultBank S⟩ := by
  obtain ⟨t, ht, hr⟩ := RationalProductCore.local_run (S 3) (S 9) (S 4) (S 10)
  have hh : (((advance RationalProductCore.program)^[t])
      (⟨some rawStart, (halfInitial, halfInitial), normalized S⟩ :
        TM2.Cfg (fun _ : RationalProductCore.Stack => Bool)
          RationalProductCore.Label RationalProductCore.Control)).l = none := by
    rw [show rawStart = BitMachineRawSequence.leftLabel halfStart from rfl]
    change (((advance RationalProductCore.program)^[t])
      (⟨some (BitMachineRawSequence.leftLabel halfStart),
        (halfInitial, halfInitial), inputBank (S 3) (S 9) (S 4) (S 10)⟩ :
        TM2.Cfg (fun _ : RationalProductCore.Stack => Bool)
          RationalProductCore.Label RationalProductCore.Control)).l = none
    rw [hr]
  obtain ⟨u, hu, hrun⟩ := BitMachineInline.outputs Sum.inl
    (fun v : RationalProductCore.Control => (v, none)) Prod.fst
    (fun _ => rfl) none RationalProductCore.program program (fun _ => rfl)
    (⟨some rawStart, (halfInitial, halfInitial), normalized S⟩ :
      TM2.Cfg (fun _ : RationalProductCore.Stack => Bool)
        RationalProductCore.Label RationalProductCore.Control) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change ((advance program)^[u]) _ = _ at hrun
  rw [show ((advance RationalProductCore.program)^[t])
      (⟨some rawStart, (halfInitial, halfInitial), normalized S⟩ :
        TM2.Cfg (fun _ : RationalProductCore.Stack => Bool)
          RationalProductCore.Label RationalProductCore.Control) =
      ⟨none, (halfInitial, halfInitial), resultBank S⟩ from hr] at hrun
  simpa [BitMachineInline.cfg, initial] using hrun

theorem local_run (S : RationalProductCore.Bank) :
    ∃ t ≤ clearTime S + rawTime S,
      ((advance program)^[t])
        (⟨some (.inr 0), initial, S⟩ : Config) =
      ⟨none, initial, resultBank S⟩ := by
  obtain ⟨t, ht, hr⟩ := compute_run S
  refine ⟨clearTime S + t, by omega, ?_⟩
  rw [show clearTime S + t = t + clearTime S by omega,
    Function.iterate_add_apply, clear_run S]
  exact hr

theorem time_bound (S : RationalProductCore.Bank) :
    clearTime S + rawTime S ≤
      100 * ((BitMachineBankCodec.encode S).length + 1) ^ 2 := by
  let n := (BitMachineBankCodec.encode S).length
  have h3 := BitMachineBankCodec.word_length_le_encode S (3 : Fin 12)
  have h4 := BitMachineBankCodec.word_length_le_encode S (4 : Fin 12)
  have h9 := BitMachineBankCodec.word_length_le_encode S (9 : Fin 12)
  have h10 := BitMachineBankCodec.word_length_le_encode S (10 : Fin 12)
  have hsum : (∑ i : Fin 8, (S (clearSlot i)).length) ≤ 8 * n := by
    calc
      _ ≤ ∑ _i : Fin 8, n := Finset.sum_le_sum (by
        intro i _
        exact BitMachineBankCodec.word_length_le_encode S (clearSlot i))
      _ = 8 * n := by simp
  have ha : ((S 4).length + 1) *
      (4 * ((S 3).length + 2 * (S 4).length) + 7) ≤
      (n + 1) * (12 * n + 7) := by
    apply Nat.mul_le_mul
    · omega
    · omega
  have hb : ((S 10).length + 1) *
      (4 * ((S 9).length + 2 * (S 10).length) + 7) ≤
      (n + 1) * (12 * n + 7) := by
    apply Nat.mul_le_mul
    · omega
    · omega
  dsimp [clearTime, rawTime]
  nlinarith

theorem output_code_length (a b c d : List Bool) :
    (BitMachineBankCodec.encode (outputBank a b c d)).length =
      2 * ((BitMachineBinaryMultiply.multiplyFrom [] a c).length + a.length +
        (BitMachineBinaryMultiply.multiplyFrom [] b d).length + b.length) + 12 := by
  rw [BitMachineBankCodec.encode_length]
  simp [Fin.sum_univ_succ, outputBank, firstFinal,
    BitMachineBinaryMultiply.finalBank, BitMachineBinaryMultiply.finBank,
    BitMachineBinaryMultiply.finStack, BitMachineBinaryMultiply.cfg,
    BitMachineBinaryMultiply.rightBank, firstStacks, finSumFinEquiv,
    Fin.addCases, BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]
  omega

theorem size_bound (S : RationalProductCore.Bank) :
    (BitMachineBankCodec.encode (resultBank S)).length ≤
      20 * ((BitMachineBankCodec.encode S).length + 1) := by
  let n := (BitMachineBankCodec.encode S).length
  have h3 := BitMachineBankCodec.word_length_le_encode S (3 : Fin 12)
  have h4 := BitMachineBankCodec.word_length_le_encode S (4 : Fin 12)
  have h9 := BitMachineBankCodec.word_length_le_encode S (9 : Fin 12)
  have h10 := BitMachineBankCodec.word_length_le_encode S (10 : Fin 12)
  have ha := BitMachineBinaryMultiply.multiplyFrom_length_bound [] (S 3) (S 4)
  have hb := BitMachineBinaryMultiply.multiplyFrom_length_bound [] (S 9) (S 10)
  dsimp [resultBank]
  rw [output_code_length]
  simp only [List.length_nil, zero_le, max_eq_right] at ha hb
  omega

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program (.inr 0) initial

def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result resultBank input

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      ((2 * 12 + 1) * (input.length + 1) +
        100 * (input.length + 1) ^ 2 +
        2 * (20 * (input.length + 1)) + 4) := by
  change (BitMachineBankWrapper.machine program (.inr 0) initial).OutputsWithin
    input (BitMachineBankWrapper.result resultBank input) _
  apply BitMachineBankWrapper.outputs program (.inr 0) initial resultBank input
    (100 * (input.length + 1) ^ 2) (20 * (input.length + 1))
  · intro S hd
    obtain ⟨t, ht, hr⟩ := local_run S
    refine ⟨t, ⟨none, initial, resultBank S⟩, ?_, hr, rfl, rfl⟩
    have he := BitMachineBankCodec.encode_decode hd
    rw [← he]
    exact ht.trans (time_bound S)
  · intro S hd
    have he := BitMachineBankCodec.encode_decode hd
    rw [← he]
    exact size_bound S

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 200, 2, ?_⟩
  intro input
  apply BitMachine.outputsWithin_mono machine (outputs input)
  have h : 1 ≤ input.length + 1 := by omega
  nlinarith

def packedInput (a b c d : List Bool) : List Bool :=
  BitMachineBankCodec.encode (inputBank a b c d)

theorem packed_output (a b c d : List Bool) :
    result (packedInput a b c d) =
      BitMachineBankCodec.encode (outputBank a b c d) := by
  have h3 : inputBank a b c d 3 = a := rfl
  have h4 : inputBank a b c d 4 = c := rfl
  have h9 : inputBank a b c d 9 = b := rfl
  have h10 : inputBank a b c d 10 = d := rfl
  simp [result, packedInput, BitMachineBankWrapper.result,
    resultBank, BitMachineBankCodec.decode_encode, h3, h4, h9, h10]

theorem packed_outputs (a b c d : List Bool) :
    machine.OutputsWithin (packedInput a b c d)
      (BitMachineBankCodec.encode (outputBank a b c d))
      (200 * ((packedInput a b c d).length + 1) ^ 2) := by
  rw [← packed_output]
  apply BitMachine.outputsWithin_mono machine (outputs (packedInput a b c d))
  have h : 1 ≤ (packedInput a b c d).length + 1 := by omega
  nlinarith

/-- The public decoder reads exactly the two designated product fields from
the twelve-field packet. No rational normalization is performed. -/
def decodeProducts (packet : List Bool) : Option (ℕ × ℕ) := do
  let S ← BitMachineBankCodec.decode 12 packet
  pure (EncodedCommunication.bitsValue (S 0),
    EncodedCommunication.bitsValue (S 6))

theorem decode_result (input : List Bool) (S : RationalProductCore.Bank)
    (h : BitMachineBankCodec.decode 12 input = some S) :
    decodeProducts (result input) =
      some (EncodedCommunication.bitsValue (S 3) *
          BitMachineBinaryMultiply.msbValue (S 4),
        EncodedCommunication.bitsValue (S 9) *
          BitMachineBinaryMultiply.msbValue (S 10)) := by
  simp [decodeProducts, result, BitMachineBankWrapper.result, h,
    resultBank, RationalProductCore.numerator_value,
    RationalProductCore.denominator_value]

theorem decode_packed_output (a b c d : List Bool) :
    decodeProducts (result (packedInput a b c d)) =
      some (EncodedCommunication.bitsValue a *
          BitMachineBinaryMultiply.msbValue c,
        EncodedCommunication.bitsValue b *
          BitMachineBinaryMultiply.msbValue d) := by
  have h : BitMachineBankCodec.decode 12 (packedInput a b c d) =
      some (inputBank a b c d) := by simp [packedInput]
  simpa [inputBank, firstBank, BitMachineBinaryMultiply.initialBank,
    BitMachineBinaryMultiply.finBank, BitMachineBinaryMultiply.finStack,
    BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank,
    firstStacks, finSumFinEquiv, Fin.addCases,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]
    using decode_result (packedInput a b c d) (inputBank a b c d) h

theorem decode_denominator_pos (a b c d : List Bool)
    (hb : 0 < EncodedCommunication.bitsValue b)
    (hd : 0 < BitMachineBinaryMultiply.msbValue d) :
    ∃ numerator denominator,
      decodeProducts (result (packedInput a b c d)) =
        some (numerator, denominator) ∧ 0 < denominator := by
  refine ⟨EncodedCommunication.bitsValue a *
      BitMachineBinaryMultiply.msbValue c,
    EncodedCommunication.bitsValue b *
      BitMachineBinaryMultiply.msbValue d, decode_packed_output a b c d, ?_⟩
  exact Nat.mul_pos hb hd

theorem malformed_result (input : List Bool)
    (h : BitMachineBankCodec.decode 12 input = none) :
    result input = [] := by
  simp [result, BitMachineBankWrapper.result, h]

end EthInapproximability.CurrentPaper.RationalProductPacket
