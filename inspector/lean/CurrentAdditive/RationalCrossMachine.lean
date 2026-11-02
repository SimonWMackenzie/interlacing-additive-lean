import CurrentAdditive.UnsignedComparePacket
import CurrentAdditive.RationalProductAdapter
import CurrentAdditive.RationalCrossCompare
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
One fixed physical program: product two operand pairs, then compare the two
unreduced products in banks 0 and 6. The comparator uses bank 2 as scratch.
-/

namespace EthInapproximability.CurrentPaper.RationalCrossMachine

open Turing BitMachineEncoding
open BitMachineStackEmbedding

def slots : Fin 3 ↪ Fin 12 := ⟨![0,6,2], by decide⟩

def unsignedProgram : UnsignedCompare.Label →
    TM2.Stmt (fun _ : Fin 12 => Bool) UnsignedCompare.Label UnsignedCompare.Control :=
  fun l => stackStmt slots (UnsignedCompare.program l)

abbrev Label := BitMachineRawSequence.Label
  RationalProductPacket.Label UnsignedCompare.Label
abbrev Control := RationalProductPacket.Control × UnsignedCompare.Control

def start : Label := BitMachineRawSequence.leftLabel (.inr 0)
def initial : Control := (RationalProductPacket.initial, UnsignedCompare.initial)

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Control :=
  BitMachineRawSequence.program RationalProductPacket.program
    unsignedProgram .scan RationalProductPacket.initial UnsignedCompare.initial

def productBank (S : Fin 12 → List Bool) : Fin 12 → List Bool :=
  RationalProductPacket.resultBank S

def inputToCompare (S : Fin 12 → List Bool) : Fin 3 → List Bool :=
  fun k => productBank S (slots k)

noncomputable def finalBank (S : Fin 12 → List Bool) : Fin 12 → List Bool :=
  bank slots (productBank S)
    (UnsignedCompare.bank
      ((inputToCompare S 2).reverse ++
        (BitMachineBinaryDivision.subAny
          (inputToCompare S 0) (inputToCompare S 1) false).1)
      [(BitMachineBinaryDivision.subAny
        (inputToCompare S 0) (inputToCompare S 1) false).2] [])

theorem unsigned_run (S : Fin 12 → List Bool) :
    ((advance unsignedProgram)^[2 * max (inputToCompare S 0).length
        (inputToCompare S 1).length + (inputToCompare S 2).length + 2])
      (⟨some UnsignedCompare.Label.scan, UnsignedCompare.initial, productBank S⟩ :
        TM2.Cfg (fun _ : Fin 12 => Bool) UnsignedCompare.Label UnsignedCompare.Control) =
      ⟨none, UnsignedCompare.initial, finalBank S⟩ := by
  have h := UnsignedCompare.scan_correct
    (inputToCompare S 0) (inputToCompare S 1) false (inputToCompare S 2)
  have hbank : UnsignedCompare.bank (inputToCompare S 0)
      (inputToCompare S 1) (inputToCompare S 2) = inputToCompare S := by
    funext k; fin_cases k <;> rfl
  rw [UnsignedCompare.run, UnsignedCompare.cfg, hbank] at h
  have he := BitMachineStackRun.run slots (productBank S)
    UnsignedCompare.program
    (⟨some UnsignedCompare.Label.scan, UnsignedCompare.initial,
      inputToCompare S⟩ :
      TM2.Cfg (fun _ : Fin 3 => Bool) UnsignedCompare.Label UnsignedCompare.Control)
    (2 * max (inputToCompare S 0).length (inputToCompare S 1).length +
      (inputToCompare S 2).length + 2)
  have he' := he.trans
    (congrArg (BitMachineStackEmbedding.stackCfg slots (productBank S)) h)
  have hstart : bank slots (productBank S) (inputToCompare S) =
      productBank S := by
    simpa only [inputToCompare] using bank_restrict slots (productBank S)
  rw [show BitMachineStackEmbedding.stackCfg slots (productBank S)
      (⟨some UnsignedCompare.Label.scan, UnsignedCompare.initial,
        inputToCompare S⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) UnsignedCompare.Label UnsignedCompare.Control) =
      ⟨some UnsignedCompare.Label.scan, UnsignedCompare.initial, productBank S⟩ from by
      simp [BitMachineStackEmbedding.stackCfg, hstart]] at he'
  simpa only [unsignedProgram, BitMachineStackEmbedding.stackCfg,
    finalBank,
    UnsignedCompare.cfg] using he'

theorem local_run (S : Fin 12 → List Bool) :
    ∃ t ≤ RationalProductPacket.clearTime S + RationalProductPacket.rawTime S +
        (2 * max (inputToCompare S 0).length (inputToCompare S 1).length +
          (inputToCompare S 2).length + 2) + 1,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ :
          TM2.Cfg (fun _ : Fin 12 => Bool) Label Control) =
        ⟨none, initial, finalBank S⟩ := by
  obtain ⟨tp, htp, hp⟩ := RationalProductPacket.local_run S
  have hc := unsigned_run S
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    RationalProductPacket.program unsignedProgram
    (.inr (0 : Fin 9)) .scan RationalProductPacket.initial
    RationalProductPacket.initial UnsignedCompare.initial
    UnsignedCompare.initial S (productBank S) (finalBank S) tp
    (2 * max (inputToCompare S 0).length
      (inputToCompare S 1).length + (inputToCompare S 2).length + 2)
    hp hc
  refine ⟨t, by omega, ?_⟩
  simpa only [program, start, initial] using hr

theorem compare_time_bound (S : Fin 12 → List Bool) :
    2 * max (inputToCompare S 0).length (inputToCompare S 1).length +
      (inputToCompare S 2).length + 2 ≤
      3 * ((BitMachineBankCodec.encode (productBank S)).length + 1) := by
  have h0 := BitMachineBankCodec.word_length_le_encode
    (productBank S) (slots 0)
  have h1 := BitMachineBankCodec.word_length_le_encode
    (productBank S) (slots 1)
  have h2 := BitMachineBankCodec.word_length_le_encode
    (productBank S) (slots 2)
  dsimp only [inputToCompare]
  omega

theorem output_word_bound (S : Fin 12 → List Bool) (j : Fin 12) :
    (finalBank S j).length ≤
      2 * (BitMachineBankCodec.encode (productBank S)).length + 1 := by
  let n := (BitMachineBankCodec.encode (productBank S)).length
  have h0 := BitMachineBankCodec.word_length_le_encode
    (productBank S) (slots 0)
  have h1 := BitMachineBankCodec.word_length_le_encode
    (productBank S) (slots 1)
  have h2 := BitMachineBankCodec.word_length_le_encode
    (productBank S) (slots 2)
  have hl := BitMachineBinaryDivision.subAny_length
    (inputToCompare S 0) (inputToCompare S 1) false
  by_cases hj : ∃ k : Fin 3, slots k = j
  · obtain ⟨k, rfl⟩ := hj
    fin_cases k
    · have he : (finalBank S (slots 0)).length =
          (inputToCompare S 2).length +
            max (inputToCompare S 0).length
              (inputToCompare S 1).length := by
        simp [finalBank, bank_at, UnsignedCompare.bank,
          BitMachineBinaryDivision.subAny_length]
      change (finalBank S (slots 0)).length ≤
        2 * (BitMachineBankCodec.encode (productBank S)).length + 1
      rw [he]
      dsimp only [inputToCompare] at *
      omega
    · simp [finalBank, bank_at, UnsignedCompare.bank]
    · simp [finalBank, bank_at, UnsignedCompare.bank]
  · rw [finalBank, bank_outside slots (productBank S) _ j hj]
    have h := BitMachineBankCodec.word_length_le_encode (productBank S) j
    omega

theorem output_size_bound (S : Fin 12 → List Bool) :
    (BitMachineBankCodec.encode (finalBank S)).length ≤
      50 * ((BitMachineBankCodec.encode (productBank S)).length + 1) := by
  let n := (BitMachineBankCodec.encode (productBank S)).length
  have hs : (∑ j : Fin 12, (finalBank S j).length) ≤
      ∑ _j : Fin 12, (2*n+1) :=
    Finset.sum_le_sum (by intro j _; exact output_word_bound S j)
  rw [BitMachineBankCodec.encode_length]
  simp at hs
  omega

theorem time_bound (S : Fin 12 → List Bool) :
    RationalProductPacket.clearTime S + RationalProductPacket.rawTime S +
      (2 * max (inputToCompare S 0).length
        (inputToCompare S 1).length + (inputToCompare S 2).length + 2) + 1 ≤
      200 * ((BitMachineBankCodec.encode S).length + 1) ^ 2 := by
  let n := (BitMachineBankCodec.encode S).length
  let p := (BitMachineBankCodec.encode (productBank S)).length
  have hp := RationalProductPacket.size_bound S
  have ht := RationalProductPacket.time_bound S
  have hc := compare_time_bound S
  dsimp only [productBank] at hp hc
  have hn : 1 ≤ n + 1 := by omega
  have hlin : n + 1 ≤ (n + 1) ^ 2 := by
    nlinarith
  nlinarith

theorem size_bound (S : Fin 12 → List Bool) :
    (BitMachineBankCodec.encode (finalBank S)).length ≤
      1100 * ((BitMachineBankCodec.encode S).length + 1) := by
  have hp := RationalProductPacket.size_bound S
  have ho := output_size_bound S
  dsimp only [productBank] at ho
  omega

noncomputable def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result finalBank input

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program start initial

theorem polytime : BitMachine.Polytime result := by
  apply BitMachineBankWrapper.polytime program start initial finalBank 200 2 1100 1
  · intro S
    obtain ⟨t, ht, hr⟩ := local_run S
    refine ⟨t, ⟨none, initial, finalBank S⟩, ht.trans (time_bound S), hr, rfl, rfl⟩
  · intro S
    simpa using size_bound S

def canonicalBank (words : Fin 4 → List Bool) : Fin 12 → List Bool :=
  RationalProductCore.inputBank
    (words 0) (words 1) (words 2).reverse (words 3).reverse

def decodeBorrow (output : List Bool) : Option Bool := do
  let S ← BitMachineBankCodec.decode 12 output
  match S 6 with
  | [v] => some v
  | _ => none

theorem canonical_input (words : Fin 4 → List Bool) :
    BitMachineBankCodec.decode 12 (RationalProductAdapter.physicalInput words) =
      some (canonicalBank words) := by
  simp [RationalProductAdapter.physicalInput,
    RationalProductPacket.packedInput, canonicalBank]

theorem canonical_output (words : Fin 4 → List Bool) :
    result (RationalProductAdapter.physicalInput words) =
      BitMachineBankCodec.encode (finalBank (canonicalBank words)) := by
  simp [result, BitMachineBankWrapper.result, canonical_input]

theorem borrow_from_products (S : Fin 12 → List Bool) :
    (finalBank S 6) =
      [decide (EncodedCommunication.bitsValue (productBank S 0) <
        EncodedCommunication.bitsValue (productBank S 6))] := by
  have h := (BitMachineBinaryDivision.subAny_spec
    (productBank S 0) (productBank S 6)).1
  change finalBank S (slots 1) = _
  rw [finalBank, bank_at]
  simpa [UnsignedCompare.bank, inputToCompare, slots, h]

theorem canonical_borrow (words : Fin 4 → List Bool) :
    decodeBorrow (result (RationalProductAdapter.physicalInput words)) =
      some (decide (EncodedCommunication.bitsValue (words 0) *
          EncodedCommunication.bitsValue (words 2) <
        EncodedCommunication.bitsValue (words 1) *
          EncodedCommunication.bitsValue (words 3))) := by
  let S := canonicalBank words
  have hp := RationalProductAdapter.physical_output words
  have he : RationalProductPacket.result
      (RationalProductAdapter.physicalInput words) =
      BitMachineBankCodec.encode (productBank S) := by
    simp [RationalProductPacket.result, BitMachineBankWrapper.result,
      canonical_input, S, productBank]
  rw [he] at hp
  simp only [RationalProductPacket.decodeProducts,
    BitMachineBankCodec.decode_encode, Option.pure_def, Option.bind_some] at hp
  have hpair := Option.some.inj hp
  have hn := congrArg Prod.fst hpair
  have hd := congrArg Prod.snd hpair
  simp only at hn hd
  rw [canonical_output]
  simp only [decodeBorrow, BitMachineBankCodec.decode_encode]
  change (match finalBank (canonicalBank words) 6 with
    | [v] => some v
    | _ => none) = _
  rw [borrow_from_products]
  simpa only [S] using congrArg (fun p : ℕ × ℕ =>
    some (decide (p.1 < p.2))) hpair

noncomputable def rationalBorrow (a b : CurrentAdditive.CodeDCodec.RawRat) : Option Bool :=
  decodeBorrow (result (RationalCrossCompare.productInput a b))

theorem rationalBorrow_correct (a b : CurrentAdditive.CodeDCodec.RawRat) :
    rationalBorrow a b =
      some (decide (EncodedCommunication.bitsValue a.numerator *
          BitMachineBinaryMultiply.msbValue b.denominator <
        EncodedCommunication.bitsValue b.numerator *
          BitMachineBinaryMultiply.msbValue a.denominator)) := by
  have h := canonical_borrow (RationalCrossCompare.words a b)
  have hb := RationalProductAdapter.msbValue_reverse b.denominator.reverse
  have ha := RationalProductAdapter.msbValue_reverse a.denominator.reverse
  simp only [List.reverse_reverse] at hb ha
  simpa [rationalBorrow, RationalCrossCompare.productInput,
    RationalCrossCompare.words, RationalProductAdapter.fourWords,
    ← hb, ← ha] using h

theorem rationalBorrow_lt (a b : CurrentAdditive.CodeDCodec.RawRat)
    (ha : a.Valid) (hb : b.Valid)
    (hsa : a.negative = false) (hsb : b.negative = false) :
    rationalBorrow a b = some (decide (a.value < b.value)) := by
  rw [rationalBorrow_correct]
  have hc := RationalCrossCompare.crossBorrow_lt a b ha hb hsa hsb
  rw [RationalCrossCompare.crossBorrow_correct] at hc
  exact hc

#print axioms local_run
#print axioms polytime
#print axioms canonical_borrow
#print axioms rationalBorrow_lt

end EthInapproximability.CurrentPaper.RationalCrossMachine
