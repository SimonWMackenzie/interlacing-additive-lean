import CurrentAdditive.RationalSubtractClock
import CurrentAdditive.RationalProductRawRat

namespace EthInapproximability.CurrentPaper.RationalSubtractSpec

open Turing BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.CodeDCodec
open RationalSubtractCore

def crossInput (a b : RawRat) : Fin 12 → List Bool :=
  RationalProductCore.inputBank a.numerator b.numerator
    b.denominator a.denominator

def denominatorInput (a b : RawRat) : Fin 12 → List Bool :=
  RationalProductCore.inputBank a.denominator.reverse [] b.denominator []

def canonicalBank (a b : RawRat) : Bank := fun i =>
  if i = 3 then a.numerator else
  if i = 4 then b.denominator else
  if i = 9 then b.numerator else
  if i = 10 then a.denominator else
  if i = 15 then a.denominator.reverse else
  if i = 16 then b.denominator else
  if i = 24 then (if a.negative then [true] else []) else
  if i = 25 then (if b.negative then [true] else []) else []

def canonicalPacket (a b : RawRat) : List Bool :=
  BitMachineBankCodec.encode (canonicalBank a b)

theorem cross_input (a b : RawRat) :
    restricted crossSlots (canonicalBank a b) = crossInput a b := by
  funext i
  fin_cases i <;> simp [restricted, crossSlots, canonicalBank,
    crossInput, RationalProductCore.inputBank,
    RationalProductCore.firstBank,
    BitMachineBinaryMultiply.initialBank,
    BitMachineBinaryMultiply.finBank,
    BitMachineBinaryMultiply.finStack,
    BitMachineBinaryMultiply.cfg,
    BitMachineBinaryMultiply.rightBank,
    RationalProductCore.firstStacks, finSumFinEquiv, Fin.addCases,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]

theorem denominator_input (a b : RawRat) :
    restricted denSlots (crossBank (canonicalBank a b)) =
      denominatorInput a b := by
  funext i
  have ho : crossBank (canonicalBank a b) (denSlots i) =
      canonicalBank a b (denSlots i) := by
    exact bank_outside crossSlots (canonicalBank a b)
      (RationalProductPacket.resultBank
        (restricted crossSlots (canonicalBank a b))) (denSlots i)
        (by fin_cases i <;> decide)
  rw [show restricted denSlots (crossBank (canonicalBank a b)) i =
    crossBank (canonicalBank a b) (denSlots i) from rfl, ho]
  fin_cases i <;> simp [denSlots,
    canonicalBank, denominatorInput,
    RationalProductCore.inputBank,
    RationalProductCore.firstBank,
    BitMachineBinaryMultiply.initialBank,
    BitMachineBinaryMultiply.finBank,
    BitMachineBinaryMultiply.finStack,
    BitMachineBinaryMultiply.cfg,
    BitMachineBinaryMultiply.rightBank,
    RationalProductCore.firstStacks, finSumFinEquiv, Fin.addCases,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]

private theorem den_preserves (S : Bank) (j : Fin 32)
    (hj : ¬ ∃ i : Fin 12, denSlots i = j) : denBank S j = S j := by
  exact bank_outside denSlots S
    (RationalProductPacket.resultBank (restricted denSlots S)) j hj

private theorem cross_preserves (S : Bank) (j : Fin 32)
    (hj : ¬ ∃ i : Fin 12, crossSlots i = j) : crossBank S j = S j := by
  exact bank_outside crossSlots S
    (RationalProductPacket.resultBank (restricted crossSlots S)) j hj

theorem cross_numerator_a (a b : RawRat) :
    productBank (canonicalBank a b) 0 =
      RationalProductPacket.resultBank (crossInput a b) 0 := by
  rw [productBank, den_preserves _ 0 (by decide)]
  exact (bank_at crossSlots (canonicalBank a b)
    (RationalProductPacket.resultBank
      (restricted crossSlots (canonicalBank a b))) 0).trans
    (by rw [cross_input])

theorem cross_numerator_b (a b : RawRat) :
    productBank (canonicalBank a b) 6 =
      RationalProductPacket.resultBank (crossInput a b) 6 := by
  rw [productBank, den_preserves _ 6 (by decide)]
  exact (bank_at crossSlots (canonicalBank a b)
    (RationalProductPacket.resultBank
      (restricted crossSlots (canonicalBank a b))) 6).trans
    (by rw [cross_input])

theorem denominator_product (a b : RawRat) :
    productBank (canonicalBank a b) 12 =
      RationalProductPacket.resultBank (denominatorInput a b) 0 := by
  rw [productBank, denBank, show (12 : Fin 32) = denSlots 0 from rfl,
    bank_at, denominator_input]

theorem product_sign_a (a b : RawRat) :
    productBank (canonicalBank a b) 24 =
      (if a.negative then [true] else []) := by
  rw [productBank, den_preserves _ 24 (by decide),
    cross_preserves _ 24 (by decide)]
  simp [canonicalBank]

theorem product_sign_b (a b : RawRat) :
    productBank (canonicalBank a b) 25 =
      (if b.negative then [true] else []) := by
  rw [productBank, den_preserves _ 25 (by decide),
    cross_preserves _ 25 (by decide)]
  simp [canonicalBank]

theorem product_scratch (a b : RawRat) (j : Fin 32) (hj : 27 ≤ j.val) :
    productBank (canonicalBank a b) j = [] := by
  have hd : ¬ ∃ i : Fin 12, denSlots i = j := by
    intro ⟨i, hi⟩
    fin_cases i <;> simp [denSlots] at hi <;> omega
  have hc : ¬ ∃ i : Fin 12, crossSlots i = j := by
    intro ⟨i, hi⟩
    fin_cases i <;> simp [crossSlots] at hi <;> omega
  rw [productBank, den_preserves _ j hd, cross_preserves _ j hc]
  fin_cases j <;> simp [canonicalBank] at *

theorem sub_input_canonical (a b : RawRat) :
    subInput (productBank (canonicalBank a b)) =
      SignedMagnitudeSubtract.canonicalInput a.negative b.negative
        (RationalProductPacket.resultBank (crossInput a b) 0)
        (RationalProductPacket.resultBank (crossInput a b) 6) := by
  funext i
  fin_cases i
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_sign_a a b
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_sign_b a b
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using cross_numerator_a a b
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using cross_numerator_b a b
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_scratch a b 27 (by decide)
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_scratch a b 28 (by decide)
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_scratch a b 29 (by decide)
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_scratch a b 30 (by decide)
  · simpa [subInput, subSlots, SignedMagnitudeSubtract.canonicalInput,
      SignedMagnitudeSubtract.contents] using product_scratch a b 31 (by decide)

noncomputable def outputRat (a b : RawRat) : RawRat :=
  let S := finalBank (canonicalBank a b)
  ⟨!((S 30).isEmpty), S 31, (S 12).reverse⟩

theorem output_sign (a b : RawRat) :
    (outputRat a b).negative =
      !((SignedMagnitudeSubtract.finalBank
        (subInput (productBank (canonicalBank a b))) 7).isEmpty) := by
  have h := bank_at subSlots (productBank (canonicalBank a b))
    (SignedMagnitudeSubtract.finalBank
      (subInput (productBank (canonicalBank a b)))) 7
  have hs := congrArg (fun w : List Bool => !w.isEmpty) h
  simpa only [outputRat, finalBank, subSlots] using hs

theorem output_numerator (a b : RawRat) :
    (outputRat a b).numerator =
      SignedMagnitudeSubtract.finalBank
        (subInput (productBank (canonicalBank a b))) 8 := by
  have h := bank_at subSlots (productBank (canonicalBank a b))
    (SignedMagnitudeSubtract.finalBank
      (subInput (productBank (canonicalBank a b)))) 8
  simpa only [outputRat, finalBank, subSlots] using h

theorem output_denominator (a b : RawRat) :
    (outputRat a b).denominator =
      (RationalProductPacket.resultBank (denominatorInput a b) 0).reverse := by
  change (finalBank (canonicalBank a b) 12).reverse = _
  rw [finalBank,
    bank_outside subSlots (productBank (canonicalBank a b))
      (SignedMagnitudeSubtract.finalBank
        (subInput (productBank (canonicalBank a b)))) 12 (by decide),
    denominator_product]

theorem cross_a_value (a b : RawRat) :
    EncodedCommunication.bitsValue
      (RationalProductPacket.resultBank (crossInput a b) 0) =
      EncodedCommunication.bitsValue a.numerator *
        BitMachineBinaryMultiply.msbValue b.denominator := by
  exact RationalProductCore.numerator_value _ _ _ _

theorem cross_b_value (a b : RawRat) :
    EncodedCommunication.bitsValue
      (RationalProductPacket.resultBank (crossInput a b) 6) =
      EncodedCommunication.bitsValue b.numerator *
        BitMachineBinaryMultiply.msbValue a.denominator := by
  exact RationalProductCore.denominator_value _ _ _ _

theorem denominator_value (a b : RawRat) :
    BitMachineBinaryMultiply.msbValue (outputRat a b).denominator =
      BitMachineBinaryMultiply.msbValue a.denominator *
        BitMachineBinaryMultiply.msbValue b.denominator := by
  rw [output_denominator, RationalProductAdapter.msbValue_reverse]
  change EncodedCommunication.bitsValue
    (RationalProductCore.outputBank a.denominator.reverse [] b.denominator [] 0) = _
  rw [RationalProductCore.numerator_value,
    RationalProductRawRat.bitsValue_reverse]

theorem output_valid (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    (outputRat a b).Valid := by
  simpa [RawRat.Valid, denominator_value] using Nat.mul_pos ha hb

theorem signed_output (a b : RawRat) :
    SignedMagnitudeSubtract.signedValue (outputRat a b).negative
      (outputRat a b).numerator =
    SignedMagnitudeSubtract.signedValue a.negative
      (RationalProductPacket.resultBank (crossInput a b) 0) -
    SignedMagnitudeSubtract.signedValue b.negative
      (RationalProductPacket.resultBank (crossInput a b) 6) := by
  rw [output_sign, output_numerator, sub_input_canonical]
  simpa only using SignedMagnitudeSubtract.canonical_output_value a.negative
    b.negative
    (RationalProductPacket.resultBank (crossInput a b) 0)
    (RationalProductPacket.resultBank (crossInput a b) 6)

private theorem raw_value_signed (r : RawRat) :
    r.value =
      (SignedMagnitudeSubtract.signedValue r.negative r.numerator : ℚ) /
        (BitMachineBinaryMultiply.msbValue r.denominator : ℚ) := by
  cases r with
  | mk sign numerator denominator =>
      cases sign <;>
        simp [RawRat.value, SignedMagnitudeSubtract.signedValue] <;> ring

private theorem cross_a_signed (a b : RawRat) :
    SignedMagnitudeSubtract.signedValue a.negative
      (RationalProductPacket.resultBank (crossInput a b) 0) =
    SignedMagnitudeSubtract.signedValue a.negative a.numerator *
      (BitMachineBinaryMultiply.msbValue b.denominator : ℤ) := by
  cases a with
  | mk sign numerator denominator =>
      cases sign <;>
        simp [SignedMagnitudeSubtract.signedValue, cross_a_value, Nat.cast_mul]

private theorem cross_b_signed (a b : RawRat) :
    SignedMagnitudeSubtract.signedValue b.negative
      (RationalProductPacket.resultBank (crossInput a b) 6) =
    SignedMagnitudeSubtract.signedValue b.negative b.numerator *
      (BitMachineBinaryMultiply.msbValue a.denominator : ℤ) := by
  cases b with
  | mk sign numerator denominator =>
      cases sign <;>
        simp [SignedMagnitudeSubtract.signedValue, cross_b_value, Nat.cast_mul]

theorem output_value (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    (outputRat a b).value = a.value - b.value := by
  let da := BitMachineBinaryMultiply.msbValue a.denominator
  let db := BitMachineBinaryMultiply.msbValue b.denominator
  let na := SignedMagnitudeSubtract.signedValue a.negative a.numerator
  let nb := SignedMagnitudeSubtract.signedValue b.negative b.numerator
  have hnum : SignedMagnitudeSubtract.signedValue
      (outputRat a b).negative (outputRat a b).numerator =
      na * (db : ℤ) - nb * (da : ℤ) := by
    rw [signed_output, cross_a_signed, cross_b_signed]
  have hrat : (SignedMagnitudeSubtract.signedValue
      (outputRat a b).negative (outputRat a b).numerator : ℚ) =
      (na : ℚ) * (db : ℚ) - (nb : ℚ) * (da : ℚ) := by
    exact_mod_cast hnum
  have hden : (outputRat a b).value =
      (SignedMagnitudeSubtract.signedValue
        (outputRat a b).negative (outputRat a b).numerator : ℚ) /
        ((da : ℚ) * (db : ℚ)) := by
    rw [raw_value_signed, denominator_value]
    norm_cast
  have ha' : (da : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb' : (db : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  rw [hden, hrat, raw_value_signed a, raw_value_signed b]
  change ((na : ℚ) * (db : ℚ) - (nb : ℚ) * (da : ℚ)) /
      ((da : ℚ) * (db : ℚ)) =
      (na : ℚ) / (da : ℚ) - (nb : ℚ) / (db : ℚ)
  field_simp [ha', hb']

def decodeResultRat (packet : List Bool) : Option RawRat := do
  let S ← BitMachineBankCodec.decode 32 packet
  let r : RawRat := ⟨!((S 30).isEmpty), S 31, (S 12).reverse⟩
  if BitMachineBinaryMultiply.msbValue r.denominator = 0 then none else some r

theorem canonical_result (a b : RawRat) :
    RationalSubtractClock.result (canonicalPacket a b) =
      BitMachineBankCodec.encode (finalBank (canonicalBank a b)) := by
  simp [RationalSubtractClock.result, BitMachineBankWrapper.result,
    canonicalPacket]

theorem canonical_decoded (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    decodeResultRat (RationalSubtractClock.result (canonicalPacket a b)) =
      some (outputRat a b) := by
  have hp := output_valid a b ha hb
  have hn : BitMachineBinaryMultiply.msbValue (outputRat a b).denominator ≠ 0 :=
    Nat.ne_of_gt hp
  rw [canonical_result]
  simp only [decodeResultRat, BitMachineBankCodec.decode_encode]
  change (if BitMachineBinaryMultiply.msbValue (outputRat a b).denominator = 0
    then none else some (outputRat a b)) = some (outputRat a b)
  simp [hn]

theorem canonical_exact_subtract (a b : RawRat) (ha : a.Valid)
    (hb : b.Valid) :
    ∃ r, decodeResultRat
      (RationalSubtractClock.result (canonicalPacket a b)) = some r ∧
      r.Valid ∧ r.value = a.value - b.value := by
  exact ⟨outputRat a b, canonical_decoded a b ha hb,
    output_valid a b ha hb, output_value a b ha hb⟩

theorem canonical_machine_outputs (a b : RawRat) :
    RationalSubtractClock.machine.OutputsWithin (canonicalPacket a b)
      (RationalSubtractClock.result (canonicalPacket a b))
      (65*((canonicalPacket a b).length+1) +
        100000000000000*((canonicalPacket a b).length+1)^2 +
        2*(150000000000000*((canonicalPacket a b).length+1)) + 4) := by
  apply BitMachineBankWrapper.outputs program start initial finalBank
    (canonicalPacket a b)
    (100000000000000*((canonicalPacket a b).length+1)^2)
    (150000000000000*((canonicalPacket a b).length+1))
  · intro S hd
    obtain ⟨t, ht, hr⟩ := RationalSubtractCore.local_run S
    refine ⟨t, ⟨none, initial, finalBank S⟩, ?_, hr, rfl, rfl⟩
    have he := BitMachineBankCodec.encode_decode hd
    rw [← he]
    exact ht.trans (RationalSubtractClock.local_time_bound S)
  · intro S hd
    have he := BitMachineBankCodec.encode_decode hd
    rw [← he]
    exact RationalSubtractClock.final_size S

#print axioms RationalSubtractClock.polytime
#print axioms canonical_machine_outputs
#print axioms canonical_exact_subtract

end EthInapproximability.CurrentPaper.RationalSubtractSpec
