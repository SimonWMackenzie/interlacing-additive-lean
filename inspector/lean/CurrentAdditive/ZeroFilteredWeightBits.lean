import CurrentAdditive.TransientArithmetic
import CurrentAdditive.AppendIndexTrace
import CurrentAdditive.CodeDTargetV2

set_option maxHeartbeats 1000000

namespace CurrentAdditive.ZeroFilteredWeightBits

open SequentialCode SequentialSourceCode RationalBitBounds IntegerBitSupport
open LabelTrace IndependentSupport TransientArithmetic
open EthInapproximability.CurrentPaper

/-- Removing zero weights restricts the numerator map of the original
common denominator. It requires no new denominator multiplication. -/
theorem positiveLaw_commonDenominator {Y : Type*}
    (alphabet : Array (Y × ℚ)) (hmass : sourceMass alphabet = 1)
    (enc : CommonDenominator (fun i : Fin alphabet.size => alphabet[i].2)) :
    ∃ ea : CommonDenominator
        (fun i : Fin (positiveLaw alphabet).size => (positiveLaw alphabet)[i].2),
      ea.denominator = enc.denominator := by
  obtain ⟨trace, he, _⟩ := positiveLaw_trace_exact alphabet hmass
  refine ⟨{
    denominator := enc.denominator
    positive := enc.positive
    numerator := fun i => enc.numerator (trace i)
    represents := ?_
  }, rfl⟩
  intro i
  rw [he i]
  exact enc.represents (trace i)

private theorem denominator_bits_le_entry (entry : Nat × ℚ) :
    Nat.size entry.2.den ≤ (CodeDTargetV2.alphabetEntry entry).length := by
  have hsign : 0 ≤
      (if entry.2.num < 0 then [true] else ([] : List Bool)).length := by omega
  simp only [CodeDTargetV2.alphabetEntry,
    BitMachineBankCodec.encode_length, CodeDCodec.encodeRawRat]
  simp [CodeDCodec.rawRatBank, CodeDCanonicalSourceV2.rawOfRat,
    BitMachineBankCodec.encode_length, Fin.sum_univ_succ,
    Nat.size_eq_bits_len]
  omega

private theorem denominator_sum_le_payload (entries : List (Nat × ℚ)) :
    (entries.map (fun e => Nat.size e.2.den)).sum ≤
      SourceListEncoding.totalLength (entries.map CodeDTargetV2.alphabetEntry) := by
  induction entries with
  | nil => simp [SourceListEncoding.totalLength]
  | cons e entries ih =>
      have he := denominator_bits_le_entry e
      simp only [List.map_cons, List.sum_cons, SourceListEncoding.totalLength] at *
      omega

private theorem payload_add_one_le_encoded (items : List (List Bool)) :
    SourceListEncoding.totalLength items + 1 ≤
      (SourceListEncoding.encode items).length := by
  have hf : SourceListEncoding.totalLength items ≤
      (SourceListEncoding.fields items).length := by
    induction items with
    | nil => simp [SourceListEncoding.totalLength, SourceListEncoding.fields]
    | cons item items ih =>
        simp only [SourceListEncoding.totalLength, List.map_cons, List.sum_cons,
          SourceListEncoding.fields, List.length_append] at *
        omega
  have hn : 1 ≤ (EncodedCommunication.natField items.length).length := by
    simp [EncodedCommunication.natField, EncodedCommunication.field_length]
  simpa only [SourceListEncoding.encode, List.length_append] using
    (Nat.add_le_add hf hn).trans_eq (Nat.add_comm _ _)

/-- The original input's product denominator is charged to the literal V2
alphabet packet, including symbols subsequently removed for zero weight. -/
theorem inputLaw_denominator_le_alphabetBytes (alphabet : Array (Nat × ℚ)) :
    Nat.size (inputLawCommonDenominator
      (fun i : Fin alphabet.size => alphabet[i].2)).denominator ≤
      (CodeDTargetV2.alphabetBytes alphabet).length := by
  have hbits := inputLaw_denominator_bits
    (fun i : Fin alphabet.size => alphabet[i].2)
  have hsum := denominator_sum_le_payload alphabet.toList
  have hsum' : (∑ i : Fin alphabet.size, Nat.size alphabet[i].2.den) ≤
      SourceListEncoding.totalLength
        (alphabet.toList.map CodeDTargetV2.alphabetEntry) := by
    have heq : Array.ofFn (fun i : Fin alphabet.size => alphabet[i]) = alphabet :=
      Array.ofFn_getElem
    have hid : alphabet.toList = List.ofFn (fun i : Fin alphabet.size => alphabet[i]) :=
      (congrArg Array.toList heq).symm.trans Array.toList_ofFn
    simpa only [hid, List.map_ofFn, List.sum_ofFn] using hsum
  have hpacket := payload_add_one_le_encoded
    (alphabet.toList.map CodeDTargetV2.alphabetEntry)
  change Nat.size (inputLawCommonDenominator
    (fun i : Fin alphabet.size => alphabet[i].2)).denominator ≤
      (SourceListEncoding.encode
        (alphabet.toList.map CodeDTargetV2.alphabetEntry)).length
  exact hbits.trans ((Nat.add_le_add_right hsum' 1).trans hpacket)

/-- Uniform retained-weight budget up to Q stages, expressed in original
alphabet size and original input bytes. For fixed D this is polynomial. -/
def budget (D Q m L : Nat) : Nat :=
  let P := (1 + Q * m) ^ D
  Q * L + 4 * Q * m * P ^ 2 * Nat.size (P + 1) + 1

theorem budget_le_explicit_polynomial (D Q m L : Nat) :
    budget D Q m L ≤
      Q * L + 4 * Q * m * ((1 + Q * m) ^ D + 1) ^ 3 + 1 := by
  let P := (1 + Q * m) ^ D
  have hs : Nat.size (P + 1) ≤ P + 1 :=
    Nat.size_le.mpr (P + 1).lt_two_pow_self
  have hh : P ^ 2 * Nat.size (P + 1) ≤ (P + 1) ^ 3 := by
    have hb := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : P ≤ P + 1) 2) hs
    convert hb using 1 <;> ring
  have hscaled := Nat.mul_le_mul_left (4 * Q * m) hh
  dsimp [budget]
  dsimp [P] at *
  nlinarith

theorem sequentialPreprocessed_all_stage_denominators
    (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (Q : Nat) :
    ∀ q, q ≤ Q → ∀ out : Array ((Fin q → Nat) × ℚ),
      sequentialPreprocessed D alphabet q = some out →
      ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
        Nat.size enc.denominator ≤
          budget D Q alphabet.size (CodeDTargetV2.alphabetBytes alphabet).length ∧
        ∀ i : Fin out.size,
          Nat.size (enc.numerator i).natAbs ≤ Nat.size enc.denominator := by
  let original := inputLawCommonDenominator
    (fun i : Fin alphabet.size => alphabet[i].2)
  obtain ⟨ea, hea⟩ := positiveLaw_commonDenominator alphabet hmass original
  have hinput : Nat.size ea.denominator ≤
      (CodeDTargetV2.alphabetBytes alphabet).length := by
    rw [hea]
    exact inputLaw_denominator_le_alphabetBytes alphabet
  have hmass' : sourceMass (positiveLaw alphabet) = 1 := by
    rw [← (positiveLaw_mass_moments alphabet hnonneg
      (n := 0) (fun _ i => Fin.elim0 i)).1]
    exact hmass
  obtain ⟨trace, _, _⟩ := positiveLaw_trace_exact alphabet hmass
  have hsize : (positiveLaw alphabet).size ≤ alphabet.size := by
    simpa using Fintype.card_le_of_injective trace trace.injective
  intro q hq out hout
  obtain ⟨enc, hbits, hnum⟩ := sequentialIndependent_numerator_bits D
    (positiveLaw alphabet) (positiveLaw_positive alphabet) hmass' ea q out hout
  let M := (generatedFeatures q D ((positiveLaw alphabet).map Prod.fst)).size
  let P := (1 + Q * alphabet.size) ^ D
  have hM : M ≤ P := by
    have hh := SequentialDimensionPolynomialProduction.generatedFeatures_size_le_polynomial
      q D ((positiveLaw alphabet).map Prod.fst)
    have hbase : 1 + q * (positiveLaw alphabet).size ≤ 1 + Q * alphabet.size :=
      Nat.add_le_add_left (Nat.mul_le_mul hq hsize) 1
    have hh' : M ≤ (1 + q * (positiveLaw alphabet).size) ^ D := by
      simpa [M] using hh
    exact hh'.trans (Nat.pow_le_pow_left hbase D)
  have hscaled := Nat.mul_le_mul hq hinput
  have hterm : 4 * q * (positiveLaw alphabet).size * M ^ 2 * Nat.size (M + 1) ≤
      4 * Q * alphabet.size * P ^ 2 * Nat.size (P + 1) := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hq) hsize)
        (Nat.pow_le_pow_left hM 2)
    · exact Nat.size_le_size (by omega)
  refine ⟨enc, ?_, hnum⟩
  change Nat.size enc.denominator ≤
    Q * (CodeDTargetV2.alphabetBytes alphabet).length +
      4 * Q * alphabet.size * P ^ 2 * Nat.size (P + 1) + 1
  change Nat.size enc.denominator ≤
    q * Nat.size ea.denominator +
      4 * q * (positiveLaw alphabet).size * M ^ 2 * Nat.size (M + 1) + 1 at hbits
  omega

theorem sequentialPreprocessed_all_stage_weights
    (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) (Q q : Nat) (hq : q ≤ Q)
    (out : Array ((Fin q → Nat) × ℚ))
    (hout : sequentialPreprocessed D alphabet q = some out) :
    ∀ i : Fin out.size,
      Fits (budget D Q alphabet.size
        (CodeDTargetV2.alphabetBytes alphabet).length) out[i].2 := by
  obtain ⟨enc, hd, hnum⟩ := sequentialPreprocessed_all_stage_denominators
    D alphabet hnonneg hmass Q q hq out hout
  intro i
  exact fits_commonDenominator enc _ hd (fun j => (hnum j).trans hd) i

#print axioms inputLaw_denominator_le_alphabetBytes
#print axioms sequentialPreprocessed_all_stage_denominators
#print axioms sequentialPreprocessed_all_stage_weights

end CurrentAdditive.ZeroFilteredWeightBits
