import CurrentAdditive.RawRatCoreBytes
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import Mathlib.Tactic

/-! Explicit all-input polynomial clock for the physical thirteen-bank core. -/
namespace CurrentAdditive.RawRatCoreClock

set_option maxRecDepth 4096

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.CodeDCodec

def inputLength (r : RawRat) : Nat := (encodeRawRat r).length
def size (r : RawRat) : Nat := inputLength r + 1

theorem local_encoded_length (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatGCDStage.localBank r)).length =
      2 * (r.numerator.length + r.denominator.length) + 7 := by
  rw [BitMachineBankCodec.encode_length]
  simp [Fin.sum_univ_succ, RawRatGCDStage.localBank,
    RawRatGCDStage.location, RawRatPreparation.prepared,
    RawRatPreparation.afterNumReverse, RawRatPreparation.afterDenCopy,
    RawRatPreparation.afterNumCopy, RawRatPreparation.inputBank]

theorem input_length (r : RawRat) :
    inputLength r =
      2 * ((if r.negative then 1 else 0) + r.numerator.length +
        r.denominator.length) + 3 := by
  rw [inputLength, encodeRawRat, BitMachineBankCodec.encode_length]
  cases h : r.negative <;> simp [Fin.sum_univ_succ, rawRatBank, h] <;> omega

theorem words_le_size (r : RawRat) :
    r.numerator.length + r.denominator.length ≤ size r := by
  rw [size, input_length]
  omega

theorem local_clock_bound (r : RawRat) :
    RawRatGCDStage.localClock r ≤ 5000 * (size r + 4)^4 := by
  rw [RawRatGCDStage.localClock, local_encoded_length]
  have h := BinaryGCDPolytime.clock_polynomial
    (2 * (r.numerator.length + r.denominator.length) + 7)
  have hs := words_le_size r
  have hx : 2 * (r.numerator.length + r.denominator.length) + 8 ≤
      size r + 4 := by
    rw [size, input_length]
    omega
  exact h.trans (Nat.mul_le_mul_left 5000 (pow_le_pow_left₀ (by omega) hx 4))

theorem prepared_encoded_length (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatPreparation.prepared r)).length =
      4 * (r.numerator.length + r.denominator.length) +
        2 * (if r.negative then 1 else 0) + 13 := by
  rw [BitMachineBankCodec.encode_length]
  cases h : r.negative <;>
    simp [Fin.sum_univ_succ, RawRatPreparation.prepared,
      RawRatPreparation.afterNumReverse, RawRatPreparation.afterDenCopy,
      RawRatPreparation.afterNumCopy, RawRatPreparation.inputBank, h] <;> omega

theorem encoded_growth {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Fin 13 => Bool) L V)
    (c : TM2.Cfg (fun _ : Fin 13 => Bool) L V) (t : Nat) :
    (BitMachineBankCodec.encode (((advance P)^[t]) c).stk).length ≤
      (BitMachineBankCodec.encode c.stk).length +
        26 * BitMachineStackGrowth.perStep P * t := by
  have hsum :
      (∑ j : Fin 13, ((((advance P)^[t]) c).stk j).length) ≤
        (∑ j : Fin 13, (c.stk j).length) +
          13 * BitMachineStackGrowth.perStep P * t := by
    calc
      _ ≤ ∑ j : Fin 13,
          ((c.stk j).length + BitMachineStackGrowth.perStep P * t) := by
            exact Finset.sum_le_sum (by
              intro j _
              exact BitMachineStackGrowth.run_growth P c t j)
      _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_assoc]
  rw [BitMachineBankCodec.encode_length, BitMachineBankCodec.encode_length]
  have hmul : 26 * BitMachineStackGrowth.perStep P * t =
      2 * (13 * BitMachineStackGrowth.perStep P * t) := by ring
  rw [hmul]
  omega

theorem gcd_encoded_growth (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatGCDStage.result r)).length ≤
      (BitMachineBankCodec.encode (RawRatPreparation.prepared r)).length +
        26 * BitMachineStackGrowth.perStep RawRatGCDStage.program *
          RawRatGCDStage.localClock r := by
  obtain ⟨v, hv⟩ := RawRatGCDStage.run r
  have h := encoded_growth RawRatGCDStage.program
    (⟨some (BitMachineRawSequence.leftLabel (0 : Fin 7)),
      (((), none), BinaryGCDCore.initial), RawRatPreparation.prepared r⟩ :
      TM2.Cfg (fun _ : Fin 13 => Bool) _ _)
    (RawRatGCDStage.localClock r)
  rw [hv] at h
  exact h

theorem gcd_encoded_bound (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatGCDStage.result r)).length ≤
      3 * size r + 13 +
        26 * BitMachineStackGrowth.perStep RawRatGCDStage.program *
          RawRatGCDStage.localClock r := by
  have hg := gcd_encoded_growth r
  rw [prepared_encoded_length] at hg
  have hs := input_length r
  unfold size
  omega

theorem numerator_quotient_length (r : RawRat) :
    (RawRatNumeratorDivision.divided r 9).length = r.numerator.length := by
  change (BitMachineStackEmbedding.bank RawRatGCDStage.location
    (RawRatNumeratorDivision.dividendReady r)
    (BitMachineBinaryDivision.finalBank
      (RawRatNumeratorDivision.dividendReady r 3)
      (RawRatNumeratorDivision.dividendReady r 4))
      (RawRatGCDStage.location 3)).length = _
  rw [BitMachineStackEmbedding.bank_at]
  simpa [BitMachineBinaryDivision.finalBank, BitMachineBinaryDivision.bank,
    RawRatNumeratorDivision.ready_input] using
    (BitMachineBinaryDivision.divideFrom_quotient_length
      (RawRatNumeratorDivision.dividendReady r 3)
      (RawRatNumeratorDivision.dividendReady r 4) [] [])

theorem denominator_quotient_length (r : RawRat) :
    (RawRatDenominatorDivision.divided r 9).length = r.denominator.length := by
  change (BitMachineStackEmbedding.bank RawRatGCDStage.location
    (RawRatDenominatorDivision.dividendReady r)
    (BitMachineBinaryDivision.finalBank
      (RawRatDenominatorDivision.dividendReady r 3)
      (RawRatDenominatorDivision.dividendReady r 4))
      (RawRatGCDStage.location 3)).length = _
  rw [BitMachineStackEmbedding.bank_at]
  simpa [BitMachineBinaryDivision.finalBank, BitMachineBinaryDivision.bank,
    RawRatDenominatorDivision.ready_input] using
    (BitMachineBinaryDivision.divideFrom_quotient_length
      (RawRatDenominatorDivision.dividendReady r 3)
      (RawRatDenominatorDivision.dividendReady r 4) [] [])

theorem canonical_first_clock_bound (r : RawRat) :
    RawRatCanonEmbedded.clock RawRatNumeratorCanonical.location
        (RawRatNumeratorDivision.divided r) ≤ 2 * r.numerator.length + 2 := by
  have h := RawRatCanonEmbedded.clock_linear RawRatNumeratorCanonical.location
    (RawRatNumeratorDivision.divided r)
  simpa [RawRatNumeratorCanonical.location, numerator_quotient_length] using h

theorem canonical_second_clock_bound (r : RawRat) :
    RawRatCanonEmbedded.clock RawRatDenominatorCanonical.location
        (RawRatDenominatorDivision.divided r) ≤ 2 * r.denominator.length + 2 := by
  have h := RawRatCanonEmbedded.clock_linear RawRatDenominatorCanonical.location
    (RawRatDenominatorDivision.divided r)
  simpa [RawRatDenominatorCanonical.location, denominator_quotient_length] using h

theorem input_bank_encoded_length (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatPreparation.inputBank r)).length =
      inputLength r + 10 := by
  rw [input_length, BitMachineBankCodec.encode_length]
  cases h : r.negative <;>
    simp [Fin.sum_univ_succ, RawRatPreparation.inputBank, h] <;> omega

theorem first_encoded_growth (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatNumeratorCanonical.result r)).length ≤
      inputLength r + 10 +
        26 * BitMachineStackGrowth.perStep
          RawRatFirstQuotientController.program *
          RawRatFirstQuotientController.clock r := by
  obtain ⟨t, ht, hv⟩ := RawRatFirstQuotientController.run r
  have h := encoded_growth RawRatFirstQuotientController.program
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
      RawRatCoreController.firstInitial, RawRatPreparation.inputBank r⟩ :
      TM2.Cfg (fun _ : Fin 13 => Bool) _ _)
    t
  dsimp [RawRatCoreController.firstInitial] at h
  rw [hv, input_bank_encoded_length] at h
  have h' : (BitMachineBankCodec.encode
      (RawRatNumeratorCanonical.result r)).length ≤
      inputLength r + 10 +
        26 * BitMachineStackGrowth.perStep
          RawRatFirstQuotientController.program * t := by
    simpa only using h
  have hh := Nat.mul_le_mul_left
    (26 * BitMachineStackGrowth.perStep RawRatFirstQuotientController.program) ht
  omega

theorem trim_length_le (w : List Bool) :
    (BitMachineTrimLeadingZeros.trim w).length ≤ w.length := by
  induction w with
  | nil => simp [BitMachineTrimLeadingZeros.trim]
  | cons b bs ih => cases b <;> simp [BitMachineTrimLeadingZeros.trim] <;> omega

theorem canonical_denominator_length (r : RawRat) :
    (RawRatDenominatorCanonical.canonicalLE r 2).length ≤
      r.denominator.length := by
  rw [RawRatDenominatorCanonical.canonicalLE,
    RawRatCanonEmbedded.result]
  change (BitMachineStackEmbedding.bank RawRatDenominatorCanonical.location
    (RawRatDenominatorDivision.divided r)
    (![[], [], BG34Canon.canon
      (RawRatDenominatorDivision.divided r 9)] : Fin 3 → List Bool)
    (RawRatDenominatorCanonical.location 2)).length ≤ _
  rw [BitMachineStackEmbedding.bank_at]
  change (BG34Canon.canon
    (RawRatDenominatorDivision.divided r 9)).length ≤ _
  unfold BG34Canon.canon
  simp only [List.length_reverse]
  exact (trim_length_le _).trans (by simp [denominator_quotient_length])

theorem canonical_sign_length (r : RawRat) :
    (RawRatDenominatorCanonical.result r 0).length ≤ 1 := by
  rw [RawRatCoreBytes.denominator_sign]
  cases r.negative <;> simp

def gcdTimeBound (r : RawRat) : Nat := 5000 * (size r + 4)^4

def gcdSizeBound (r : RawRat) : Nat :=
  3 * size r + 13 +
    26 * BitMachineStackGrowth.perStep RawRatGCDStage.program * gcdTimeBound r

def divisionTimeBound (r : RawRat) : Nat :=
  size r * (4 * (size r + gcdSizeBound r + 1) + 5) + 1

def firstTimeBound (r : RawRat) : Nat :=
  gcdTimeBound r + 6 * gcdSizeBound r + divisionTimeBound r +
    6 * size r + 25

def secondTimeBound (r : RawRat) : Nat :=
  6 * (size r + 10 +
    26 * BitMachineStackGrowth.perStep
      RawRatFirstQuotientController.program * firstTimeBound r) +
    divisionTimeBound r + 5 * size r + 50

def totalTimeBound (r : RawRat) : Nat :=
  firstTimeBound r + secondTimeBound r + 1

theorem gcd_size_bound (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatGCDStage.result r)).length ≤
      gcdSizeBound r := by
  have hg := gcd_encoded_bound r
  have ht := local_clock_bound r
  have hm := Nat.mul_le_mul_left
    (26 * BitMachineStackGrowth.perStep RawRatGCDStage.program) ht
  unfold gcdSizeBound gcdTimeBound
  omega

theorem divisor_length_bound (r : RawRat) :
    (RawRatGCDStage.result r 4).length ≤ gcdSizeBound r :=
  (BitMachineBankCodec.word_length_le_encode _ 4).trans (gcd_size_bound r)

theorem first_division_clock_bound (r : RawRat) :
    RawRatDivisionEmbedded.clock (RawRatNumeratorDivision.dividendReady r) ≤
      divisionTimeBound r := by
  have h := RawRatDivisionEmbedded.clock_bound
    (RawRatNumeratorDivision.dividendReady r)
  rw [RawRatNumeratorDivision.ready_input,
    RawRatNumeratorDivision.ready_divisor] at h
  simp only [List.length_reverse] at h
  have hn := words_le_size r
  have hg := divisor_length_bound r
  unfold divisionTimeBound
  calc
    _ ≤ r.numerator.length *
        (4 * (r.numerator.length + (RawRatGCDStage.result r 4).length + 1) + 5) + 1 := h
    _ ≤ size r * (4 * (size r + gcdSizeBound r + 1) + 5) + 1 := by
      gcongr <;> omega

theorem second_division_clock_bound (r : RawRat) :
    RawRatDivisionEmbedded.clock (RawRatDenominatorDivision.dividendReady r) ≤
      divisionTimeBound r := by
  have h := RawRatDivisionEmbedded.clock_bound
    (RawRatDenominatorDivision.dividendReady r)
  rw [RawRatDenominatorDivision.ready_input,
    RawRatDenominatorDivision.ready_divisor] at h
  have hn := words_le_size r
  have hg := divisor_length_bound r
  unfold divisionTimeBound
  calc
    _ ≤ r.denominator.length *
        (4 * (r.denominator.length + (RawRatGCDStage.result r 4).length + 1) + 5) + 1 := h
    _ ≤ size r * (4 * (size r + gcdSizeBound r + 1) + 5) + 1 := by
      gcongr <;> omega

theorem first_clock_bound (r : RawRat) :
    RawRatFirstQuotientController.clock r ≤ firstTimeBound r := by
  have hg := local_clock_bound r
  have hb := gcd_size_bound r
  have hd := first_division_clock_bound r
  have hc := canonical_first_clock_bound r
  have hn := words_le_size r
  unfold RawRatFirstQuotientController.clock RawRatPreGCD.clock
    RawRatClearArithmetic.clock firstTimeBound gcdTimeBound
  omega

theorem second_clock_bound (r : RawRat) :
    RawRatSecondQuotientController.clock r ≤ secondTimeBound r := by
  have hf := first_clock_bound r
  have he := first_encoded_growth r
  have hd := second_division_clock_bound r
  have hc := canonical_second_clock_bound r
  have hlen := canonical_denominator_length r
  have hs := canonical_sign_length r
  have hw := words_le_size r
  have hm := Nat.mul_le_mul_left
    (26 * BitMachineStackGrowth.perStep
      RawRatFirstQuotientController.program) hf
  have hsize : size r = inputLength r + 1 := rfl
  unfold RawRatSecondQuotientController.clock RawRatClearArithmetic.clock
    secondTimeBound
  omega

theorem core_clock_bound (r : RawRat) :
    RawRatCoreController.clock r ≤ totalTimeBound r := by
  have h₁ := first_clock_bound r
  have h₂ := second_clock_bound r
  unfold RawRatCoreController.clock totalTimeBound
  omega

def gcdSizeCoefficient : Nat :=
  20 + 130000 * BitMachineStackGrowth.perStep RawRatGCDStage.program

def divisionCoefficient : Nat := 4 * gcdSizeCoefficient + 14

def firstCoefficient : Nat :=
  5040 + 6 * gcdSizeCoefficient + divisionCoefficient

def totalCoefficient : Nat :=
  (1 + 156 * BitMachineStackGrowth.perStep
    RawRatFirstQuotientController.program) * firstCoefficient +
    divisionCoefficient + 122

private theorem power_facts (x : Nat) (hx : 1 ≤ x) :
    x ≤ x^4 ∧ 1 ≤ x^4 ∧ x^4 ≤ x^5 ∧ x ≤ x^5 ∧ 1 ≤ x^5 := by
  have h2 : x ≤ x^2 := by nlinarith [sq_nonneg (x : ℤ)]
  have h3 : x^2 ≤ x^3 := by
    calc
      x^2 = x^2 * 1 := by omega
      _ ≤ x^2 * x := Nat.mul_le_mul_left _ hx
      _ = x^3 := by ring
  have h4 : x^3 ≤ x^4 := by
    calc
      x^3 = x^3 * 1 := by omega
      _ ≤ x^3 * x := Nat.mul_le_mul_left _ hx
      _ = x^4 := by ring
  have h5 : x^4 ≤ x^5 := by
    calc
      x^4 = x^4 * 1 := by omega
      _ ≤ x^4 * x := Nat.mul_le_mul_left _ hx
      _ = x^5 := by ring
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact h5
  constructor
  · omega
  · omega

theorem gcd_size_monomial (r : RawRat) :
    gcdSizeBound r ≤ gcdSizeCoefficient * (size r + 4)^4 := by
  let x := size r + 4
  have hx : 1 ≤ x := by omega
  obtain ⟨hs4, h14, _, _, _⟩ := power_facts x hx
  have hs : size r ≤ x^4 := (by omega : size r ≤ x).trans hs4
  have hlin : 3 * size r + 13 ≤ 20 * x^4 := by omega
  unfold gcdSizeBound gcdTimeBound gcdSizeCoefficient
  change 3 * size r + 13 +
      26 * BitMachineStackGrowth.perStep RawRatGCDStage.program *
        (5000 * x^4) ≤
      (20 + 130000 * BitMachineStackGrowth.perStep
        RawRatGCDStage.program) * x^4
  nlinarith [hlin]

theorem division_monomial (r : RawRat) :
    divisionTimeBound r ≤ divisionCoefficient * (size r + 4)^5 := by
  let x := size r + 4
  have hx : 1 ≤ x := by omega
  obtain ⟨hs4, h14, h45, hs5, h15⟩ := power_facts x hx
  have hs : size r ≤ x := by omega
  have hb := gcd_size_monomial r
  change gcdSizeBound r ≤ gcdSizeCoefficient * x^4 at hb
  have hbracket :
      4 * (size r + gcdSizeBound r + 1) + 5 ≤
        (4 * gcdSizeCoefficient + 13) * x^4 := by
    nlinarith [hs4, h14, hb]
  have hm := Nat.mul_le_mul hs hbracket
  unfold divisionTimeBound divisionCoefficient
  change size r * (4 * (size r + gcdSizeBound r + 1) + 5) + 1 ≤
    (4 * gcdSizeCoefficient + 14) * x^5
  nlinarith [hm, h15]

theorem first_monomial (r : RawRat) :
    firstTimeBound r ≤ firstCoefficient * (size r + 4)^5 := by
  let x := size r + 4
  have hx : 1 ≤ x := by omega
  obtain ⟨_, _, h45, hs5, h15⟩ := power_facts x hx
  have hs : size r ≤ x^5 := (by omega : size r ≤ x).trans hs5
  have hb := gcd_size_monomial r
  have hd := division_monomial r
  change gcdSizeBound r ≤ gcdSizeCoefficient * x^4 at hb
  change divisionTimeBound r ≤ divisionCoefficient * x^5 at hd
  have hG : gcdTimeBound r ≤ 5000 * x^5 := by
    unfold gcdTimeBound
    exact Nat.mul_le_mul_left _ h45
  have hB : 6 * gcdSizeBound r ≤
      6 * gcdSizeCoefficient * x^5 := by
    have hm := Nat.mul_le_mul_left 6 hb
    have hp := Nat.mul_le_mul_left (6 * gcdSizeCoefficient) h45
    nlinarith
  unfold firstTimeBound firstCoefficient
  change gcdTimeBound r + 6 * gcdSizeBound r + divisionTimeBound r +
      6 * size r + 25 ≤
    (5040 + 6 * gcdSizeCoefficient + divisionCoefficient) * x^5
  nlinarith [hG, hB, hd, hs, h15]

theorem total_monomial (r : RawRat) :
    totalTimeBound r ≤ totalCoefficient * (size r + 4)^5 := by
  let x := size r + 4
  have hx : 1 ≤ x := by omega
  obtain ⟨_, _, _, hs5, h15⟩ := power_facts x hx
  have hs : size r ≤ x^5 := (by omega : size r ≤ x).trans hs5
  have hf := first_monomial r
  have hd := division_monomial r
  change firstTimeBound r ≤ firstCoefficient * x^5 at hf
  change divisionTimeBound r ≤ divisionCoefficient * x^5 at hd
  have hmul := Nat.mul_le_mul_left
    (26 * BitMachineStackGrowth.perStep
      RawRatFirstQuotientController.program) hf
  unfold totalTimeBound secondTimeBound totalCoefficient
  change firstTimeBound r +
      (6 * (size r + 10 +
        26 * BitMachineStackGrowth.perStep
          RawRatFirstQuotientController.program * firstTimeBound r) +
        divisionTimeBound r + 5 * size r + 50) + 1 ≤
      ((1 + 156 * BitMachineStackGrowth.perStep
        RawRatFirstQuotientController.program) * firstCoefficient +
        divisionCoefficient + 122) * x^5
  nlinarith [hf, hd, hs, h15, hmul]

def polynomialCoefficient : Nat := 3125 * totalCoefficient

theorem core_clock_polynomial (r : RawRat) :
    RawRatCoreController.clock r ≤
      polynomialCoefficient * (inputLength r + 1)^5 := by
  have hc := core_clock_bound r
  have hp := total_monomial r
  have hx : size r + 4 ≤ 5 * (inputLength r + 1) := by
    unfold size
    omega
  have hpow := pow_le_pow_left₀ (by omega : 0 ≤ size r + 4) hx 5
  unfold polynomialCoefficient
  have hm := Nat.mul_le_mul_left totalCoefficient hpow
  calc
    _ ≤ totalTimeBound r := hc
    _ ≤ totalCoefficient * (size r + 4)^5 := hp
    _ ≤ totalCoefficient * (5 * (inputLength r + 1))^5 := hm
    _ = 3125 * totalCoefficient * (inputLength r + 1)^5 := by ring

theorem canonical_output_length_le (r : RawRat) (hr : r.Valid) :
    (encodeRawRat (CurrentAdditive.CodeDCanonicalSource.rawOfRat r.value)).length ≤
      (encodeRawRat r).length := by
  rw [← CurrentAdditive.BinaryGCDNormalization.normalize_is_rawOfRat r hr]
  have hn := CurrentAdditive.BinaryGCDNormalization.normalize_numerator_length_le r
  have hd := CurrentAdditive.BinaryGCDNormalization.normalize_denominator_length_le r
  have hs :
      (if (CurrentAdditive.BinaryGCDNormalization.normalize r).negative
        then 1 else 0) ≤ (if r.negative then 1 else 0) := by
    cases h : r.negative <;>
      simp [CurrentAdditive.BinaryGCDNormalization.normalize, h] <;>
      split_ifs <;> omega
  simp only [encodeRawRat, BitMachineBankCodec.encode_length]
  simp only [rawRatBank, Fin.sum_univ_succ]
  split_ifs at * <;> simp_all <;> omega

theorem selected_encode_le_full (S : Fin 13 → List Bool) :
    (BitMachineBankSerialize.encode
      (List.ofFn (![S 0, S 1, S 11] : Fin 3 → List Bool))).length ≤
      (BitMachineBankCodec.encode S).length := by
  have heq : BitMachineBankSerialize.encode
      (List.ofFn (![S 0, S 1, S 11] : Fin 3 → List Bool)) =
      BitMachineBankCodec.encode
        (![S 0, S 1, S 11] : Fin 3 → List Bool) := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [heq, BitMachineBankCodec.encode_length,
    BitMachineBankCodec.encode_length]
  simp [Fin.sum_univ_succ]
  omega

theorem core_output_encoded_growth (r : RawRat) :
    (BitMachineBankCodec.encode (RawRatCoreController.result r)).length ≤
      inputLength r + 10 +
        26 * BitMachineStackGrowth.perStep RawRatCoreController.program *
          RawRatCoreController.clock r := by
  obtain ⟨t, v, ht, hv⟩ := RawRatCoreController.run r
  have h := encoded_growth RawRatCoreController.program
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
      (RawRatCoreController.firstInitial,
        RawRatCoreController.secondInitial),
      RawRatPreparation.inputBank r⟩ :
      TM2.Cfg (fun _ : Fin 13 => Bool) _ _) t
  dsimp [RawRatCoreController.firstInitial,
    RawRatCoreController.secondInitial] at h
  dsimp [RawRatCoreController.firstInitial,
    RawRatCoreController.secondInitial] at hv
  rw [hv, input_bank_encoded_length] at h
  have h' : (BitMachineBankCodec.encode
      (RawRatCoreController.result r)).length ≤
      inputLength r + 10 +
        26 * BitMachineStackGrowth.perStep
          RawRatCoreController.program * t := by
    simpa only using h
  have hm := Nat.mul_le_mul_left
    (26 * BitMachineStackGrowth.perStep RawRatCoreController.program) ht
  omega

theorem selected_output_size (r : RawRat) :
    (BitMachineBankSerialize.encode
      (List.ofFn (![RawRatCoreController.result r 0,
        RawRatCoreController.result r 1,
        RawRatCoreController.result r 11] : Fin 3 → List Bool))).length ≤
      6 * (inputLength r +
        26 * BitMachineStackGrowth.perStep RawRatCoreController.program *
          RawRatCoreController.clock r) + 3 := by
  have hs := selected_encode_le_full (RawRatCoreController.result r)
  have hg := core_output_encoded_growth r
  have hlen : 3 ≤ inputLength r := by
    rw [input_length]
    omega
  omega

end CurrentAdditive.RawRatCoreClock
