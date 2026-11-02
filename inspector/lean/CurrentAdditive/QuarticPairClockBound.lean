import CurrentAdditive.QuarticPairFront

/-! A literal size bound for the fixed formula-preserving physical front. -/

namespace Paper2.CurrentAdditive.QuarticPairClockBound

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

noncomputable section

theorem pair_front_clock_of_atom_cap
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (raw output : List Bool) (cutTime Z : ℕ)
    (hformula : (EncodedCNF.encode Φ.val).length ≤ Z)
    (hraw : raw.length ≤ Z)
    (houtput : output.length ≤ Z)
    (hx : (BitMachineBankCodec.encode
      (FullFront.X0 (t10Graph D B Φ) (kOf Φ.val.variables) raw)).length ≤ Z)
    (hcut : cutTime ≤ Z) :
    QuarticPairFront.pairFrontClock D B Φ raw output cutTime ≤
      (QuarticPairFront.frontCoefficient D B + 100) *
        (3 * (Z + 1)) ^ (QuarticPairFront.frontExponent D B + 1) := by
  let E := EncodedCNF.encode Φ.val
  let input := EncodedComplexity.pair E raw
  let X := BitMachineBankCodec.encode
    (FullFront.X0 (t10Graph D B Φ) (kOf Φ.val.variables) raw)
  let A := 3 * (Z + 1)
  let Q := A ^ (QuarticPairFront.frontExponent D B + 1)
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hi : input.length + 1 ≤ A := by
    dsimp [input, A, E]
    rw [EncodedComplexity.pair_length]
    omega
  have hpair : (EncodedComplexity.pair E input).length ≤ 5 * (Z + 1) := by
    rw [EncodedComplexity.pair_length]
    have hE : E.length ≤ Z := hformula
    omega
  have hpow : (input.length + 1) ^ QuarticPairFront.frontExponent D B ≤ Q := by
    calc
      _ ≤ A ^ QuarticPairFront.frontExponent D B := Nat.pow_le_pow_left hi _
      _ ≤ Q := by
        dsimp [Q]
        exact Nat.pow_le_pow_right hA (by omega)
  have hlin : Z + 1 ≤ Q := by
    have hq : A ≤ Q := by
      simpa only [pow_one] using
        (Nat.pow_le_pow_right hA
          (show 1 ≤ QuarticPairFront.frontExponent D B + 1 by omega))
    dsimp [A] at hq
    omega
  have hfront : QuarticPairFront.frontCoefficient D B *
      (input.length + 1) ^ QuarticPairFront.frontExponent D B ≤
      QuarticPairFront.frontCoefficient D B * Q :=
    Nat.mul_le_mul_left _ hpow
  have hrest : QuarticPairFront.pairFrontClock D B Φ raw output cutTime ≤
      QuarticPairFront.frontCoefficient D B *
        (input.length + 1) ^ QuarticPairFront.frontExponent D B +
      100 * (Z + 1) := by
    unfold QuarticPairFront.pairFrontClock
    dsimp only [E, input, X] at *
    simp only [EncodedComplexity.pair_length] at *
    omega
  calc
    _ ≤ QuarticPairFront.frontCoefficient D B *
          (input.length + 1) ^ QuarticPairFront.frontExponent D B +
        100 * (Z + 1) := hrest
    _ ≤ QuarticPairFront.frontCoefficient D B * Q + 100 * Q :=
      Nat.add_le_add hfront (Nat.mul_le_mul_left _ hlin)
    _ = (QuarticPairFront.frontCoefficient D B + 100) *
          (3 * (Z + 1)) ^ (QuarticPairFront.frontExponent D B + 1) := by
      dsimp [Q, A]
      ring

#print axioms pair_front_clock_of_atom_cap

end
end Paper2.CurrentAdditive.QuarticPairClockBound
