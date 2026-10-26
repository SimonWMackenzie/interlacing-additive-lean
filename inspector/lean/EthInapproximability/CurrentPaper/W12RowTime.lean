import EthInapproximability.CurrentPaper.WeightedRowFields
import EthInapproximability.CurrentPaper.MatrixWeightedPreparedPolynomial

/-! Lane owner:b-weighted-level-12, segment 1 (piece): the admitted row clock
`WeightedRowFields.rowTime` is monotone in its eight arguments and of degree 9, and each of the eight
arguments used by the level-row clock `LevelJClean.boundJ` is at most the admitted prepared envelope
`ProtectedBudgetNormalizationScratch.preparedEnvelope` of the same level. Pure arithmetic. -/

namespace EthInapproximability.CurrentPaper.W12RowTime

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

theorem exactTime_mono {r w c r' w' c' : ℕ} (hr : r ≤ r') (hw : w ≤ w') (hc : c ≤ c') :
    MatrixAddressMachine.exactTime r w c ≤ MatrixAddressMachine.exactTime r' w' c' := by
  unfold MatrixAddressMachine.exactTime
  have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) hw
  omega

theorem rowTime_mono (V FS NB SL RX W29 W21 W1 X : ℕ) (h1 : V ≤ X) (h2 : FS ≤ X) (h3 : NB ≤ X)
    (h4 : SL ≤ X) (h5 : RX ≤ X) (h6 : W29 ≤ X) (h7 : W21 ≤ X) (h8 : W1 ≤ X) :
    WeightedRowFields.rowTime V FS NB SL RX W29 W21 W1 ≤
      WeightedRowFields.rowTime X X X X X X X X := by
  unfold WeightedRowFields.rowTime
  repeat' (first | with_reducible exact le_refl _ | assumption | with_reducible apply Nat.add_le_add |
    with_reducible apply exactTime_mono | with_reducible apply Nat.mul_le_mul)

def Krow : ℕ := 2 ^ 40

theorem rowTime_diag (X : ℕ) (hX : 1 ≤ X) :
    WeightedRowFields.rowTime X X X X X X X X ≤ Krow * X ^ 9 := by
  unfold WeightedRowFields.rowTime MatrixAddressMachine.exactTime Krow
  have q1 : X ≤ X ^ 9 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q2 : X ^ 2 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q3 : X ^ 3 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q4 : X ^ 4 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q5 : X ^ 5 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q6 : X ^ 6 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q7 : X ^ 7 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q8 : X ^ 8 ≤ X ^ 9 := Nat.pow_le_pow_right hX (by norm_num)
  have q0 : 1 ≤ X ^ 9 := Nat.one_le_pow _ _ hX
  ring_nf
  omega

theorem rowTime_le (V FS NB SL RX W29 W21 W1 X : ℕ) (h1 : V ≤ X) (h2 : FS ≤ X) (h3 : NB ≤ X)
    (h4 : SL ≤ X) (h5 : RX ≤ X) (h6 : W29 ≤ X) (h7 : W21 ≤ X) (h8 : W1 ≤ X) :
    WeightedRowFields.rowTime V FS NB SL RX W29 W21 W1 ≤ Krow * (X + 1) ^ 9 :=
  (rowTime_mono V FS NB SL RX W29 W21 W1 (X + 1) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)).trans (rowTime_diag (X + 1) (by omega))

/-- Each field used by the row clock is below the envelope sum (generic record). -/
theorem fields_le (d : MatrixWeightedEntryController.Input) (V s x y O : ℕ) :
    V ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    4 * s ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    d.nb ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    d.stagePrefixRows ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    d.rx ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    d.binBase ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    d.rawWidth ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O ∧
    d.uniform ≤ 1 + V + (s - 3) + 4 * s + x + y + MatrixWeightedEntryEnvelope.inputScale d x y + O := by
  unfold MatrixWeightedEntryEnvelope.inputScale
  omega

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

open ProtectedFullBankBridgeScratch in
theorem envelope_eq (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    ProtectedBudgetNormalizationScratch.preparedEnvelope G c b y j M =
      1 + Fintype.card V + (Iteration.s G c b y j M - 3) + 4 * Iteration.s G c b y j M +
        actualRows G c b y j M + actualCols G c b y j M +
        MatrixWeightedEntryEnvelope.inputScale (actualD G c b y j M) (actualRows G c b y j M) (actualCols G c b y j M) +
        ProtectedBudgetNormalizationScratch.outerSize (Iteration.rQ G c b y j M) (Iteration.rq G c b y j M)
          (actualRows G c b y j M) (actualCols G c b y j M) (actualP G c b y j M).nextDepth
          (actualP G c b y j M).sourceConstant (Parameters.bins (actualP G c b y j M))
          (Parameters.scale (actualP G c b y j M)) := rfl

open ProtectedFullBankBridgeScratch in
/-- **The level-row clock's row part is at most `Krow · (preparedEnvelope + 1)^9`**, at every level state. -/
theorem rowTime_level (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    WeightedRowFields.rowTime (Fintype.card V) (4 * Iteration.s G c b y j M)
        (actualD G c b y j M).nb (actualD G c b y j M).stagePrefixRows (actualD G c b y j M).rx
        (actualD G c b y j M).binBase (actualD G c b y j M).rawWidth (actualD G c b y j M).uniform ≤
      Krow * (ProtectedBudgetNormalizationScratch.preparedEnvelope G c b y j M + 1) ^ 9 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := fields_le (actualD G c b y j M) (Fintype.card V)
    (Iteration.s G c b y j M) (actualRows G c b y j M) (actualCols G c b y j M)
    (ProtectedBudgetNormalizationScratch.outerSize (Iteration.rQ G c b y j M) (Iteration.rq G c b y j M)
      (actualRows G c b y j M) (actualCols G c b y j M) (actualP G c b y j M).nextDepth
      (actualP G c b y j M).sourceConstant (Parameters.bins (actualP G c b y j M))
      (Parameters.scale (actualP G c b y j M)))
  rw [envelope_eq]
  exact rowTime_le _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8

#print axioms exactTime_mono
#print axioms envelope_eq
#print axioms rowTime_mono
#print axioms rowTime_diag
#print axioms rowTime_le
#print axioms fields_le
#print axioms rowTime_level

end EthInapproximability.CurrentPaper.W12RowTime
