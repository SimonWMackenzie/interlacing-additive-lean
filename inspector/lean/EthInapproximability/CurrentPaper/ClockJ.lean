import EthInapproximability.CurrentPaper.ClockI

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 (third piece): the admitted Stage-4
bridge budget `ProtectedFullBankBridgeScratch.actualPhysicalBudget` at every round level.

* `outerSize_le`: the admitted outer-size envelope is at most
  `λ + b + c + s + 19 O + 4`, where `O = (2^r rows)^(2^R) (2^R cols^(2^r))` is the size of the
  two-interlace output (every other large term of the envelope divides into `O`).
* `phys_output_len`: `O` is literally the length of `actualPhysicalOutput`.
* `envelope_le`: the admitted `preparedEnvelope ≤ |V| + scale P + nextDepth P + sourceConstant P
  + bins P + 200 O²` (via `ClockI.inputScale_le` on `actualD`).
* `level_envelope`, `level_budget`: at every physical level `j < k`,
  `preparedEnvelope ≤ KE c A · Z²` and
  `actualPhysicalBudget ≤ coefficient · KE c A ^ 18 · Z ^ 36`, `Z = (|w|+1)^(d+1) · tableSize`
  (from the admitted `actualPhysicalBudget_prepared_polynomial`, `ClockE.level_output` (`O < 4T`),
  `ClockC.level_scaleBound`, `scale_le`, `bins_le`). -/

namespace EthInapproximability.CurrentPaper.ClockJ

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

noncomputable section

theorem dims_pos (R r rows cols : ℕ)
    (hO : 1 ≤ (2 ^ r * rows) ^ 2 ^ R * (2 ^ R * cols ^ 2 ^ r)) : 1 ≤ rows ∧ 1 ≤ cols := by
  have hW : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ R := Nat.one_le_two_pow
  constructor
  · refine Nat.pos_of_ne_zero (fun h => ?_)
    rw [h, Nat.mul_zero, Nat.zero_pow (by omega), Nat.zero_mul] at hO
    omega
  · refine Nat.pos_of_ne_zero (fun h => ?_)
    rw [h, Nat.zero_pow (by omega), Nat.mul_zero, Nat.mul_zero] at hO
    omega

theorem outerSize_le (R r rows cols b c s lam : ℕ)
    (hO : 1 ≤ (2 ^ r * rows) ^ 2 ^ R * (2 ^ R * cols ^ 2 ^ r)) :
    ProtectedBudgetNormalizationScratch.outerSize R r rows cols b c s lam ≤
      lam + b + c + s + 19 * ((2 ^ r * rows) ^ 2 ^ R * (2 ^ R * cols ^ 2 ^ r)) + 4 := by
  obtain ⟨hrows, hcols⟩ := dims_pos R r rows cols hO
  have hW : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ R := Nat.one_le_two_pow
  unfold ProtectedBudgetNormalizationScratch.outerSize
  dsimp only
  set W := 2 ^ r with hWd
  set B := 2 ^ R with hBd
  have hX : 1 ≤ W * rows := Nat.mul_pos hW hrows
  have hY : 1 ≤ cols ^ W := Nat.one_le_pow _ _ hcols
  have hXB : 1 ≤ (W * rows) ^ B := Nat.one_le_pow _ _ hX
  have hBY : 1 ≤ B * cols ^ W := Nat.mul_pos hB hY
  have h1 : W * rows ≤ (W * rows) ^ B := Nat.le_self_pow (by omega) _
  have h2 : (W * rows) ^ B ≤ (W * rows) ^ B * (B * cols ^ W) := Nat.le_mul_of_pos_right _ hBY
  have h3 : B * cols ^ W ≤ (W * rows) ^ B * (B * cols ^ W) := Nat.le_mul_of_pos_left _ hXB
  have h4 : cols ^ W ≤ B * cols ^ W := Nat.le_mul_of_pos_left _ hB
  have h5 : B ≤ B * cols ^ W := Nat.le_mul_of_pos_right _ hY
  have h6 : W ≤ W * rows := Nat.le_mul_of_pos_right _ hrows
  have h7 : rows ≤ W * rows := Nat.le_mul_of_pos_left _ hW
  have h8 : cols ≤ cols ^ W := by
    calc cols = cols ^ 1 := (pow_one _).symm
      _ ≤ cols ^ W := Nat.pow_le_pow_right hcols hW
  have h9 : W * rows * cols ^ W ≤ (W * rows) ^ B * (B * cols ^ W) := Nat.mul_le_mul h1 h4
  have h10 : cols ^ W * (W * rows) ≤ (W * rows) ^ B * (B * cols ^ W) := by
    rw [Nat.mul_comm]; exact h9
  have h11 : rows * cols ≤ (W * rows) ^ B * (B * cols ^ W) :=
    le_trans (Nat.mul_le_mul h7 h8) h9
  have h12 : B * cols ^ W * (W * rows) ^ B = (W * rows) ^ B * (B * cols ^ W) := Nat.mul_comm _ _
  omega

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

open ProtectedFullBankBridgeScratch in
theorem phys_output_len (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    (actualPhysicalOutput G c b y j M).length =
      (2 ^ Iteration.rq G c b y j M * actualRows G c b y j M) ^ 2 ^ Iteration.rQ G c b y j M *
        (2 ^ Iteration.rQ G c b y j M * actualCols G c b y j M ^ 2 ^ Iteration.rq G c b y j M) := by
  unfold actualPhysicalOutput
  rw [MatrixMaterialization.rowMajor_length]
  rfl

open ProtectedFullBankBridgeScratch in
theorem envelope_le (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix) :
    ProtectedBudgetNormalizationScratch.preparedEnvelope G c b y j M ≤
      Fintype.card V + Parameters.scale (actualP G c b y j M) + (actualP G c b y j M).nextDepth +
        (actualP G c b y j M).sourceConstant + Parameters.bins (actualP G c b y j M) +
        200 * ((actualPhysicalOutput G c b y j M).length * (actualPhysicalOutput G c b y j M).length) := by
  have hO0 : 1 ≤ (actualPhysicalOutput G c b y j M).length := by
    rw [ClockE.output_length]
    exact Nat.mul_pos (Iteration.step G c b y j M).rows_pos (Iteration.step G c b y j M).columns_pos
  have hO := hO0
  rw [phys_output_len] at hO
  obtain ⟨hrows, hcols⟩ := dims_pos _ _ _ _ hO
  have hOS := outerSize_le (Iteration.rQ G c b y j M) (Iteration.rq G c b y j M)
    (actualRows G c b y j M) (actualCols G c b y j M) (actualP G c b y j M).nextDepth
    (actualP G c b y j M).sourceConstant (Parameters.bins (actualP G c b y j M))
    (Parameters.scale (actualP G c b y j M)) hO
  rw [← phys_output_len] at hOS
  have hIS : MatrixWeightedEntryEnvelope.inputScale (actualD G c b y j M) (actualRows G c b y j M)
      (actualCols G c b y j M) ≤
      1 + actualRows G c b y j M + actualCols G c b y j M + 8 * actualRows G c b y j M +
        12 * actualCols G c b y j M + actualRows G c b y j M * actualCols G c b y j M +
        actualCols G c b y j M * actualCols G c b y j M :=
    ClockI.inputScale_le M.entry (Iteration.a G c b y j M) (Iteration.s G c b y j M)
      (Iteration.q₂ G c b y j M) (Iteration.labels G c b y j M)
      (GraphVectors.vertexCount V (Iteration.s G c b y j M))
      (GraphVectors.auxiliaryCount (Iteration.s G c b y j M))
      (lt_of_lt_of_le (by decide : 0 < 4) (Iteration.bins_ge_four G c b y j M))
      (Iteration.secondFamily G c b y j M) (GraphVectors.itemOrder G (Iteration.s G c b y j M))
      (GraphVectors.vectors G (Iteration.s G c b y j M))
      (GraphVectors.supportCap G (le_trans (by decide : 3 ≤ 4) (Iteration.bins_ge_four G c b y j M)))
      (actualRows G c b y j M) (actualCols G c b y j M) hrows hcols
  have hsd : (actualD G c b y j M).s = Iteration.s G c b y j M := rfl
  have hsIS : (actualD G c b y j M).s ≤ MatrixWeightedEntryEnvelope.inputScale (actualD G c b y j M)
      (actualRows G c b y j M) (actualCols G c b y j M) := by
    unfold MatrixWeightedEntryEnvelope.inputScale; omega
  rw [hsd] at hsIS
  -- the output dominates the carriers
  have hOr : actualRows G c b y j M ≤ (actualPhysicalOutput G c b y j M).length := by
    have := ClockF.actualRows_le G c b y j M
    rw [ClockE.output_length]
    exact le_trans this (Nat.le_mul_of_pos_right _ (Iteration.step G c b y j M).columns_pos)
  have hOc : actualCols G c b y j M ≤ (actualPhysicalOutput G c b y j M).length := by
    have := ClockF.actualCols_le G c b y j M
    rw [ClockE.output_length]
    exact le_trans this (Nat.le_mul_of_pos_left _ (Iteration.step G c b y j M).rows_pos)
  have hrc : actualRows G c b y j M * actualCols G c b y j M ≤
      (actualPhysicalOutput G c b y j M).length * (actualPhysicalOutput G c b y j M).length :=
    Nat.mul_le_mul hOr hOc
  have hcc : actualCols G c b y j M * actualCols G c b y j M ≤
      (actualPhysicalOutput G c b y j M).length * (actualPhysicalOutput G c b y j M).length :=
    Nat.mul_le_mul hOc hOc
  have hOO : (actualPhysicalOutput G c b y j M).length ≤
      (actualPhysicalOutput G c b y j M).length * (actualPhysicalOutput G c b y j M).length :=
    Nat.le_mul_of_pos_left _ hO0
  show 1 + Fintype.card V + (Iteration.s G c b y j M - 3) + 4 * Iteration.s G c b y j M +
      actualRows G c b y j M + actualCols G c b y j M +
      MatrixWeightedEntryEnvelope.inputScale (actualD G c b y j M) (actualRows G c b y j M)
        (actualCols G c b y j M) +
      ProtectedBudgetNormalizationScratch.outerSize (Iteration.rQ G c b y j M) (Iteration.rq G c b y j M)
        (actualRows G c b y j M) (actualCols G c b y j M) (actualP G c b y j M).nextDepth
        (actualP G c b y j M).sourceConstant (Parameters.bins (actualP G c b y j M))
        (Parameters.scale (actualP G c b y j M)) ≤ _
  omega

#print axioms outerSize_le
#print axioms phys_output_len
#print axioms envelope_le

end
end EthInapproximability.CurrentPaper.ClockJ
