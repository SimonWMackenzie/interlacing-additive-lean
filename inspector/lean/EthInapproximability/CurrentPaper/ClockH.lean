import EthInapproximability.CurrentPaper.ClockG
import EthInapproximability.CurrentPaper.MatrixWeightedPreparedPolynomial

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 (first piece): translation of the
entry-clock shape and the carrier sizes of the Stage-4 entry input.

* `translate`: a clock `X ≤ (n + |enc G| + 1)^C + 2^(C p)` with `p = FinalPadding.exponent L n`
  (the naming length whose square is the table size) is `≤ 2 (|w|+1)^C tableSize^C`, where `w` is
  the branch packet (`|w| = 2(n + |enc G|) + 2`).
* `level_exponent`: at every round level `i < k`, `oneLevelBound P_i ≤ exponent`, i.e. the naming
  premise `oneLevelBound ≤ p` of the entry-clock lemmas holds at `p = exponent` (from
  `ClockG.level_widths`).
* `inputScale_le`: every field of the admitted entry input `MatrixWeightedEntrySemantic.actualInput`
  is bounded by the two protected carrier counts `PC = |ProtectedColumns|`, `PR = |ProtectedRows|`
  (when both are positive), hence `inputScale d x y ≤ 1 + x + y + 64 (PC + PR) + PC PR + PR^2`. -/

namespace EthInapproximability.CurrentPaper.ClockH

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Construction MatrixStage4Codes MatrixStage4Digits WeightedDuplication

noncomputable section

/-! ## Translation of the entry-clock shape -/

theorem packet_ge (n : ℕ) (word : List Bool) :
    n + word.length + 1 ≤ (SourceOriginalBranchPackets.packet n word).length + 1 := by
  rw [SourceOriginalBranchPackets.packet_length]; omega

theorem le_exponent (L : ℕ → ℕ) (n x : ℕ) (hk : 1 ≤ L n) (h : 2 * L n * x < n) :
    x ≤ FinalPadding.exponent L n := by
  unfold FinalPadding.exponent
  rw [max_eq_right hk, Nat.le_div_iff_mul_le (by omega)]
  calc x * (2 * L n) = 2 * L n * x := Nat.mul_comm _ _
    _ ≤ n := le_of_lt h

theorem two_pow_le_table (L : ℕ → ℕ) (n C : ℕ) :
    2 ^ (C * FinalPadding.exponent L n) ≤ FinalPadding.tableSize L n ^ C := by
  unfold FinalPadding.tableSize
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  have : 2 * FinalPadding.exponent L n * C = 2 * (C * FinalPadding.exponent L n) := by ring
  omega

theorem table_pos (L : ℕ → ℕ) (n : ℕ) : 1 ≤ FinalPadding.tableSize L n := by
  unfold FinalPadding.tableSize; exact Nat.one_le_two_pow

/-- The entry-clock shape `(n + |enc G| + 1)^C + 2^(C p)` at `p = exponent` is a
`(|w|+1)^C tableSize^C` bound. -/
theorem translate (L : ℕ → ℕ) (n ell wl C X : ℕ) (hw : n + ell + 1 ≤ wl + 1)
    (hX : X ≤ (n + ell + 1) ^ C + 2 ^ (C * FinalPadding.exponent L n)) :
    X ≤ 2 * (wl + 1) ^ C * FinalPadding.tableSize L n ^ C := by
  have h1 : (n + ell + 1) ^ C ≤ (wl + 1) ^ C := Nat.pow_le_pow_left hw C
  have h2 := two_pow_le_table L n C
  have hT : 1 ≤ FinalPadding.tableSize L n ^ C := Nat.one_le_pow _ _ (table_pos L n)
  have hW : 1 ≤ (wl + 1) ^ C := Nat.one_le_pow _ _ (by omega)
  have h3 : (wl + 1) ^ C ≤ (wl + 1) ^ C * FinalPadding.tableSize L n ^ C :=
    Nat.le_mul_of_pos_right _ hT
  have h4 : FinalPadding.tableSize L n ^ C ≤ (wl + 1) ^ C * FinalPadding.tableSize L n ^ C :=
    Nat.le_mul_of_pos_left _ hW
  have h5 : 2 * (wl + 1) ^ C * FinalPadding.tableSize L n ^ C =
      (wl + 1) ^ C * FinalPadding.tableSize L n ^ C + (wl + 1) ^ C * FinalPadding.tableSize L n ^ C := by
    ring
  omega

/-- The packet form: `(n + |enc G| + 1)^C + 2^(C·exponent) ≤ 2 (|w|+1)^C T^C`. -/
theorem translate_packet {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (L : ℕ → ℕ) (n C X : ℕ)
    (hX : X ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C +
      2 ^ (C * FinalPadding.exponent L n)) :
    X ≤ 2 * ((SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ C *
      FinalPadding.tableSize L n ^ C :=
  translate L n _ _ C X (packet_ge n _) hX

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- At every round level `i < k` the naming premise holds at `p = exponent`. -/
theorem level_exponent (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (i : ℕ)
    (hi : i < ETHTailGrowth.repetitions c A d n) :
    EffectiveIteration.oneLevelBound
        (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) i) ≤
      FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n :=
  le_exponent _ n _ hrep (ClockG.level_widths G c A d Δ n γ hcommon hlower hupper hrep i hi).1

/-! ## Carrier sizes of the entry input -/

theorem card_mul_copies {I : Type} [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, Fintype (S i)]
    (c : I → ℕ) (i : I) :
    Fintype.card (S i) * copies S c i = c i * ∏ h, Fintype.card (S h) := by
  unfold copies
  rw [Nat.mul_left_comm]
  congr 1
  exact Finset.mul_prod_erase _ (fun h => Fintype.card (S h)) (Finset.mem_univ i)

theorem prod_rowSupport (X T V B : Type) [Fintype X] [Fintype T] [Fintype V] [Fintype B] :
    ∏ h : Fin 4, Fintype.card (rowSupport X T V B h) =
      Fintype.card X * Fintype.card T * Fintype.card V * Fintype.card B := by
  simp [Fin.prod_univ_four]

theorem rowWeight_le (i : Fin 4) : rowWeight i ≤ 2 ^ 22 := by
  fin_cases i <;> simp [rowWeight]

theorem card_rowSupport_pos (X T V B : Type) [Fintype X] [Fintype T] [Fintype V] [Fintype B]
    (h : 0 < Fintype.card X * Fintype.card T * Fintype.card V * Fintype.card B) (i : Fin 4) :
    0 < Fintype.card (rowSupport X T V B i) := by
  have hX : 0 < Fintype.card X := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with h0 | h0
    · simp [h0] at h
    · exact h0
  have hT : 0 < Fintype.card T := by
    rcases Nat.eq_zero_or_pos (Fintype.card T) with h0 | h0
    · simp [h0] at h
    · exact h0
  have hV : 0 < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | h0
    · simp [h0] at h
    · exact h0
  have hB : 0 < Fintype.card B := by
    rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | h0
    · simp [h0] at h
    · exact h0
  rw [card_rowSupport]
  fin_cases i
  · exact hX
  · exact hT
  · exact hV
  · exact hB

/-- `card (S i) * copies i ≤ |Rows|`, and `copies i ≤ |Rows|`. -/
theorem boundary_le (X T V B : Type) [Fintype X] [Fintype T] [Fintype V] [Fintype B] (i : Fin 4) :
    Fintype.card (rowSupport X T V B i) * copies (rowSupport X T V B) rowWeight i ≤
      Fintype.card (Rows X T V B) := by
  rw [card_mul_copies, prod_rowSupport, card_rows]
  have := rowWeight_le i
  have h : rowWeight i * (Fintype.card X * Fintype.card T * Fintype.card V * Fintype.card B) ≤
      2 ^ 22 * (Fintype.card X * Fintype.card T * Fintype.card V * Fintype.card B) :=
    Nat.mul_le_mul_right _ this
  calc _ ≤ _ := h
    _ = _ := by ring

theorem divisor_le (X T V B : Type) [Fintype X] [Fintype T] [Fintype V] [Fintype B]
    (h : 0 < Fintype.card X * Fintype.card T * Fintype.card V * Fintype.card B) (i : Fin 4) :
    copies (rowSupport X T V B) rowWeight i ≤ Fintype.card (Rows X T V B) := by
  have hp := card_rowSupport_pos X T V B h i
  calc copies (rowSupport X T V B) rowWeight i
      ≤ Fintype.card (rowSupport X T V B i) * copies (rowSupport X T V B) rowWeight i :=
        Nat.le_mul_of_pos_left _ hp
    _ ≤ _ := boundary_le X T V B i

#print axioms translate
#print axioms translate_packet
#print axioms level_exponent
#print axioms boundary_le
#print axioms divisor_le

end
end EthInapproximability.CurrentPaper.ClockH
