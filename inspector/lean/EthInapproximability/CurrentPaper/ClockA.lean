import EthInapproximability.CurrentPaper.HB2Machine

/-! Lane owner:b-weighted-level-10, unit 2, segment 4 (first part): public scalar facts at every
level `j ≤ k`, the emission and fuel clocks, `hc` from the source constant, and the reduction of
`HB2Physical`'s clock premise to the two round majorants.

From the `HB2Physical` hypotheses alone (`SourceCommon`, `n ≤ |E|`, `|E| ≤ A n b^d`,
`1 ≤ k = repetitions c A d n`), the admitted cutoff selection
`CutoffBitMachine.actualClock_selected_cutoff` gives `sourceCutoff c A d k ≤ n`; the admitted
`EffectiveIteration.run_indexing_table_size_beyond_cutoff` / `run_indexing_budget_beyond_cutoff`
and `PhysicalLevelRun.physParameters_eq` then give, for every `j ≤ k`, `rows_j * cols_j < 4 T`
(`T = FinalPadding.tableSize (repetitions c A d) n`) and `2 k (y_j + j + j) < n` (`level_facts`).
So every emission term is linear in `|w|` and `T` (`emit_clock`), the fuel shell's clock is
`2|w| + L0 + I0 + (k-1)(T_round+1) + O(|w|)` (`fuel_clock`), and `hb2_physical_reduced` derives
`HB2Physical` from: `hW₀`, `hW`, `hT`, and TWO polynomial bounds `level0BoundP + installBoundP 0 ≤
C (|w|+1)^e T^f` and `T_round ≤ C (|w|+1)^e T^f`. -/

namespace EthInapproximability.CurrentPaper.ClockA

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open RoundInstall (installProgram installCtrl)
open FuelShell Emission HB2Machine

noncomputable section

set_option maxHeartbeats 3000000

/-- `hc` from the source-constant hypotheses of the endpoint (admitted `source_constant_floor`). -/
theorem hc_of_source {c Δ : ℕ} {γ : ℚ} (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) : 1 ≤ c :=
  le_trans (Nat.one_le_two_pow) (IterationAlignedComplete.source_constant_floor hΔ hγ hγone hsource)

/-- `(r c)^k < 2^n` with `1 ≤ k` gives `r c < 4 * tableSize`. -/
theorem lt_four_table (L : ℕ → ℕ) (n x : ℕ) (hk : 1 ≤ L n) (hx : x ^ L n < 2 ^ n) :
    x < 4 * FinalPadding.tableSize L n := by
  unfold FinalPadding.tableSize FinalPadding.exponent
  rw [max_eq_right hk]
  set k := L n with hkdef
  set e := n / (2 * k) with he
  have h1 : n < 2 * k * (e + 1) := Nat.lt_mul_div_succ n (by omega)
  have h2 : 2 ^ n < 2 ^ (2 * (e + 1) * k) :=
    Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  have h3 : 2 ^ (2 * (e + 1) * k) = (4 * 2 ^ (2 * e)) ^ k := by
    rw [pow_mul]
    congr 1
    rw [show 2 * (e + 1) = 2 * e + 2 by ring, pow_add]
    ring
  by_contra hc
  rw [not_lt] at hc
  have h4 := Nat.pow_le_pow_left hc k
  omega

theorem one_le_table (L : ℕ → ℕ) (n : ℕ) : 1 ≤ FinalPadding.tableSize L n :=
  Nat.one_le_two_pow

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Public scalar facts at every level `j ≤ k`, from the `HB2Physical` hypotheses alone. -/
theorem level_facts (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ) (hj : j ≤ ETHTailGrowth.repetitions c A d n) :
    (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.rows *
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.columns <
        4 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ∧
    2 * ETHTailGrowth.repetitions c A d n *
      ((PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).budget + j + j) < n := by
  set k := ETHTailGrowth.repetitions c A d n with hkdef
  set b := EffectiveIteration.sourceDepth n with hb
  have hcut : EffectiveIteration.sourceCutoff c A d k ≤ n :=
    CutoffBitMachine.actualClock_selected_cutoff c A d n k hrep (le_refl _)
  have hv : Fintype.card V ≤ 2 * Fintype.card E := hcommon.1
  have hsz := EffectiveIteration.run_indexing_table_size_beyond_cutoff G c A d n k (by omega) hcut hv
    hlower hupper j hj
  have hbud := EffectiveIteration.run_indexing_budget_beyond_cutoff G c A d n k (by omega) hcut hv
    hlower hupper j hj
  have hr := congrArg Parameters.Input.rows
    (PhysicalLevelRun.physParameters_eq G c b (Iteration.seedState b) j)
  have hcl := congrArg Parameters.Input.columns
    (PhysicalLevelRun.physParameters_eq G c b (Iteration.seedState b) j)
  have hco := congrArg Parameters.Input.cost
    (PhysicalLevelRun.physParameters_eq G c b (Iteration.seedState b) j)
  change (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix.rows = _ at hr
  change (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix.columns = _ at hcl
  change (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).budget + j = _ at hco
  dsimp only at hsz
  refine ⟨?_, ?_⟩
  · apply lt_four_table (ETHTailGrowth.repetitions c A d) n _ hrep
    rw [hr, hcl]
    exact hsz.2
  · rw [hco]
    exact hbud

theorem k_le (k y n : ℕ) (hk : 1 ≤ k) (h : 2 * k * (y + k + k) < n) : k ≤ n := by
  nlinarith

theorem rows_le_prod (M : Iteration.Matrix) : M.rows ≤ M.rows * M.columns :=
  Nat.le_mul_of_pos_right _ M.columns_pos

theorem cols_le_prod (M : Iteration.Matrix) : M.columns ≤ M.rows * M.columns :=
  Nat.le_mul_of_pos_left _ M.rows_pos

theorem hb2Word_length (G : EndpointGraph V E) (n c k : ℕ) :
    (hb2Word G n c k).length =
      2 * (n + k + (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).matrix.rows +
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).matrix.columns +
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).matrix.rows *
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).matrix.columns +
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).budget) + 6 := by
  unfold hb2Word
  rw [BitMachineBankCodec.encode_length]
  simp [Fin.sum_univ_succ, MatrixMaterialization.rowMajor_length]
  ring

/-- The emission clock is linear in the packet length and the table size. -/
theorem emit_clock (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) :
    emitBound G n c (ETHTailGrowth.repetitions c A d n) ≤
      100 * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length +
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n + 1) := by
  have hf := level_facts G c A d Δ n γ hcommon hlower hupper hrep _ (le_refl _)
  set k := ETHTailGrowth.repetitions c A d n with hkdef
  set st := PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) k with hst
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hT
  have hpl := SourceOriginalBranchPackets.packet_length n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hwl := hb2Word_length G n c k
  rw [← hst] at hwl
  have hr := rows_le_prod st.matrix
  have hc := cols_le_prod st.matrix
  have hkk : k * k ≤ 2 * k * (st.budget + k + k) := by nlinarith
  have hkb : k * (st.budget + k) ≤ 2 * k * (st.budget + k + k) := by nlinarith
  have hk1 : k ≤ k * k := Nat.le_mul_self k
  have hkb1 : st.budget + k ≤ k * (st.budget + k) := Nat.le_mul_of_pos_left _ (by omega)
  have hml := MatrixMaterialization.rowMajor_length st.matrix.entry
  have hb : emitBound G n c k = 5 * ((SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) +
      (2 * k + 2) + (2 * st.matrix.rows + 2) + (2 * st.matrix.columns + 2) +
      (2 * (MatrixMaterialization.rowMajor st.matrix.entry).length + 2) +
      (2 * (st.budget + k) + 2) + (2 * k + 2) + (k + 1) +
      (2 * (hb2Word G n c k).length + 2) + 8 := rfl
  rw [hb, hml, hwl]
  omega

/-- The fuel shell's clock, with the two round terms kept. -/
theorem fuel_clock [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (M : BitMachine.Machine) (G : EndpointGraph V E) (n c T22₀ T : ℕ)
    (hkn : WeightedRawWords.kValue M n ≤ n) :
    fuelShellBound M G n c T22₀ T ≤
      level0BoundP M G n c T22₀ + installBoundP G c (EffectiveIteration.sourceDepth n) 0 +
        (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length * (T + 1) +
        4 * (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 12 := by
  have hpl := SourceOriginalBranchPackets.packet_length n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  set w := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hw
  set k := WeightedRawWords.kValue M n with hk
  have hkw : k - 1 ≤ w := by omega
  have hm : (k - 1) * (T + 1) ≤ w * (T + 1) := Nat.mul_le_mul_right _ hkw
  unfold fuelShellBound
  rw [← hw, ← hk]
  omega

/-- `HB2Physical` from `hc`, the writer-22 specifications, `hT`, and TWO polynomial round
majorants: the level-0 round with its install, and the uniform round majorant `T`. -/
theorem hb2_physical_reduced [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (c A d Δ : ℕ) (γ : ℚ) (hc : 1 ≤ c)
    {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (C e f : ℕ)
    (hprem : ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      ∃ T22₀ T22 T : ℕ,
        Writer22Spec (CutoffBitMachine.actualMachine c A d) W₀ w₀₀ v₀₀ T22₀ G n c ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
            (yP G c (EffectiveIteration.sourceDepth n) j) j
            (MP G c (EffectiveIteration.sourceDepth n) j)
            (mSj (mb1 (CutoffBitMachine.actualMachine c A d) G n c) G c
              (EffectiveIteration.sourceDepth n) j)
            (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry)) ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          roundBoundP G c (EffectiveIteration.sourceDepth n) j
              (mb1 (CutoffBitMachine.actualMachine c A d) G n c)
              (MatrixMaterialization.rowMajor
                (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 +
            installBoundP G c (EffectiveIteration.sourceDepth n) j + 1 ≤ T) ∧
        level0BoundP (CutoffBitMachine.actualMachine c A d) G n c T22₀ +
            installBoundP G c (EffectiveIteration.sourceDepth n) 0 ≤
          C * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ e *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ f ∧
        T ≤ C * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ e *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ f) :
    PhysicalLevelRun.HB2Physical c A d Δ γ := by
  apply hb2_physical c A d Δ γ hc W₀ w₀₀ v₀₀ W w₀ v₀ (2 * C + 400) (e + 1) (f + 1)
  intro V E _ _ _ _ G n hcommon hlower hupper hrep
  obtain ⟨T22₀, T22, T, hW₀, hW, hT, h0, hTT⟩ := hprem G n hcommon hlower hupper hrep
  refine ⟨T22₀, T22, T, hW₀, hW, hT, ?_⟩
  have hkk := (level_facts G c A d Δ n γ hcommon hlower hupper hrep _ (le_refl _)).2
  have hkn : ETHTailGrowth.repetitions c A d n ≤ n := k_le _ _ _ hrep hkk
  have hfuel := fuel_clock (CutoffBitMachine.actualMachine c A d) G n c T22₀ T hkn
  have hemit := emit_clock G c A d Δ n γ hcommon hlower hupper hrep
  rw [kValue_actual]
  set w := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hw
  set t := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with ht
  set X := (w + 1) ^ (e + 1) * t ^ (f + 1) with hX
  set B := C * (w + 1) ^ e * t ^ f with hB
  have ht1 : 1 ≤ t := one_le_table _ _
  have hwe : 1 ≤ (w + 1) ^ e := Nat.one_le_pow _ _ (by omega)
  have htf : 1 ≤ t ^ f := Nat.one_le_pow _ _ ht1
  have hP1 : 1 ≤ (w + 1) ^ e * t ^ f * t := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hwe htf) ht1
    simpa using this
  have hP2 : 1 ≤ (w + 1) ^ e * (w + 1) * t ^ f := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hwe (show 1 ≤ w + 1 by omega)) htf
    simpa using this
  have hwX : w + 1 ≤ X := by
    calc w + 1 = (w + 1) * 1 := by ring
      _ ≤ (w + 1) * ((w + 1) ^ e * t ^ f * t) := Nat.mul_le_mul_left _ hP1
      _ = X := by rw [hX]; ring
  have htX : t ≤ X := by
    calc t = t * 1 := by ring
      _ ≤ t * ((w + 1) ^ e * (w + 1) * t ^ f) := Nat.mul_le_mul_left _ hP2
      _ = X := by rw [hX]; ring
  have hBX : (w + 1) * B ≤ C * X := by
    calc (w + 1) * B = (w + 1) * B * 1 := by ring
      _ ≤ (w + 1) * B * t := Nat.mul_le_mul_left _ ht1
      _ = C * X := by rw [hX, hB]; ring
  have hB1 : B ≤ (w + 1) * B := Nat.le_mul_of_pos_left _ (by omega)
  have hTw : w * (T + 1) ≤ (w + 1) * B + (w + 1) := by
    have h := Nat.mul_le_mul (Nat.le_succ w) (Nat.succ_le_succ hTT)
    calc w * (T + 1) ≤ (w + 1) * (B + 1) := h
      _ = (w + 1) * B + (w + 1) := by ring
  have hsplit : (2 * C + 400) * X = 2 * (C * X) + 400 * X := by ring
  calc fuelShellBound (CutoffBitMachine.actualMachine c A d) G n c T22₀ T +
        emitBound G n c (ETHTailGrowth.repetitions c A d n) + 1
      ≤ B + w * (T + 1) + 4 * w + 12 + 100 * (w + t + 1) + 1 := by omega
    _ ≤ (2 * C + 400) * X := by rw [hsplit]; omega
    _ = (2 * C + 400) * (w + 1) ^ (e + 1) * t ^ (f + 1) := by rw [hX]; ring

#print axioms hc_of_source
#print axioms lt_four_table
#print axioms level_facts
#print axioms hb2Word_length
#print axioms emit_clock
#print axioms fuel_clock
#print axioms hb2_physical_reduced

end
end EthInapproximability.CurrentPaper.ClockA
