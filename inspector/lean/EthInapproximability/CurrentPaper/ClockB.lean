import EthInapproximability.CurrentPaper.ClockA

/-! Lane owner:b-weighted-level-10, unit 2, segment 4b-i: the install clocks and the reduction of
`HB2Physical` to the two ROUND clocks.

`install_clock`: for every `j < k`, `installBoundP G c b j ≤ (2c + 2A + 64) (|w|+1)^(d+1) T`
(the six install words are unary `c`, `b`, `y_{j+1} + j + 1`, rows, columns, `|E|` of level
`j+1 ≤ k`; `b ≤ n + 1` by the admitted `sourceDepth_le_succ`; `|E| ≤ A n b^d`).
`hb2_physical_rounds`: `HB2Physical` from `hc`, `hW₀`, `hW` and TWO polynomial bounds, on the
level-0 round clock `level0BoundP` and on ONE uniform majorant `R` of the round clocks
`roundBoundP j` (`1 ≤ j < k`); the round majorant `T` and the install clocks are supplied here.
`hb2_physical_source`: the same with the endpoint's source-constant hypotheses in place of `hc`. -/

namespace EthInapproximability.CurrentPaper.ClockB

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open RoundInstall (installProgram installCtrl W6)
open FuelShell Emission HB2Machine ClockA

noncomputable section

set_option maxHeartbeats 3000000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem installBoundP_eq (G : EndpointGraph V E) (c b j : ℕ) :
    installBoundP G c b j =
      2 * c + 2 * b + 2 * ((PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).budget + (j + 1)) +
        2 * Fintype.card E +
        3 * (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.rows +
        3 * (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.columns +
        2 * (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 30 := by
  unfold installBoundP
  simp [ETHParameterScaleMachineInput.words, Iteration.parameters, LevelJPrep.Pj, yP, MP]

/-- The install clock at every level `j < k` is polynomial in the packet length and the table. -/
theorem install_clock (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    installBoundP G c (EffectiveIteration.sourceDepth n) j ≤
      (2 * c + 2 * A + 64) *
        ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := by
  have hf := level_facts G c A d Δ n γ hcommon hlower hupper hrep (j + 1) hj
  have hpl := SourceOriginalBranchPackets.packet_length n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hb := WeightedRawWordsClock.sourceDepth_le_succ n
  rw [installBoundP_eq]
  set k := ETHTailGrowth.repetitions c A d n with hkdef
  set b := EffectiveIteration.sourceDepth n with hbdef
  set st := PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1) with hst
  set t := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with ht
  set w := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hw
  set g := (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length with hg
  have hr := rows_le_prod st.matrix
  have hc := cols_le_prod st.matrix
  have hcost : st.budget + (j + 1) < n := by
    have h1 : st.budget + (j + 1) + (j + 1) ≤ 2 * k * (st.budget + (j + 1) + (j + 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have ht1 : 1 ≤ t := one_le_table _ _
  set Y := (w + 1) ^ (d + 1) with hY
  have hY1 : w + 1 ≤ Y := by
    rw [hY, pow_succ]
    have h1 := Nat.one_le_pow d (w + 1) (by omega)
    calc w + 1 = 1 * (w + 1) := by ring
      _ ≤ (w + 1) ^ d * (w + 1) := Nat.mul_le_mul_right _ h1
  have hbY : b ^ d ≤ (w + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have hE : Fintype.card E ≤ A * Y := by
    calc Fintype.card E ≤ A * n * b ^ d := hupper
      _ ≤ A * (w + 1) * (w + 1) ^ d := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hbY
      _ = A * Y := by rw [hY, pow_succ]; ring
  set X := Y * t with hX
  have hYX : Y ≤ X := by
    calc Y = Y * 1 := by ring
      _ ≤ Y * t := Nat.mul_le_mul_left _ ht1
  have htX : t ≤ X := by
    calc t = 1 * t := by ring
      _ ≤ Y * t := Nat.mul_le_mul_right _ (by omega)
  have hAX : A * Y ≤ A * X := Nat.mul_le_mul_left _ hYX
  have hcX : c ≤ c * X := Nat.le_mul_of_pos_right _ (by omega)
  have hsplit : (2 * c + 2 * A + 64) * Y * t = 2 * (c * X) + 2 * (A * X) + 64 * X := by
    rw [hX]; ring
  rw [hsplit]
  omega

/-- `HB2Physical` from `hc`, the writer-22 specifications, and polynomial bounds on the two ROUND
clocks: the level-0 round clock `level0BoundP` and one uniform majorant `R` of `roundBoundP j`. -/
theorem hb2_physical_rounds [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (c A d Δ : ℕ) (γ : ℚ) (hc : 1 ≤ c)
    {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (C e f : ℕ)
    (hprem : ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      ∃ T22₀ T22 R : ℕ,
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
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 ≤ R) ∧
        level0BoundP (CutoffBitMachine.actualMachine c A d) G n c T22₀ ≤
          C * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ e *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ f ∧
        R ≤ C * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ e *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ f) :
    PhysicalLevelRun.HB2Physical c A d Δ γ := by
  apply hb2_physical_reduced c A d Δ γ hc W₀ w₀₀ v₀₀ W w₀ v₀
    (C + 2 * c + 2 * A + 66) (e + d + 1) (f + 1)
  intro V E _ _ _ _ G n hcommon hlower hupper hrep
  obtain ⟨T22₀, T22, R, hW₀, hW, hR, h0, hRC⟩ := hprem G n hcommon hlower hupper hrep
  set w := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hw
  set t := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with ht
  set I := (2 * c + 2 * A + 64) * (w + 1) ^ (d + 1) * t with hI
  have hinst : ∀ j, j < ETHTailGrowth.repetitions c A d n →
      installBoundP G c (EffectiveIteration.sourceDepth n) j ≤ I := fun j hj =>
    install_clock G c A d Δ n γ hcommon hlower hupper hrep j hj
  refine ⟨T22₀, T22, R + I + 1, hW₀, hW, ?_, ?_, ?_⟩
  · intro j hj1 hj2
    have h1 := hR j hj1 hj2
    have h2 := hinst j hj2
    omega
  · have h2 := hinst 0 (by omega)
    set B := C * (w + 1) ^ e * t ^ f with hB
    set Z := (w + 1) ^ (e + d + 1) * t ^ (f + 1) with hZ
    have ht1 : 1 ≤ t := one_le_table _ _
    have hBZ : B ≤ C * Z := by
      have h1 : 1 ≤ (w + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
      calc B = C * (w + 1) ^ e * t ^ f * 1 * 1 := by rw [hB]; ring
        _ ≤ C * (w + 1) ^ e * t ^ f * (w + 1) ^ (d + 1) * t :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) ht1
        _ = C * Z := by rw [hZ]; ring
    have hIZ : I ≤ (2 * c + 2 * A + 64) * Z := by
      have h1 : 1 ≤ (w + 1) ^ e := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ t ^ f := Nat.one_le_pow _ _ ht1
      calc I = (2 * c + 2 * A + 64) * (w + 1) ^ (d + 1) * t * 1 * 1 := by rw [hI]; ring
        _ ≤ (2 * c + 2 * A + 64) * (w + 1) ^ (d + 1) * t * (w + 1) ^ e * t ^ f :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
        _ = (2 * c + 2 * A + 64) * Z := by rw [hZ]; ring
    have hgoal : (C + 2 * c + 2 * A + 66) * (w + 1) ^ (e + d + 1) * t ^ (f + 1) =
        C * Z + (2 * c + 2 * A + 64) * Z + 2 * Z := by rw [hZ]; ring
    rw [hgoal]
    omega
  · set B := C * (w + 1) ^ e * t ^ f with hB
    set Z := (w + 1) ^ (e + d + 1) * t ^ (f + 1) with hZ
    have ht1 : 1 ≤ t := one_le_table _ _
    have hZ1 : 1 ≤ Z := Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega)) (Nat.one_le_pow _ _ ht1)
    have hBZ : B ≤ C * Z := by
      have h1 : 1 ≤ (w + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
      calc B = C * (w + 1) ^ e * t ^ f * 1 * 1 := by rw [hB]; ring
        _ ≤ C * (w + 1) ^ e * t ^ f * (w + 1) ^ (d + 1) * t :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) ht1
        _ = C * Z := by rw [hZ]; ring
    have hIZ : I ≤ (2 * c + 2 * A + 64) * Z := by
      have h1 : 1 ≤ (w + 1) ^ e := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ t ^ f := Nat.one_le_pow _ _ ht1
      calc I = (2 * c + 2 * A + 64) * (w + 1) ^ (d + 1) * t * 1 * 1 := by rw [hI]; ring
        _ ≤ (2 * c + 2 * A + 64) * (w + 1) ^ (d + 1) * t * (w + 1) ^ e * t ^ f :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
        _ = (2 * c + 2 * A + 64) * Z := by rw [hZ]; ring
    have hgoal : (C + 2 * c + 2 * A + 66) * (w + 1) ^ (e + d + 1) * t ^ (f + 1) =
        C * Z + (2 * c + 2 * A + 64) * Z + 2 * Z := by rw [hZ]; ring
    rw [hgoal]
    omega

/-- The same with the endpoint's source-constant hypotheses in place of `hc`. -/
theorem hb2_physical_source [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (c A d Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (C e f : ℕ)
    (hprem : ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      ∃ T22₀ T22 R : ℕ,
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
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 ≤ R) ∧
        level0BoundP (CutoffBitMachine.actualMachine c A d) G n c T22₀ ≤
          C * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ e *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ f ∧
        R ≤ C * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ e *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ f) :
    PhysicalLevelRun.HB2Physical c A d Δ γ :=
  hb2_physical_rounds c A d Δ γ (hc_of_source hΔ hγ hγone hsource) W₀ w₀₀ v₀₀ W w₀ v₀ C e f hprem

#print axioms installBoundP_eq
#print axioms install_clock
#print axioms hb2_physical_rounds
#print axioms hb2_physical_source

end
end EthInapproximability.CurrentPaper.ClockB
