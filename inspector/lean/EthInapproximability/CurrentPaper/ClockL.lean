import EthInapproximability.CurrentPaper.ClockK

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 (fifth piece): the bridge-start stack
lengths of `ProtectedFullBankBridgeScratch.actualPhysicalStart` (the `nB` sum of `roundBoundP` /
`level0BoundP`).

Every cell of the admitted physical start is at most the admitted `preparedEnvelope`
(`start_cell_le`): the writer region is the admitted writer start (owner-5
`OuterStartBank.actualPhysicalStart_writer`: persistent entry bank, the embedded order-preparation
operands `|V|, s-3, 4s`, unary `rows`, `cols`), the outer region is owner-5's closed form
`OuterStartBank.outerTarget` (unary `scale`, and unary `nextDepth`, `sourceConstant`, `bins`, `0`).
At a physical level `j < k` the whole `nB` summand of the round clocks is then
`≤ nB (KE + perStep bridgeH · coefficient · KE^18) Z^36` (`level_stacks`). -/

namespace EthInapproximability.CurrentPaper.ClockL

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedEntryEnvelope

noncomputable section

theorem outer_cell_le (b c s lam : ℕ) (o : MatrixTableInterlaceProtectedBridge.OStack) :
    (OuterStartBank.outerTarget b c s lam o).length ≤ lam + b + c + s := by
  rcases o with o | (o | o)
  · by_cases h : o = MatrixOuterWidthMachine.inputStack
    · subst h
      show ((MatrixOuterWidthMachine.startCfg lam).stk MatrixOuterWidthMachine.inputStack).length ≤ _
      rw [MatrixOuterWidthMachine.startCfg_input]
      simp only [MatrixOuterWidthMachine.unary, List.length_replicate]
      omega
    · show ((MatrixOuterWidthMachine.startCfg lam).stk o).length ≤ _
      rw [MatrixOuterWidthMachine.startCfg_other_empty lam o h]
      simp
  · rcases o with k | k
    · show ((MatrixRestorationWidthMachine.startCfg b c s 0).stk (.inl k)).length ≤ _
      change (MatrixRestorationWidthMachineProduct.inputBank b c s 0
        ((Fintype.equivFin (Fin 12)).symm k)).length ≤ _
      generalize (Fintype.equivFin (Fin 12)).symm k = m
      fin_cases m <;> simp [MatrixRestorationWidthMachineProduct.inputBank,
        MatrixRestorationWidthMachineProduct.unary] <;> omega
    · show ((MatrixRestorationWidthMachine.startCfg b c s 0).stk (.inr k)).length ≤ _
      rw [MatrixRestorationWidthMachine.startCfg_post_empty]
      simp
  · show ([] : List Bool).length ≤ _
    simp

theorem outerSize_ge (R r rows cols b c s lam : ℕ) :
    lam + b + c + s ≤ ProtectedBudgetNormalizationScratch.outerSize R r rows cols b c s lam := by
  unfold ProtectedBudgetNormalizationScratch.outerSize
  dsimp only
  generalize 2 ^ r = W
  generalize 2 ^ R = B
  generalize W * rows = X
  generalize cols ^ W = Y
  generalize X ^ B = XB
  generalize B * Y = BY
  generalize X * Y = XY
  generalize Y * X = YX
  generalize BY * XB = BYXB
  generalize rows * cols = RC
  omega

theorem ready_cell_le (bank : Fin 64 → List Bool) (r c K : ℕ) (hB : BankBound bank K)
    (hr : r ≤ K) (hc : c ≤ K) (w : MatrixTableWriter.Stack 64) :
    ((MatrixTableWriter.ready bank r c 0 0 0 0 [] []).contents w).length ≤ K := by
  rcases w with (k | k) | e
  · exact hB k
  · show ((![List.replicate 0 true, List.replicate 0 true, []] : Fin 3 → List Bool) k).length ≤ K
    fin_cases k <;> simp
  · cases e <;>
      first
      | (show (List.replicate r true).length ≤ K; simp only [List.length_replicate]; omega)
      | (show (List.replicate c true).length ≤ K; simp only [List.length_replicate]; omega)
      | (show (List.replicate 0 true).length ≤ K; simp)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

open ProtectedFullBankBridgeScratch in
theorem writer_cell_le (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix)
    (w : MatrixTableInterlaceProtectedBridge.WStack) :
    ((actualWriterStart G c b y j M).stk w).length ≤
      inputScale (actualD G c b y j M) (actualRows G c b y j M) (actualCols G c b y j M) +
        Fintype.card V + 4 * Iteration.s G c b y j M + actualRows G c b y j M +
        actualCols G c b y j M := by
  set K := inputScale (actualD G c b y j M) (actualRows G c b y j M) (actualCols G c b y j M) +
        Fintype.card V + 4 * Iteration.s G c b y j M + actualRows G c b y j M +
        actualCols G c b y j M with hK
  have hP : BankBound (MatrixWeightedEntryController.persistentBank (actualD G c b y j M)) K :=
    bankBound_mono _ (bankBound_persistent (actualD G c b y j M) (actualRows G c b y j M)
      (actualCols G c b y j M)) (by omega)
  have hI : BankBound (MatrixWeightedCanonicalOrderMachine.initialBank (Fintype.card V)
      (Iteration.s G c b y j M - 3) (4 * Iteration.s G c b y j M)) K := by
    intro m
    fin_cases m <;> simp [MatrixWeightedCanonicalOrderMachine.initialBank] <;> omega
  have hB : BankBound (MatrixWeightedOrderPreparation.sourceBank
      (MatrixWeightedEntryController.persistentBank (actualD G c b y j M)) (Fintype.card V)
      (Iteration.s G c b y j M - 3) (4 * Iteration.s G c b y j M)) K :=
    bankBound_embedded _ _ _ K hP hI
  show ((MatrixTableWriter.ready (MatrixWeightedOrderPreparation.sourceBank
      (MatrixWeightedEntryController.persistentBank (actualD G c b y j M)) (Fintype.card V)
      (Iteration.s G c b y j M - 3) (4 * Iteration.s G c b y j M))
      (actualRows G c b y j M) (actualCols G c b y j M) 0 0 0 0 [] []).contents w).length ≤ K
  exact ready_cell_le _ _ _ K hB (by omega) (by omega) w

open ProtectedFullBankBridgeScratch in
theorem start_cell_le (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix)
    (x : MatrixTableInterlaceProtectedBridge.Stack) :
    ((actualPhysicalStart G c b y j M).stk x).length ≤
      ProtectedBudgetNormalizationScratch.preparedEnvelope G c b y j M := by
  have hE : ProtectedBudgetNormalizationScratch.preparedEnvelope G c b y j M =
      1 + Fintype.card V + (Iteration.s G c b y j M - 3) + 4 * Iteration.s G c b y j M +
        actualRows G c b y j M + actualCols G c b y j M +
        inputScale (actualD G c b y j M) (actualRows G c b y j M) (actualCols G c b y j M) +
        ProtectedBudgetNormalizationScratch.outerSize (Iteration.rQ G c b y j M)
          (Iteration.rq G c b y j M) (actualRows G c b y j M) (actualCols G c b y j M) b c
          (Parameters.bins (Iteration.stepParameters G c b y j M))
          (Parameters.scale (Iteration.stepParameters G c b y j M)) := rfl
  have hos := outerSize_ge (Iteration.rQ G c b y j M) (Iteration.rq G c b y j M)
    (actualRows G c b y j M) (actualCols G c b y j M) b c
    (Parameters.bins (Iteration.stepParameters G c b y j M))
    (Parameters.scale (Iteration.stepParameters G c b y j M))
  rcases x with w | o
  · rw [OuterStartBank.actualPhysicalStart_writer]
    have := writer_cell_le G c b y j M w
    omega
  · rw [OuterStartBank.actualPhysicalStart_outer]
    have := outer_cell_le b c (Parameters.bins (Iteration.stepParameters G c b y j M))
      (Parameters.scale (Iteration.stepParameters G c b y j M)) o
    omega

open ProtectedFullBankBridgeScratch in
theorem level_stacks [Fintype OuterLevel0Bridge.BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    (∑ i : Fin Level0CleanRun.nB,
        (((actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
            (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).stk
              ((Fintype.equivFin OuterLevel0Bridge.BStack).symm i)).length +
          BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
            actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
              (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
              (StepP.MP G c (EffectiveIteration.sourceDepth n) j))) ≤
      Level0CleanRun.nB * (ClockK.KE c A + BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)) *
        (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ 36 := by
  have hEnv := ClockK.level_envelope G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hBud := ClockK.level_budget G c A d Δ n γ hcommon hlower hupper hrep j hj
  set Z := ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hZ
  have hZ1 : 1 ≤ Z := Nat.mul_pos (Nat.one_le_pow _ _ (by omega)) (ClockH.table_pos _ n)
  have hZ2 : Z * Z ≤ Z ^ 36 := by
    rw [← pow_two]; exact Nat.pow_le_pow_right hZ1 (by norm_num)
  have hEZ : ProtectedBudgetNormalizationScratch.preparedEnvelope G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤ ClockK.KE c A * Z ^ 36 :=
    le_trans hEnv (Nat.mul_le_mul_left _ hZ2)
  set p := BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH with hp
  have hterm : ∀ i : Fin Level0CleanRun.nB,
      ((actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
            (StepP.MP G c (EffectiveIteration.sourceDepth n) j)).stk
              ((Fintype.equivFin OuterLevel0Bridge.BStack).symm i)).length +
          p * actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
              (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
              (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤
        (ClockK.KE c A + p * (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)) *
          Z ^ 36 := by
    intro i
    have h1 := start_cell_le G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ((Fintype.equivFin OuterLevel0Bridge.BStack).symm i)
    have h2 := Nat.mul_le_mul_left p hBud
    have e : (ClockK.KE c A + p * (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)) *
          Z ^ 36 = ClockK.KE c A * Z ^ 36 +
            p * (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18 * Z ^ 36) := by ring
    rw [e]
    omega
  calc _ ≤ ∑ _i : Fin Level0CleanRun.nB,
        (ClockK.KE c A + p * (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)) *
          Z ^ 36 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

#print axioms outer_cell_le
#print axioms writer_cell_le
#print axioms start_cell_le
#print axioms level_stacks

end
end EthInapproximability.CurrentPaper.ClockL
