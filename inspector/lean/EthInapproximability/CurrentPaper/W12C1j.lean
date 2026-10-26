import EthInapproximability.CurrentPaper.W12Ready0
import EthInapproximability.CurrentPaper.LevelJPrep

/-! Lane owner:b-weighted-level-12, segment 1 (piece): the start-bank sum of the level-`j` charged clear.
Every cell of the admitted scalar start bank `WeightedRawRowsSource.initialBank P g noW` is at most
`wordSize P + |enc g| + 1` (layer by layer through the admitted `bank`/`Sum.elim` definitions, with the admitted
`BankBound` lemmas); hence every cleared cell of `LevelJRows.C1j` is, when the master `N` cell is blank. -/

namespace EthInapproximability.CurrentPaper.W12C1j

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open MatrixWeightedEntryEnvelope BitMachineStackEmbedding

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem blank_bb (α : Type*) (K : ℕ) : BankBound (fun _ : α => ([] : List Bool)) K :=
  fun _ => Nat.zero_le _

theorem noW_bb (K : ℕ) : BankBound WeightedRawWords.noW K := fun _ => Nat.zero_le _

theorem initial_bb (P : Parameters.Input) :
    BankBound (ETHScaleGlobalLog.initial P) (ETHParameterScaleMachineInput.wordSize P) := by
  intro k
  rcases k with k | k
  · fin_cases k <;>
      simp [ETHScaleGlobalLog.initial, ETHParameterScaleMachineInput.words,
        ETHParameterScaleMachineInput.wordSize] <;> omega
  · simp [ETHScaleGlobalLog.initial]

theorem guarded_bb (w : List Bool) :
    BankBound (SourceNormalizationMachineDecode.guardedStart w).stk w.length := by
  intro k
  rcases k with k | k
  · fin_cases k <;>
      simp [SourceNormalizationMachineDecode.guardedStart, SourceNormalizationMachineDecode.cfg,
        SourceNormalizationMachineField.Data.stacks]
  · fin_cases k <;>
      simp [SourceNormalizationMachineDecode.guardedStart, SourceNormalizationMachineDecode.cfg]

/-- **Every cell of the admitted scalar start bank.** -/
theorem IB_bb (P : Parameters.Input) (g : EncodedGraph.Graph) :
    BankBound (WeightedRawRowsSource.initialBank P g WeightedRawWords.noW)
      (ETHParameterScaleMachineInput.wordSize P + (EncodedGraph.encode g).length + 1) := by
  have hI : BankBound (ETHScaleGlobalLog.initial P)
      (ETHParameterScaleMachineInput.wordSize P + (EncodedGraph.encode g).length + 1) :=
    bankBound_mono _ (initial_bb P) (by omega)
  have hG : BankBound (SourceNormalizationMachineDecode.guardedStart (true :: EncodedGraph.encode g)).stk
      (ETHParameterScaleMachineInput.wordSize P + (EncodedGraph.encode g).length + 1) :=
    bankBound_mono _ (guarded_bb _) (by simp)
  unfold WeightedRawRowsSource.initialBank WeightedScalarComplete.initialBank
    WeightedActualSizeSuffix.initialBank WeightedMTPrefix.initialBank WeightedPrefixAT.initialBank
    WeightedScaleDerivedFromBins.initialBank WeightedBinsGraphQ.initialBank WeightedBinsGraphQ.base
    WeightedGraphQJoined.initialBank WeightedGraphQJoined.lift GraphVertexPreludeJoin.parserStart
    BitMachineStackEmbedding.stackCfg WeightedBinsGeneric.initialBank WeightedBinsGeneric.foreignBank
    ETHBinsJoinedScratch.initialBank ETHScaleActualComplete.initialBank
  repeat' (first
    | exact hI
    | exact hG
    | exact noW_bb _
    | exact blank_bb _ _
    | apply bankBound_sumElim
    | apply bankBound_embedded)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Every cleared cell of the level start bank `C1j`** (master `N` blank). -/
theorem C1j_clear_le (G : EndpointGraph V E) (c b y i : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) (hN : mS .N = []) (k : Fin WeightedLevel0Clean.nClear) :
    (LevelJRows.C1j G c b y i Mx mS (WeightedLevel0Clean.clearCells k)).length ≤
      ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters G c b y i Mx) +
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 := by
  obtain ⟨z, hz⟩ := (WeightedLevel0Clean.clearCells_iff (WeightedLevel0Clean.clearCells k)).1 ⟨k, rfl⟩
  rw [← hz]
  rcases z with ⟨x, hx⟩ | j | u
  · show (LevelJRows.C1j G c b y i Mx mS (WeightedLevel0Rows.rawEmb (Sum.inl x))).length ≤ _
    unfold LevelJRows.C1j
    rw [bank_at]
    exact IB_bb _ _ x
  · show (LevelJRows.C1j G c b y i Mx mS (Sum.inr (Sum.inl j))).length ≤ _
    unfold LevelJRows.C1j
    rw [bank_outside _ _ _ _ (by
      rintro ⟨w, hw⟩
      rcases w with w | w <;> cases hw)]
    simp
  · show (LevelJRows.C1j G c b y i Mx mS (WeightedLevel0Rows.rawEmb (Sum.inr .N))).length ≤ _
    unfold LevelJRows.C1j
    rw [bank_at]
    simp [hN]

theorem C1j_sum_le (G : EndpointGraph V E) (c b y i : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) (hN : mS .N = []) :
    (∑ k : Fin WeightedLevel0Clean.nClear,
        (LevelJRows.C1j G c b y i Mx mS (WeightedLevel0Clean.clearCells k)).length) ≤
      WeightedLevel0Clean.nClear *
        (ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters G c b y i Mx) +
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) := by
  calc (∑ k : Fin WeightedLevel0Clean.nClear,
        (LevelJRows.C1j G c b y i Mx mS (WeightedLevel0Clean.clearCells k)).length)
      ≤ ∑ _k : Fin WeightedLevel0Clean.nClear,
          (ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters G c b y i Mx) +
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) :=
        Finset.sum_le_sum (fun k _ => C1j_clear_le G c b y i Mx mS hN k)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

#print axioms initial_bb
#print axioms guarded_bb
#print axioms IB_bb
#print axioms C1j_clear_le
#print axioms C1j_sum_le

end
end EthInapproximability.CurrentPaper.W12C1j
