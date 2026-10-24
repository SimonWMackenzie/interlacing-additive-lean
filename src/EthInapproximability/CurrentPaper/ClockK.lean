import EthInapproximability.CurrentPaper.ClockJ

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 (fourth piece): the bridge envelope and
the admitted bridge budget at every physical round level `j < k`, in the shape
`C (|w|+1)^e tableSize^f`. -/

namespace EthInapproximability.CurrentPaper.ClockK

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

noncomputable section

/-- The envelope constant (depends on the machine constants `c`, `A` only). -/
def KE (c A : ℕ) : ℕ := 16777216 + ClockC.binsConst + 5 * c + 5 * A + 3400

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem card_V_le (G : EndpointGraph V E) (n : ℕ) :
    Fintype.card V ≤ (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length := by
  have h := EncodedGraph.encode_length_lower (EncodedETHSource.serializeGraph G)
  have h2 := SourceOriginalBranchPackets.packet_length n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have h3 : (EncodedETHSource.serializeGraph G).vertices = Fintype.card V := rfl
  omega

open ProtectedFullBankBridgeScratch in
theorem level_envelope (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    ProtectedBudgetNormalizationScratch.preparedEnvelope G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤
      KE c A * ((((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
        (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) := by
  set b := EffectiveIteration.sourceDepth n with hb
  set wl := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length with hwl
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hT
  set P := actualP G c b (StepP.yP G c b j) j (StepP.MP G c b j) with hP
  set O := (actualPhysicalOutput G c b (StepP.yP G c b j) j (StepP.MP G c b j)).length with hO
  have he : ProtectedBudgetNormalizationScratch.preparedEnvelope G c b (StepP.yP G c b j) j
      (StepP.MP G c b j) ≤ Fintype.card V + Parameters.scale P + P.nextDepth + P.sourceConstant +
        Parameters.bins P + 200 * (O * O) :=
    ClockJ.envelope_le G c b (StepP.yP G c b j) j (StepP.MP G c b j)
  have hOT : O < 4 * T := ClockE.level_output G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hSB : Parameters.scaleBound P ≤ c + 2 * n + 8 * T + A * (wl + 1) ^ (d + 1) + 3 :=
    ClockC.level_scaleBound G c A d Δ n γ hcommon hlower hupper hrep j (le_of_lt hj)
  have hsc := ClockC.scale_le P
  have hbi := ClockC.bins_le P
  have hsrc : P.sourceConstant ≤ Parameters.scaleBound P := le_max_left _ _
  have hnd : P.nextDepth ≤ Parameters.scaleBound P :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hV : Fintype.card V ≤ wl := card_V_le G n
  have hpl : wl = 2 * (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length) + 2 :=
    SourceOriginalBranchPackets.packet_length n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hnw : n ≤ wl := by omega
  have hT1 : 1 ≤ T := ClockH.table_pos _ n
  set Q := (wl + 1) ^ (d + 1) with hQ
  have hQw : wl + 1 ≤ Q := by
    calc wl + 1 = (wl + 1) ^ 1 := (pow_one _).symm
      _ ≤ (wl + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hZQ : Q ≤ Q * T := Nat.le_mul_of_pos_right _ hT1
  have hZT : T ≤ Q * T := Nat.le_mul_of_pos_left _ (by omega)
  set Z := Q * T with hZ
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z * Z := Nat.le_mul_of_pos_left _ hZ1
  have hZZ1 : 0 < Z * Z := by omega
  have hAQ : A * Q ≤ A * (Z * Z) := Nat.mul_le_mul_left _ (by omega)
  have hTT : T * T ≤ Z * Z := Nat.mul_le_mul hZT hZT
  have hOO : O * O ≤ 16 * (T * T) := by
    have := Nat.mul_le_mul (le_of_lt hOT) (le_of_lt hOT)
    calc O * O ≤ 4 * T * (4 * T) := this
      _ = 16 * (T * T) := by ring
  have hbc : ClockC.binsConst ≤ ClockC.binsConst * (Z * Z) := Nat.le_mul_of_pos_right _ hZZ1
  have hcc : c ≤ c * (Z * Z) := Nat.le_mul_of_pos_right _ hZZ1
  have e : KE c A * (Z * Z) = 16777216 * (Z * Z) + ClockC.binsConst * (Z * Z) + 5 * (c * (Z * Z)) +
      3400 * (Z * Z) + 5 * (A * (Z * Z)) := by unfold KE; ring
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  rw [h24] at hsc
  rw [e]
  omega

open ProtectedFullBankBridgeScratch in
theorem level_budget (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤
      ProtectedBudgetNormalizationScratch.coefficient * KE c A ^ 18 *
        (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ 36 := by
  have h1 := ProtectedBudgetNormalizationScratch.actualPhysicalBudget_prepared_polynomial G c
    (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
    (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have h2 := level_envelope G c A d Δ n γ hcommon hlower hupper hrep j hj
  set Z := ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hZ
  have h3 := Nat.mul_le_mul_left ProtectedBudgetNormalizationScratch.coefficient (Nat.pow_le_pow_left h2 18)
  calc _ ≤ _ := h1
    _ ≤ _ := h3
    _ = _ := by ring

#print axioms card_V_le
#print axioms level_envelope
#print axioms level_budget

end
end EthInapproximability.CurrentPaper.ClockK
