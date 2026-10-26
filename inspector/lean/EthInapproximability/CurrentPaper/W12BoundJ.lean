import EthInapproximability.CurrentPaper.W12RowTime
import EthInapproximability.CurrentPaper.ClockK
import EthInapproximability.CurrentPaper.EntryClockPoly3Uniform

/-! Lane owner:b-weighted-level-12, segment 1 (piece): the admitted level-row clock
`LevelJClean.boundJ` (= `publicBound15` part + `rowTime` part, the core of `cleanBoundJ` / `readyBoundJ`)
at every physical level `j < k`, polynomially in `|w| + 1` and `tableSize`.

* `publicBound15` part: lane entry-clock-3's level-generic `hP15` (`PolyIn U`), the level size `U` bounded by
  the naming premise of `naming_at_levels`, `EntryClockPoly.absorb`, owner-11's `translate_packet`.
* `rowTime` part: `W12RowTime.rowTime_level` (`≤ Krow (preparedEnvelope + 1)^9`) and owner-11's
  `ClockK.level_envelope`.
-/

namespace EthInapproximability.CurrentPaper.W12BoundJ

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem dI_binBase (i : LI) :
    (ProtectedFullBankBridgeScratch.actualD i.G i.c i.b i.y i.lv i.M).binBase =
      MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) := rfl
theorem dI_rawWidth (i : LI) :
    (ProtectedFullBankBridgeScratch.actualD i.G i.c i.b i.y i.lv i.M).rawWidth =
      MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i) := rfl
theorem dI_s (i : LI) : (ProtectedFullBankBridgeScratch.actualD i.G i.c i.b i.y i.lv i.M).s = sI i := rfl
theorem noW_eq' : WeightedRawWords.noW = noW3 := rfl

/-- The `publicBound15` summand of `boundJ`, literally, at a level `i`. -/
def pbJ (i : LI) : ℕ :=
  WeightedLevelFields15.publicBound15 (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M)
    (EncodedETHSource.serializeGraph i.G) (Fintype.card i.E) WeightedRawWords.noW
    (Parameters.firstExponent (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M))
    (Parameters.bins (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M))
    (ParameterizedNP.GuardedSourceSlab.q2 i.G (Parameters.bins (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M)))
    (PrimeSampler.size (ParameterizedNP.GuardedSourceSlab.q2 i.G
        (Parameters.bins (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M)))
      (Parameters.balanceOrder (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M))
      (Construction.qOne (Parameters.firstExponent (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M)) *
        (Iteration.stepParameters i.G i.c i.b i.y i.lv i.M).rows))
    (ProtectedFullBankBridgeScratch.actualD i.G i.c i.b i.y i.lv i.M).binBase
    (ProtectedFullBankBridgeScratch.actualD i.G i.c i.b i.y i.lv i.M).rawWidth
    (ProtectedFullBankBridgeScratch.actualD i.G i.c i.b i.y i.lv i.M).s

theorem pbJ_poly : PolyIn U pbJ := by
  refine PolyIn.mono (fun i => le_of_eq ?_) hP15
  unfold pbJ
  rw [dI_binBase, dI_rawWidth, dI_s, noW_eq']

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `boundJ` splits literally into its `publicBound15` and `rowTime` parts; `ps` is the
closed controller constant `perStep WeightedLevelFields15.program` exactly as elaborated inside `boundJ`
(assigned by unification, so no instance is restated). -/
theorem boundJ_split : ∃ ps : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c b y j : ℕ) (M : Iteration.Matrix),
    LevelJClean.boundJ G c b y j M =
      pbJ ⟨V, E, G, c, b, y, j, M⟩ + (9 * (ps * pbJ ⟨V, E, G, c, b, y, j, M⟩) + 9 + 2) +
        WeightedRowFields.rowTime (Fintype.card V) (4 * Iteration.s G c b y j M)
          (ProtectedFullBankBridgeScratch.actualD G c b y j M).nb
          (ProtectedFullBankBridgeScratch.actualD G c b y j M).stagePrefixRows
          (ProtectedFullBankBridgeScratch.actualD G c b y j M).rx
          (ProtectedFullBankBridgeScratch.actualD G c b y j M).binBase
          (ProtectedFullBankBridgeScratch.actualD G c b y j M).rawWidth
          (ProtectedFullBankBridgeScratch.actualD G c b y j M).uniform + 2 :=
  ⟨_, fun {V E} _ _ _ _ G c b y j M => rfl⟩

/-- **The `publicBound15` part at every physical level `j < k`** (absolute `Cp`). -/
theorem pbJ_level : ∃ Cp : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    ∀ j, j < ETHTailGrowth.repetitions c A d n →
    pbJ ⟨V, E, G, c, EffectiveIteration.sourceDepth n, StepP.yP G c (EffectiveIteration.sourceDepth n) j, j,
        StepP.MP G c (EffectiveIteration.sourceDepth n) j⟩ ≤
      2 * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp := by
  obtain ⟨K, D, hKD⟩ := pbJ_poly
  refine ⟨K + 2 * 2 * D, fun {V E} _ _ _ _ G c A d Δ n γ hcommon hlower hupper hrep j hj => ?_⟩
  let i : LI := ⟨V, E, G, c, EffectiveIteration.sourceDepth n, StepP.yP G c (EffectiveIteration.sourceDepth n) j, j,
    StepP.MP G c (EffectiveIteration.sourceDepth n) j⟩
  have h1 := hKD i
  have hname := naming_at_levels G c A d Δ n γ hcommon hlower hupper hrep j hj
  set p := n / (2 * ETHTailGrowth.repetitions c A d n) with hp_def
  have h128 := (EffectiveIteration.parameter_size_bounds (Iteration.stepParameters G c
    (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
    (StepP.MP G c (EffectiveIteration.sourceDepth n) j))).1
  rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
  have hU : U i ≤ 2 ^ (1 * p) * (n + ell3 G + 1) ^ 1 := by
    unfold U
    rw [one_mul, pow_one]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hname) (by
      show ell3 G + 1 ≤ n + ell3 G + 1
      omega)
  have hell := card_le_ell3 G
  have hp : 1 ≤ p := by
    have : 1 ≤ Parameters.balanceOrder (Iteration.stepParameters G c
      (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hab := EntryClockPoly.absorb K D 1 1 (n + ell3 G + 1) p (U i) (by omega) hp hU
  have e : (K + 2 * (1 + 1) * D) * p = (K + 2 * 2 * D) * p := by ring
  have hX1 : 1 ≤ n + ell3 G + 1 := by omega
  have hmono : (n + ell3 G + 1) ^ (K + 2 * 1 * D) ≤ (n + ell3 G + 1) ^ (K + 2 * 2 * D) :=
    Nat.pow_le_pow_right hX1 (by omega)
  rw [e] at hab
  have hexp : FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n = p := by
    rw [hp_def]; unfold FinalPadding.exponent; rw [max_eq_right hrep]
  have hfin : pbJ i ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ (K + 2 * 2 * D) +
      2 ^ ((K + 2 * 2 * D) * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n) := by
    rw [hexp]
    exact h1.trans (hab.trans (Nat.add_le_add_right hmono _))
  exact ClockH.translate_packet G (ETHTailGrowth.repetitions c A d) n _ _ hfin

/-- **The level-row clock `boundJ` at every physical level `j < k`**: explicit polynomial in
`a = |w| + 1` and `T = tableSize` (`Cp` absolute from `pbJ_level`; `KE c A` from owner-11's `ClockK`). -/
theorem boundJ_level : ∃ Cp ps : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    ∀ j, j < ETHTailGrowth.repetitions c A d n →
    LevelJClean.boundJ G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤
      (1 + 9 * ps) * (2 * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) + 13 +
      W12RowTime.Krow * (ClockK.KE c A * ((((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
        (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) + 1) ^ 9 := by
  obtain ⟨Cp, hCp⟩ := pbJ_level
  obtain ⟨ps, hps⟩ := boundJ_split
  refine ⟨Cp, ps, fun {V E} _ _ _ _ G c A d Δ n γ hcommon hlower hupper hrep j hj => ?_⟩
  rw [hps]
  have hpb := hCp G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hrt := W12RowTime.rowTime_level G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
  have hen := ClockK.level_envelope G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hrt' := hrt.trans (Nat.mul_le_mul_left W12RowTime.Krow
    (Nat.pow_le_pow_left (Nat.add_le_add_right hen 1) 9))
  generalize (pbJ (⟨V, E, G, c, EffectiveIteration.sourceDepth n, StepP.yP G c (EffectiveIteration.sourceDepth n) j, j,
      StepP.MP G c (EffectiveIteration.sourceDepth n) j⟩ : LI)) = x at hpb ⊢
  generalize (2 * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) = B at hpb ⊢
  have h9 : 9 * (ps * x) ≤ 9 * (ps * B) := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left ps hpb)
  have e : (1 + 9 * ps) * B = B + 9 * (ps * B) := by ring
  rw [e]
  omega

#print axioms dI_binBase
#print axioms pbJ_poly
#print axioms boundJ_split
#print axioms pbJ_level
#print axioms boundJ_level

end
end EthInapproximability.CurrentPaper.W12BoundJ
