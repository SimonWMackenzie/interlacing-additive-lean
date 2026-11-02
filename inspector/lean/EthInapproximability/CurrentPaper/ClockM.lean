import EthInapproximability.CurrentPaper.ClockL

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 / 5 (reduction): `HB2Physical` for ONE
fixed machine from the writer-22 specs, the entry-clock polynomial premises on `T22₀`, `T22` (in the
exact form `(n + |enc G| + 1)^C + 2^(C p)`, `p = exponent`), and polynomial premises on the two
remaining round-clock components `prepBound`/`prepBoundJ` and `dimsBound` ONLY.

Every other component of `roundBoundP` / `level0BoundP` is majorized here from the checked pieces:
the cost-update clock (`ClockD.level_costBound`), the matrix and output words (`ClockE`), the bridge
budget (`ClockK.level_budget`), the bridge-start stacks with the `perStep bridgeH` factor
(`ClockL.level_stacks`), and `T22`, `T22₀` via `ClockH.translate_packet`; the round majorant and
the install/emission/fuel clocks come from owner-10's `ClockB.hb2_physical_source`. -/

namespace EthInapproximability.CurrentPaper.ClockM

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open FuelShell Emission HB2Machine ClockA ClockB

noncomputable section

set_option maxHeartbeats 3000000

/-! ## Arithmetic -/

theorem split_le (a t e f m : ℕ) (ha : 1 ≤ a) (ht : 1 ≤ t) (hm : e + f ≤ m) :
    a ^ e * t ^ f ≤ (a * t) ^ m :=
  calc a ^ e * t ^ f ≤ (a * t) ^ e * (a * t) ^ f :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right a ht) e)
          (Nat.pow_le_pow_left (Nat.le_mul_of_pos_left t ha) f)
    _ = (a * t) ^ (e + f) := (pow_add _ _ _).symm
    _ ≤ (a * t) ^ m := Nat.pow_le_pow_right (Nat.mul_pos ha ht) hm

theorem round_arith (P T22 cost dims bud mw out S nB Ym Cx Kc Kb Ks : ℕ)
    (hP : P ≤ Cx * Ym) (hT : T22 ≤ 2 * Ym) (hc : cost ≤ Kc * Ym) (hd : dims ≤ Cx * Ym)
    (hb : bud ≤ Kb * Ym) (hmw : mw ≤ 4 * Ym) (ho : out ≤ 4 * Ym) (hS : S ≤ Ks * Ym)
    (hn : nB ≤ nB * Ym) (h1 : 1 ≤ Ym) :
    (P + (T22 + (cost + (dims + bud + 1) + 1) + 1) + 1) +
        ((mw + 1 + 2) + ((2 * out + 2) + (S + nB + 2) + 1) + 1) + 1 ≤
      (2 * Cx + Kc + Kb + Ks + nB + 30) * Ym := by
  have e : (2 * Cx + Kc + Kb + Ks + nB + 30) * Ym =
      Cx * Ym + Cx * Ym + Kc * Ym + Kb * Ym + Ks * Ym + nB * Ym + 30 * Ym := by ring
  rw [e]; omega

theorem level0_arith (P T22 cost dims bud out S nB Ym Cx Kc Kb Ks : ℕ)
    (hP : P ≤ Cx * Ym) (hT : T22 ≤ 2 * Ym) (hc : cost ≤ Kc * Ym) (hd : dims ≤ Cx * Ym)
    (hb : bud ≤ Kb * Ym) (ho : out ≤ 4 * Ym) (hS : S ≤ Ks * Ym)
    (hn : nB ≤ nB * Ym) (h1 : 1 ≤ Ym) :
    (P + (T22 + (cost + (dims + bud + 1) + 1) + 1) + 1) +
        ((2 * out + 2) + (S + nB + 2) + 1) + 1 ≤
      (2 * Cx + Kc + Kb + Ks + nB + 30) * Ym := by
  have e : (2 * Cx + Kc + Kb + Ks + nB + 30) * Ym =
      Cx * Ym + Cx * Ym + Kc * Ym + Kb * Ym + Ks * Ym + nB * Ym + 30 * Ym := by ring
  rw [e]; omega

/-- The inner constant of the cost-update clock. -/
def Kin (c A : ℕ) : ℕ := 16777216 + ClockC.binsConst + 8 * c + 8 * A + 105

/-- The cost-update constant. -/
def Kcost (c A : ℕ) : ℕ := (2000000 * ClockD.Kc + 1000000) * Kin c A ^ 6

/-- The combined round-clock constant. -/
def Kround [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label] (c A Cx : ℕ) : ℕ :=
  2 * Cx + Kcost c A + ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18 +
    Level0CleanRun.nB * (ClockK.KE c A + BitMachineStackGrowth.perStep bridgeH *
      (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)) +
    Level0CleanRun.nB + 30

/-- The common exponent. -/
def mexp (d ex fx C22 : ℕ) : ℕ := 36 * (d + 1) + ex + fx + 2 * C22

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The shared per-instance majorizations (every level `j < k`). -/
theorem level_pieces (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (ex fx C22 : ℕ) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    let a := (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1
    let T := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n
    let Ym := (a * T) ^ mexp d ex fx C22
    1 ≤ Ym ∧ a ^ ex * T ^ fx ≤ Ym ∧ a ^ C22 * T ^ C22 ≤ Ym ∧ T ≤ Ym ∧
      (a ^ (d + 1) * T) ^ 36 ≤ Ym ∧
      costBound (Parameters.scale (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j))
          (EffectiveIteration.sourceDepth n) c
          (Parameters.bins (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j))
          (Fintype.card E)
          (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).cost ≤ Kcost c A * Ym := by
  intro a T Ym
  have ha : 1 ≤ a := by omega
  have hT : 1 ≤ T := ClockH.table_pos _ n
  have hY1 : 1 ≤ a * T := Nat.mul_pos ha hT
  have hm1 : 36 * (d + 1) ≤ mexp d ex fx C22 := by unfold mexp; omega
  have hY : 1 ≤ Ym := Nat.one_le_pow _ _ hY1
  refine ⟨hY, split_le a T ex fx _ ha hT (by unfold mexp; omega),
    split_le a T C22 C22 _ ha hT (by unfold mexp; omega), ?_, ?_, ?_⟩
  · calc T ≤ a * T := Nat.le_mul_of_pos_left _ ha
      _ = (a * T) ^ 1 := (pow_one _).symm
      _ ≤ Ym := Nat.pow_le_pow_right hY1 (by unfold mexp; omega)
  · have hZ : a ^ (d + 1) * T ≤ (a * T) ^ (d + 1) := by
      have := split_le a T (d + 1) 1 (d + 1 + 1) ha hT (by omega)
      rw [pow_one] at this
      calc a ^ (d + 1) * T ≤ a ^ (d + 1) * T ^ (d + 1) :=
            Nat.mul_le_mul_left _ (by
              calc T = T ^ 1 := (pow_one _).symm
                _ ≤ T ^ (d + 1) := Nat.pow_le_pow_right hT (by omega))
        _ = (a * T) ^ (d + 1) := (mul_pow _ _ _).symm
    calc (a ^ (d + 1) * T) ^ 36 ≤ ((a * T) ^ (d + 1)) ^ 36 := Nat.pow_le_pow_left hZ 36
      _ = (a * T) ^ (36 * (d + 1)) := by rw [← pow_mul, Nat.mul_comm (d + 1) 36]
      _ ≤ Ym := Nat.pow_le_pow_right hY1 hm1
  · have hcost := ClockD.level_costBound G c A d Δ n γ hcommon hlower hupper hrep j (le_of_lt hj)
    have hpl := SourceOriginalBranchPackets.packet_length n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
    set Y1 := (a * T) ^ (d + 1) with hY1d
    have hYd : 1 ≤ Y1 := Nat.one_le_pow _ _ hY1
    have hnY : n + 1 ≤ Y1 := by
      calc n + 1 ≤ a := by omega
        _ ≤ a * T := Nat.le_mul_of_pos_right _ hT
        _ = (a * T) ^ 1 := (pow_one _).symm
        _ ≤ Y1 := Nat.pow_le_pow_right hY1 (by omega)
    have hTY : T ≤ Y1 := by
      calc T ≤ a * T := Nat.le_mul_of_pos_left _ ha
        _ = (a * T) ^ 1 := (pow_one _).symm
        _ ≤ Y1 := Nat.pow_le_pow_right hY1 (by omega)
    have haY : a ^ (d + 1) ≤ Y1 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hT) _
    have hAY : A * a ^ (d + 1) ≤ A * Y1 := Nat.mul_le_mul_left _ haY
    have hbc : ClockC.binsConst ≤ ClockC.binsConst * Y1 := Nat.le_mul_of_pos_right _ hYd
    have hcc : c ≤ c * Y1 := Nat.le_mul_of_pos_right _ hYd
    have hinner : 2 ^ 24 + ClockC.binsConst + 8 * (c + 2 * n +
        8 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n +
        A * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) + 3) + 1 ≤
        Kin c A * Y1 := by
      have e : Kin c A * Y1 = 16777216 * Y1 + ClockC.binsConst * Y1 + 8 * (c * Y1) + 8 * (A * Y1) +
          105 * Y1 := by unfold Kin; ring
      have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      rw [e, h24]
      show 16777216 + ClockC.binsConst + 8 * (c + 2 * n + 8 * T + A * a ^ (d + 1) + 3) + 1 ≤ _
      omega
    have h6 := Nat.pow_le_pow_left hinner 6
    have hY6 : Y1 ^ 6 ≤ Ym := by
      rw [hY1d, ← pow_mul]
      exact Nat.pow_le_pow_right hY1 (by unfold mexp; omega)
    calc _ ≤ _ := hcost
      _ ≤ (2000000 * ClockD.Kc + 1000000) * (Kin c A * Y1) ^ 6 := Nat.mul_le_mul_left _ h6
      _ = Kcost c A * Y1 ^ 6 := by unfold Kcost; ring
      _ ≤ Kcost c A * Ym := Nat.mul_le_mul_left _ hY6

#print axioms split_le
#print axioms round_arith
#print axioms level0_arith
#print axioms level_pieces

end
end EthInapproximability.CurrentPaper.ClockM
