import EthInapproximability.CurrentPaper.W12Final
import EthInapproximability.CurrentPaper.W12ReadyJ

/-! Lane owner:b-weighted-level-12: the ready halves (segment 1) substituted into the endpoint.
`thm:main` of lock v8 with `hB2` discharged modulo exactly: the level-`j` family clock `LevelJFamilyClock`
(lane entry-clock-4's target) and the dims clocks `DimsPoly` (segment 2). -/

namespace EthInapproximability.CurrentPaper.BLevel12

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EncodedETHSource EncodedETHSourceComposition
open OuterLevel0Prep Level0DimsRound OuterLevel0Full RoundP StepP Level0Install LevelJPrep

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

attribute [local instance] Level0DimsClean.instLabel Level0DimsClean.instBStack

theorem pow_pair_le (a T e f M : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T) (he : e ≤ M) (hf : f ≤ M) :
    a ^ e * T ^ f ≤ a ^ M * T ^ M :=
  Nat.mul_le_mul (Nat.pow_le_pow_right ha he) (Nat.pow_le_pow_right hT hf)

theorem kz_le (a T d KE M : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T) (hM : 18 * (d + 1) + 18 ≤ M) :
    (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9 ≤ (KE + 1) ^ 9 * (a ^ M * T ^ M) := by
  have hZ : 1 ≤ (a ^ (d + 1) * T) * (a ^ (d + 1) * T) :=
    Nat.mul_pos (Nat.mul_pos (Nat.one_le_pow _ _ ha) hT) (Nat.mul_pos (Nat.one_le_pow _ _ ha) hT)
  have h1 : KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1 ≤
      (KE + 1) * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) := by
    rw [Nat.add_mul, one_mul]; omega
  have h2 : ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) ^ 9 = a ^ (18 * (d + 1)) * T ^ 18 := by ring
  calc (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9
      ≤ ((KE + 1) * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T))) ^ 9 := Nat.pow_le_pow_left h1 9
    _ = (KE + 1) ^ 9 * (a ^ (18 * (d + 1)) * T ^ 18) := by rw [mul_pow, h2]
    _ ≤ (KE + 1) ^ 9 * (a ^ M * T ^ M) :=
        Nat.mul_le_mul_left _ (pow_pair_le a T _ _ M ha hT (by omega) (by omega))

/-- Collapse of the explicit level-0 ready bound (`W12Ready0.ready0_level`) to the `Cx a^M T^M` shape. -/
theorem collapse0 (a T d Cp M rawC KE Krow ps ps2 nC : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T)
    (hM : 128 + Cp + 18 * (d + 1) + 18 ≤ M) :
    (1 + nC * ps2) * (rawC * a ^ 128 + 110 * a ^ 3 + 1 +
        ((1 + 9 * ps) * (2 * a ^ Cp * T ^ Cp) + 14 +
          Krow * (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9)) + nC + 3 + (24 * T + 11) ≤
      ((1 + nC * ps2) * (rawC + 110 + 1 + (1 + 9 * ps) * 2 + 14 + Krow * (KE + 1) ^ 9) + nC + 38) *
        a ^ M * T ^ M := by
  have hY : 1 ≤ a ^ M * T ^ M := Nat.mul_pos (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hT)
  have t1 : a ^ 128 ≤ a ^ M * T ^ M := by
    have := pow_pair_le a T 128 0 M ha hT (by omega) (by omega); simpa using this
  have t2 : a ^ 3 ≤ a ^ M * T ^ M := by
    have := pow_pair_le a T 3 0 M ha hT (by omega) (by omega); simpa using this
  have t4 : 2 * a ^ Cp * T ^ Cp ≤ 2 * (a ^ M * T ^ M) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 (pow_pair_le a T Cp Cp M ha hT (by omega) (by omega))
  have t5 := kz_le a T d KE M ha hT (by omega)
  have t6 : T ≤ a ^ M * T ^ M := by
    have := pow_pair_le a T 0 1 M ha hT (by omega) (by omega); simpa using this
  rw [show ∀ K : ℕ, K * a ^ M * T ^ M = K * (a ^ M * T ^ M) from fun K => Nat.mul_assoc _ _ _]
  generalize a ^ M * T ^ M = Y at hY t1 t2 t4 t5 t6 ⊢
  have s1 : rawC * a ^ 128 ≤ rawC * Y := Nat.mul_le_mul_left _ t1
  have s2 : (1 + 9 * ps) * (2 * a ^ Cp * T ^ Cp) ≤ (1 + 9 * ps) * (2 * Y) := Nat.mul_le_mul_left _ t4
  have s3 : Krow * (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9 ≤ Krow * ((KE + 1) ^ 9 * Y) :=
    Nat.mul_le_mul_left _ t5
  have hS : rawC * a ^ 128 + 110 * a ^ 3 + 1 +
        ((1 + 9 * ps) * (2 * a ^ Cp * T ^ Cp) + 14 +
          Krow * (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9) ≤
      (rawC + 110 + 1 + (1 + 9 * ps) * 2 + 14 + Krow * (KE + 1) ^ 9) * Y := by
    have e : (rawC + 110 + 1 + (1 + 9 * ps) * 2 + 14 + Krow * (KE + 1) ^ 9) * Y =
        rawC * Y + 110 * Y + Y + ((1 + 9 * ps) * (2 * Y) + 14 * Y + Krow * ((KE + 1) ^ 9 * Y)) := by ring
    rw [e]; omega
  have hS' := Nat.mul_le_mul_left (1 + nC * ps2) hS
  have hn : nC ≤ nC * Y := Nat.le_mul_of_pos_right _ hY
  have e2 : ((1 + nC * ps2) * (rawC + 110 + 1 + (1 + 9 * ps) * 2 + 14 + Krow * (KE + 1) ^ 9) + nC + 38) * Y =
      (1 + nC * ps2) * ((rawC + 110 + 1 + (1 + 9 * ps) * 2 + 14 + Krow * (KE + 1) ^ 9) * Y) + nC * Y + 38 * Y := by
    ring
  rw [e2]; omega

/-- Collapse of the explicit level-`j` ready bound (`W12ReadyJ.readyJ_level`). -/
theorem collapseJ (a T d Cp M KE Krow ps ps3 nC : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T)
    (hM : 128 + Cp + 18 * (d + 1) + 18 ≤ M) :
    (1 + nC * ps3) * ((1 + 9 * ps) * (2 * a ^ Cp * T ^ Cp) + 13 +
          Krow * (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9) +
        nC * (7 * (T * a)) + nC + 3 + (24 * T + 11) ≤
      ((1 + nC * ps3) * ((1 + 9 * ps) * 2 + 13 + Krow * (KE + 1) ^ 9) + 7 * nC + nC + 38) *
        a ^ M * T ^ M := by
  have hY : 1 ≤ a ^ M * T ^ M := Nat.mul_pos (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hT)
  have t4 : 2 * a ^ Cp * T ^ Cp ≤ 2 * (a ^ M * T ^ M) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 (pow_pair_le a T Cp Cp M ha hT (by omega) (by omega))
  have t5 := kz_le a T d KE M ha hT (by omega)
  have t6 : T ≤ a ^ M * T ^ M := by
    have := pow_pair_le a T 0 1 M ha hT (by omega) (by omega); simpa using this
  have t7 : T * a ≤ a ^ M * T ^ M := by
    have := pow_pair_le a T 1 1 M ha hT (by omega) (by omega)
    simpa [Nat.mul_comm] using this
  rw [show ∀ K : ℕ, K * a ^ M * T ^ M = K * (a ^ M * T ^ M) from fun K => Nat.mul_assoc _ _ _]
  generalize a ^ M * T ^ M = Y at hY t4 t5 t6 t7 ⊢
  have s2 : (1 + 9 * ps) * (2 * a ^ Cp * T ^ Cp) ≤ (1 + 9 * ps) * (2 * Y) := Nat.mul_le_mul_left _ t4
  have s3 : Krow * (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9 ≤ Krow * ((KE + 1) ^ 9 * Y) :=
    Nat.mul_le_mul_left _ t5
  have hS : (1 + 9 * ps) * (2 * a ^ Cp * T ^ Cp) + 13 +
        Krow * (KE * ((a ^ (d + 1) * T) * (a ^ (d + 1) * T)) + 1) ^ 9 ≤
      ((1 + 9 * ps) * 2 + 13 + Krow * (KE + 1) ^ 9) * Y := by
    have e : ((1 + 9 * ps) * 2 + 13 + Krow * (KE + 1) ^ 9) * Y =
        (1 + 9 * ps) * (2 * Y) + 13 * Y + Krow * ((KE + 1) ^ 9 * Y) := by ring
    rw [e]; omega
  have hS' := Nat.mul_le_mul_left (1 + nC * ps3) hS
  have h7 : nC * (7 * (T * a)) ≤ nC * (7 * Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 7 t7)
  have hn : nC ≤ nC * Y := Nat.le_mul_of_pos_right _ hY
  have e2 : ((1 + nC * ps3) * ((1 + 9 * ps) * 2 + 13 + Krow * (KE + 1) ^ 9) + 7 * nC + nC + 38) * Y =
      (1 + nC * ps3) * (((1 + 9 * ps) * 2 + 13 + Krow * (KE + 1) ^ 9) * Y) + nC * (7 * Y) + nC * Y + 38 * Y := by
    ring
  rw [e2]; omega

/-- INTERFACE (segment 2; NOT proved here): the dims clocks at level 0 and at every level `1 ≤ j < k`, in the
exact shape of `ClockQ.hb2_physical_ready`'s `hprem`. -/
def DimsPoly (c A d Δ : ℕ) (γ : ℚ) (Cx ex fx : ℕ) : Prop :=
  ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n : ℕ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    NextDimsMachineTN.dimsBound (dx G n c) ≤
        Cx * ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
      (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
        NextDimsMachineTN.dimsBound (dxJ G c (EffectiveIteration.sourceDepth n)
            (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)) ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx)

theorem shape_up (D Cx Ctot a T ex fx M : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T) (hex : ex ≤ M) (hfx : fx ≤ M)
    (hC : Cx ≤ Ctot) (hD : D ≤ Cx * a ^ ex * T ^ fx) : D ≤ Ctot * a ^ M * T ^ M := by
  have h := pow_pair_le a T ex fx M ha hT hex hfx
  calc D ≤ Cx * a ^ ex * T ^ fx := hD
    _ = Cx * (a ^ ex * T ^ fx) := by ring
    _ ≤ Ctot * (a ^ M * T ^ M) := Nat.mul_le_mul hC h
    _ = Ctot * a ^ M * T ^ M := by ring

/-- **Segment 1 substituted:** the ready conjuncts of `ReadyDimsPoly` are proved; only the dims clocks remain. -/
theorem readyDims_of_dims (c A d Δ : ℕ) (γ : ℚ) (Cxd exd fxd : ℕ) (hD : DimsPoly c A d Δ γ Cxd exd fxd) :
    ∃ Cx ex fx : ℕ, ReadyDimsPoly c A d Δ γ Cx ex fx := by
  obtain ⟨Cp0, ps0, h0⟩ := W12Ready0.ready0_level
  obtain ⟨ps2, h0'⟩ := h0 c A d
  obtain ⟨CpJ, psJ, ps3, hJ⟩ := W12ReadyJ.readyJ_level
  refine ⟨((1 + WeightedLevel0Clean.nClear * ps2) * (WeightedRawWordsClock.rawC (CutoffBitMachine.actualMachine c A d) c +
        110 + 1 + (1 + 9 * ps0) * 2 + 14 + W12RowTime.Krow * (ClockK.KE c A + 1) ^ 9) + WeightedLevel0Clean.nClear + 38) +
      ((1 + WeightedLevel0Clean.nClear * ps3) * ((1 + 9 * psJ) * 2 + 13 + W12RowTime.Krow * (ClockK.KE c A + 1) ^ 9) +
        7 * WeightedLevel0Clean.nClear + WeightedLevel0Clean.nClear + 38) + Cxd,
    128 + Cp0 + CpJ + 18 * (d + 1) + 18 + exd + fxd, 128 + Cp0 + CpJ + 18 * (d + 1) + 18 + exd + fxd, ?_⟩
  intro V E _ _ _ _ G n hcommon hlower hupper hrep
  obtain ⟨hd0, hdj⟩ := hD G n hcommon hlower hupper hrep
  have ha : 1 ≤ (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1 := by omega
  have hT : 1 ≤ FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := ClockH.table_pos _ n
  refine ⟨?_, ?_, fun j hj1 hjk => ⟨?_, ?_⟩⟩
  · have h := (h0' G Δ n γ hcommon hlower hupper hrep).trans
      (collapse0 _ _ d Cp0 (128 + Cp0 + CpJ + 18 * (d + 1) + 18 + exd + fxd) _ _ _ ps0 ps2 _ ha hT (by omega))
    exact shape_up _ _ _ _ _ _ _ _ ha hT (le_refl _) (le_refl _) (by omega) h
  · exact shape_up _ _ _ _ _ _ _ _ ha hT (by omega) (by omega) (by omega) hd0
  · have h := (hJ (CutoffBitMachine.actualMachine c A d) G c A d Δ n γ hcommon hlower hupper hrep j hjk).trans
      (collapseJ _ _ d CpJ (128 + Cp0 + CpJ + 18 * (d + 1) + 18 + exd + fxd) _ _ psJ ps3 _ ha hT (by omega))
    exact shape_up _ _ _ _ _ _ _ _ ha hT (le_refl _) (le_refl _) (by omega) h
  · exact shape_up _ _ _ _ _ _ _ _ ha hT (by omega) (by omega) (by omega) (hdj j hj1 hjk)

/-- **`HB2Physical` for ONE fixed machine, ready halves discharged:** premises the source constants, the level-`j`
family clock `LevelJFamilyClock` and the dims clocks `DimsPoly` only. -/
theorem hb2_physical_dims (hfam : LevelJFamilyClock)
    (c A d Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) (Cxd exd fxd : ℕ)
    (hD : DimsPoly c A d Δ γ Cxd exd fxd) :
    PhysicalLevelRun.HB2Physical c A d Δ γ := by
  obtain ⟨Cx, ex, fx, h⟩ := readyDims_of_dims c A d Δ γ Cxd exd fxd hD
  exact hb2_physical_fixed hfam c A d Δ γ hΔ hγ hγone hsource Cx ex fx h

theorem hRD_of_dims
    (hD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, DimsPoly c A d Δ γ Cx ex fx) :
    ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, ReadyDimsPoly c A d Δ γ Cx ex fx := by
  intro c A d Δ γ h1 h2 h3 h4
  obtain ⟨Cx, ex, fx, h⟩ := hD c A d Δ γ h1 h2 h3 h4
  exact readyDims_of_dims c A d Δ γ Cx ex fx h

/-- **`thm:main` of lock v8**, `hB2` discharged modulo exactly `LevelJFamilyClock` and `DimsPoly`. -/
theorem thm_main_dims (hfam : LevelJFamilyClock)
    (hD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, DimsPoly c A d Δ γ Cx ex fx)
    (Computable : (ℕ → ℕ) → Prop)
    (hComp : ∀ c A d : ℕ, Computable (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)))
    (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) :
    ∃ α : ℕ → ℕ, Computable α ∧ Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  thm_main_fixed hfam (hRD_of_dims hD) Computable hComp hETH Srec D B

theorem thm_main_core_dims (hfam : LevelJFamilyClock)
    (hD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, DimsPoly c A d Δ γ Cx ex fx)
    (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) :
    ∃ α : ℕ → ℕ, (∃ c A d : ℕ, α = FinalPadding.allowance (ETHTailGrowth.repetitions c A d)) ∧
      Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  thm_main_core_fixed hfam (hRD_of_dims hD) hETH Srec D B

theorem thm_main_nonempty_dims (hfam : LevelJFamilyClock)
    (hD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, DimsPoly c A d Δ γ Cx ex fx)
    (Computable : (ℕ → ℕ) → Prop)
    (hComp : ∀ c A d : ℕ, Computable (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)))
    (hIPZ : ∀ η : ℚ, 0 < η → Nonempty (Sparsification η))
    (hDinur : Nonempty DinurReduction)
    (hBOT : ∀ k : ℕ, Nonempty (BOTReduction k))
    (hETH : EncodedETHTail.ETH) :
    ∃ α : ℕ → ℕ, Computable α ∧ Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  thm_main_nonempty_fixed hfam (hRD_of_dims hD) Computable hComp hIPZ hDinur hBOT hETH

#print axioms kz_le
#print axioms collapse0
#print axioms collapseJ
#print axioms readyDims_of_dims
#print axioms hb2_physical_dims
#print axioms thm_main_dims
#print axioms thm_main_core_dims
#print axioms thm_main_nonempty_dims

end
end EthInapproximability.CurrentPaper.BLevel12
