import EthInapproximability.CurrentPaper.ClockQ
import EthInapproximability.CurrentPaper.EntryPrepFamilyComposeJ
import EthInapproximability.CurrentPaper.EntryClockPoly3Uniform
import EthInapproximability.CurrentPaper.BEthThmMain

/-! Lane owner:b-weighted-level-12, Paper B, segments 3 and 4 (composition only).

* `hb2_physical_fixed`: `PhysicalLevelRun.HB2Physical c A d Δ γ` for ONE fixed machine: owner-10's
  `hb2Machine` with level-0 program `W0prog` (the admitted `EntryPrepFamily.level0_writer22`) and the
  level-`j` program `writerF = writerJ progF …` of lane entry-levelj-2 (`kshell_hW_F`), from the source
  constants, the level-`j` family clock premise `LevelJFamilyClock` (lane entry-clock-4's target, NOT
  proved here) and the ready/dims polynomial premise `ReadyDimsPoly` (segments 1 and 2, NOT proved
  here). `hW` is discharged by `kshell_hW_F`, `T22zero` by `uniform_T22` (= `T22_0_le` + naming), `T22`
  by the family-clock premise at the naming premise of `naming_at_levels`.
* `hb2Supply_fixed`: `BEthEndpoint.HB2Supply S D B` from the same premises (source constants from the
  record fields `degreeBound_pos`, `source_gap_pos`, `source_gap_le_one`).
* `thm_main_fixed`, `thm_main_core_fixed`: `thm:main` of lock v8 through `BEthEndpoint.thm_main` /
  `thm_main_core` with `hB2` discharged modulo exactly those two named premises.
-/

namespace EthInapproximability.CurrentPaper.BLevel12

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EncodedETHSource EncodedETHSourceComposition
open OuterLevel0Prep Level0DimsRound OuterLevel0Full RoundP StepP Level0Install LevelJPrep
open EntryPrepCopy EntryPrepVec EntryPrepFamily EntryPrepVecJ EntryWriter22J

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

attribute [local instance] Level0DimsClean.instLabel Level0DimsClean.instBStack

/-- Lane entry-levelj-2's ONE level-`j` writer program `writerJ progF wF vF`. -/
abbrev writerF := writerJ progF
  (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
  (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
    (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))

abbrev w55 : ClockO.labelOf writerF :=
  BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob))

abbrev ctlF : ClockO.ctrlOf writerF :=
  (MultiMove.initial, (prepInit ((MultiMove.initial, false),
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))

example : Fintype (ClockO.labelOf writerF) := inferInstance
example : Fintype (ClockO.ctrlOf writerF) := inferInstance

/-- INTERFACE (lane entry-clock-4's target; NOT proved here): the level-`j` writer clock at the
level-`j` family clock `TFJ`, at every physical level, under the naming premise. -/
def LevelJFamilyClock : Prop :=
  ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c j p : ℕ),
    EffectiveIteration.oneLevelBound
        (Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
          (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤ p →
    writerBound_j G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (EntryPrepFamilyJ.TFJ G c (EffectiveIteration.sourceDepth n)
          (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤
      (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C + 2 ^ (C * p)

/-- The same target stated on the family clock `TFJ` alone (the shape of `EC3TF.TF_le` at level `j`). -/
def TFJClock : Prop :=
  ∃ C0 : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c j p : ℕ),
    EffectiveIteration.oneLevelBound
        (Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
          (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤ p →
    EntryPrepFamilyJ.TFJ G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) ≤
      (EntryClockPoly.ellG G + 1) ^ C0 + 2 ^ (C0 * p)

/-- The `TFJ` form implies the writer-clock form (lane entry-clock-3's `writerBound_j_poly`). -/
theorem levelJFamilyClock_of_TFJ (h : TFJClock) : LevelJFamilyClock := by
  obtain ⟨C0, h0⟩ := h
  obtain ⟨C, hC⟩ := EntryClockPoly3.writerBound_j_poly C0
  refine ⟨C, fun {V E} _ _ _ _ G n c j p hp => ?_⟩
  have h1 := hC G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
    (StepP.MP G c (EffectiveIteration.sourceDepth n) j) p _ hp (h0 G n c j p hp)
  have hl : EntryClockPoly.ellG G + 1 ≤
      n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 := by
    unfold EntryClockPoly.ellG; omega
  exact h1.trans (Nat.add_le_add_right (Nat.pow_le_pow_left hl _) _)

/-- INTERFACE (segments 1 and 2; NOT proved here): the ready halves and the dims clocks, at level 0
and at every level `1 ≤ j < k`, in the exact shape of `ClockQ.hb2_physical_ready`'s `hprem`. -/
def ReadyDimsPoly (c A d Δ : ℕ) (γ : ℚ) (Cx ex fx : ℕ) : Prop :=
  ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n : ℕ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    readyBound (CutoffBitMachine.actualMachine c A d) G n c ≤
        Cx * ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
      NextDimsMachineTN.dimsBound (dx G n c) ≤
        Cx * ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
      (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
        readyBoundJ G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) j) j
            (MP G c (EffectiveIteration.sourceDepth n) j)
            (mSj (mb1 (CutoffBitMachine.actualMachine c A d) G n c) G c
              (EffectiveIteration.sourceDepth n) j) ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
        NextDimsMachineTN.dimsBound (dxJ G c (EffectiveIteration.sourceDepth n)
            (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)) ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx)

theorem shape_mono (X C' C q : ℕ) (hX : 1 ≤ X) (h : C' ≤ C) :
    X ^ C' + 2 ^ (C' * q) ≤ X ^ C + 2 ^ (C * q) :=
  Nat.add_le_add (Nat.pow_le_pow_right hX h)
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h))

/-- **Segment 3: `HB2Physical` for ONE fixed machine** (`hb2Machine … W0prog w00 v00 writerF w55 ctlF`,
through `ClockQ.hb2_physical_ready`), `hW` and both entry clocks discharged. -/
theorem hb2_physical_fixed (hfam : LevelJFamilyClock)
    (c A d Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c) (Cx ex fx : ℕ)
    (hRD : ReadyDimsPoly c A d Δ γ Cx ex fx) :
    PhysicalLevelRun.HB2Physical c A d Δ γ := by
  obtain ⟨C, hC⟩ := hfam
  obtain ⟨C1, hU⟩ := EntryClockPoly3.uniform_T22 0
  refine ClockQ.hb2_physical_ready c A d Δ γ hΔ hγ hγone hsource writerF w55 ctlF Cx ex fx (C + C1) ?_
  intro V E _ _ _ _ G n hcommon hlower hupper hrep
  obtain ⟨hr0, hd0, hj⟩ := hRD G n hcommon hlower hupper hrep
  have hexp : FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n =
      n / (2 * ETHTailGrowth.repetitions c A d n) := by
    unfold FinalPadding.exponent; rw [max_eq_right hrep]
  have hell : EntryClockPoly.ellG G = (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length := rfl
  have hX : 1 ≤ n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 := by omega
  refine ⟨(n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C +
      2 ^ (C * (n / (2 * ETHTailGrowth.repetitions c A d n))), ?_, ?_, ?_, hr0, hd0, hj⟩
  · refine EntryPrepFamilyJ.kshell_hW_F (CutoffBitMachine.actualMachine c A d) G n c _ _ ?_
    intro j hj1 hjk
    exact hC G n c j _ (EntryClockPoly3.naming_at_levels G c A d Δ n γ hcommon hlower hupper hrep j hjk)
  · rw [hexp]
    have h0 := (hU G c A d Δ n γ hcommon hlower hupper hrep).1
    rw [hell] at h0
    exact h0.trans (shape_mono _ C1 (C + C1) _ hX (by omega))
  · rw [hexp]
    exact shape_mono _ C (C + C1) _ hX (by omega)

/-- **Segment 4 (a): `HB2Supply S D B`** for the cited records, from the two named premises. -/
theorem hb2Supply_fixed (hfam : LevelJFamilyClock)
    (hRD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, ReadyDimsPoly c A d Δ γ Cx ex fx)
    {η : ℚ} (S : Sparsification η) (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) :
    BEthEndpoint.HB2Supply S D B := by
  intro c hc
  have hΔ : 0 < B.degreeBound := B.degreeBound_pos
  obtain ⟨Cx, ex, fx, h⟩ := hRD c _ _ B.degreeBound (sourceGap D B) hΔ (source_gap_pos D B)
    (source_gap_le_one D B) hc
  exact hb2_physical_fixed hfam c _ _ B.degreeBound (sourceGap D B) hΔ (source_gap_pos D B)
    (source_gap_le_one D B) hc Cx ex fx h

/-- **Segment 4 (b): `thm:main` of lock v8** (`BEthEndpoint.thm_main`, records as data, D-B1 the
predicate `Computable`), H-B2 discharged modulo the two named premises. -/
theorem thm_main_fixed (hfam : LevelJFamilyClock)
    (hRD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, ReadyDimsPoly c A d Δ γ Cx ex fx)
    (Computable : (ℕ → ℕ) → Prop)
    (hComp : ∀ c A d : ℕ, Computable (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)))
    (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) :
    ∃ α : ℕ → ℕ, Computable α ∧ Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  BEthEndpoint.thm_main Computable hComp hETH Srec D B
    (fun η hη => hb2Supply_fixed hfam hRD (Srec η hη) D B)

/-- `thm_main_core` (no D-B1; the allowance family exposed) with `hB2` discharged the same way. -/
theorem thm_main_core_fixed (hfam : LevelJFamilyClock)
    (hRD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, ReadyDimsPoly c A d Δ γ Cx ex fx)
    (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) :
    ∃ α : ℕ → ℕ, (∃ c A d : ℕ, α = FinalPadding.allowance (ETHTailGrowth.repetitions c A d)) ∧
      Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  BEthEndpoint.thm_main_core hETH Srec D B (fun η hη => hb2Supply_fixed hfam hRD (Srec η hη) D B)

/-- The `Nonempty` binder shape of D-B2 (`BEthEndpoint.thm_main_nonempty`). -/
theorem thm_main_nonempty_fixed (hfam : LevelJFamilyClock)
    (hRD : ∀ (c A d Δ : ℕ) (γ : ℚ), 0 < Δ → 0 < γ → γ ≤ 1 → 2 ^ 44 * (Δ : ℚ) / γ ≤ c →
      ∃ Cx ex fx : ℕ, ReadyDimsPoly c A d Δ γ Cx ex fx)
    (Computable : (ℕ → ℕ) → Prop)
    (hComp : ∀ c A d : ℕ, Computable (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)))
    (hIPZ : ∀ η : ℚ, 0 < η → Nonempty (Sparsification η))
    (hDinur : Nonempty DinurReduction)
    (hBOT : ∀ k : ℕ, Nonempty (BOTReduction k))
    (hETH : EncodedETHTail.ETH) :
    ∃ α : ℕ → ℕ, Computable α ∧ Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  BEthEndpoint.thm_main_nonempty Computable hComp hIPZ hDinur hBOT
    (fun _ S D B => hb2Supply_fixed hfam hRD S D B) hETH

#print axioms levelJFamilyClock_of_TFJ
#print axioms hb2_physical_fixed
#print axioms hb2Supply_fixed
#print axioms thm_main_fixed
#print axioms thm_main_core_fixed
#print axioms thm_main_nonempty_fixed

end
end EthInapproximability.CurrentPaper.BLevel12
