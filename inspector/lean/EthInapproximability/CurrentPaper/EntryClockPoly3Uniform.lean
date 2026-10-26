import EthInapproximability.CurrentPaper.EntryClockPoly3Final0
import EthInapproximability.CurrentPaper.EntryClockPoly3LevelJ
import EthInapproximability.CurrentPaper.ClockG
import EthInapproximability.CurrentPaper.FuelShell

/-!
# Lane owner:b-entry-clock-3, segment 3: one uniform writer-22 clock at every level

Under the endpoint hypotheses of the admitted `ClockB.hb2_physical_source` premise `hprem`
(`G.SourceCommon γ Δ`, `n ≤ |E|`, `|E| ≤ A n b^d`, `1 ≤ repetitions c A d n`, with
`b = sourceDepth n`, `k = repetitions c A d n = kValue (actualMachine c A d) n`), the admitted
`ClockG.level_widths` gives `2 k · oneLevelBound (physParameters .. j) < n` at every `j < k`.
So the naming premise holds at EVERY physical level with ONE `p := n / (2 k)`, and:

* `T22_0` (the literal clock of the admitted `EntryPrepFamily.level0_writer22`) and
* `writerBound_j G c b (yP G c b j) j (MP G c b j) TJ` at every `1 ≤ j < k`
  (the literal clock of the admitted `EntryWriter22J.writer22J_of_family4` at the physRun state),
  for any level-j family clock `TJ ≤ (|enc G|+1)^C0 + 2^(C0 p)`,

are all `≤ T22 := (n + |enc G| + 1)^C + 2^(C (n / (2k)))` for ONE absolute `C`.
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly3

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryPrepVec EntryTailClear EntryPrepFamily

/-- The naming premise at every physical level `j < k`, with `p = n / (2k)`. -/
theorem naming_at_levels {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n) :
    EffectiveIteration.oneLevelBound
        (Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
          (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤
      n / (2 * ETHTailGrowth.repetitions c A d n) := by
  have h := (ClockG.level_widths G c A d Δ n γ hcommon hlower hupper hrep j hj).1
  have e : PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) j =
    Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j) := rfl
  rw [e] at h
  rw [Nat.le_div_iff_mul_le (by omega)]
  rw [Nat.mul_comm] at h
  omega

/-- The level-0 naming premise is the `j = 0` case. -/
theorem naming_level0 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) :
    EffectiveIteration.oneLevelBound (EntryClockPoly.P0 G n c) ≤
      n / (2 * ETHTailGrowth.repetitions c A d n) :=
  naming_at_levels G c A d Δ n γ hcommon hlower hupper hrep 0 (by omega)

/-- **Segment 3.** ONE `T22 = (n + |enc G| + 1)^C + 2^(C (n / (2k)))` bounds the level-0 clock and
the level-j clock at every physRun state `1 ≤ j < k`, uniformly over graphs and endpoint
parameters, for any level-j family clock under the stated polynomial premise. -/
theorem uniform_T22 (C0 : ℕ) : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (prepBound G n c (labBound G n c (TF G n c)) + (tailBound G n c + clearBound G n c + 1) + 1) + 1 ≤
      (n + EntryClockPoly.ellG G + 1) ^ C +
        2 ^ (C * (n / (2 * ETHTailGrowth.repetitions c A d n)))) ∧
    (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
      ∀ TJ : ℕ, TJ ≤ (EntryClockPoly.ellG G + 1) ^ C0 +
          2 ^ (C0 * (n / (2 * ETHTailGrowth.repetitions c A d n))) →
      EntryWriter22J.writerBound_j G c (EffectiveIteration.sourceDepth n)
          (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
          (StepP.MP G c (EffectiveIteration.sourceDepth n) j) TJ ≤
        (n + EntryClockPoly.ellG G + 1) ^ C +
          2 ^ (C * (n / (2 * ETHTailGrowth.repetitions c A d n)))) := by
  obtain ⟨C1, h1⟩ := T22_0_le
  obtain ⟨C2, h2⟩ := writerBound_j_poly C0
  refine ⟨max C1 C2, fun {V E} _ _ _ _ G c A d Δ n γ hcommon hlower hupper hrep => ?_⟩
  set p := n / (2 * ETHTailGrowth.repetitions c A d n) with hp
  have hX1 : 1 ≤ n + EntryClockPoly.ellG G + 1 := by omega
  have mono : ∀ C', C' ≤ max C1 C2 →
      (n + EntryClockPoly.ellG G + 1) ^ C' + 2 ^ (C' * p) ≤
        (n + EntryClockPoly.ellG G + 1) ^ max C1 C2 + 2 ^ (max C1 C2 * p) := fun C' hC' =>
    Nat.add_le_add (Nat.pow_le_pow_right hX1 hC')
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hC'))
  refine ⟨?_, ?_⟩
  · exact (h1 G n c p (naming_level0 G c A d Δ n γ hcommon hlower hupper hrep)).trans
      (mono C1 (le_max_left _ _))
  · intro j hj1 hjk TJ hTJ
    rw [FuelShell.kValue_actual] at hjk
    have hw := h2 G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j) p TJ
      (naming_at_levels G c A d Δ n γ hcommon hlower hupper hrep j hjk) hTJ
    have hl : (EntryClockPoly.ellG G + 1) ^ C2 ≤ (n + EntryClockPoly.ellG G + 1) ^ C2 :=
      Nat.pow_le_pow_left (by omega) _
    exact le_trans (by omega) (mono C2 (le_max_right _ _))


/-- `RoundP.Writer22SpecJ` is monotone in its clock. -/
theorem writer22SpecJ_mono {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {LW VW : Type} (W : LW → Turing.TM2.Stmt (fun _ : Level0DimsRound.H4 => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) (T T' : ℕ) (G : EndpointGraph V E) (c b yb j : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) (mw : List Bool)
    (h : RoundP.Writer22SpecJ W w₀ v₀ T G c b yb j Mx mS mw) (hT : T ≤ T') :
    RoundP.Writer22SpecJ W w₀ v₀ T' G c b yb j Mx mS mw := by
  intro F Q P hf
  obtain ⟨t, ht, v, hr⟩ := h F Q P hf
  exact ⟨t, ht.trans hT, v, hr⟩

/-- **Segment 3, consumer form at the physRun states.** For any level-j family program with a
`Family4SpecJ` whose clock obeys the stated polynomial premise, the admitted
`EntryWriter22J.writer22J_of_family4` program satisfies `RoundP.Writer22SpecJ` at EVERY physRun
state `1 ≤ j < k` with the ONE clock `T22 = (n + |enc G| + 1)^C + 2^(C (n / (2k)))`, in exactly the
argument shape of the admitted `ClockB.hb2_physical_source` premise (`G c (sourceDepth n) (yP ..) j
(MP ..) mS (rowMajor (physRun ..).matrix.entry)`). -/
theorem writer22J_uniform (C0 : ℕ) : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    ∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
    ∀ (mS : WeightedRawWords.Aux → List Bool),
      mS .Gw = EncodedGraph.encode (EncodedETHSource.serializeGraph G) →
    ∀ {LW VW : Type} (W : LW → Turing.TM2.Stmt (fun _ : OuterLevel0Prep.HStack => Bool) LW VW)
      (w₀ : LW) (v₀ : VW) (TJ : ℕ),
      TJ ≤ (EntryClockPoly.ellG G + 1) ^ C0 +
          2 ^ (C0 * (n / (2 * ETHTailGrowth.repetitions c A d n))) →
      EntryPrepVecJ.Family4SpecJ W w₀ v₀ TJ G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) mS →
      RoundP.Writer22SpecJ (EntryWriter22J.writerJ W w₀ v₀)
        (BitMachineRawSequence.leftLabel
          (MultiMove.startLabel (EntryWriter22J.jobs55.map CopyFill.toJob)))
        (MultiMove.initial, (EntryPrepVec.prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
        ((n + EntryClockPoly.ellG G + 1) ^ C +
          2 ^ (C * (n / (2 * ETHTailGrowth.repetitions c A d n))))
        G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j) mS
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) := by
  obtain ⟨C, hC⟩ := uniform_T22 C0
  refine ⟨C, fun {V E} _ _ _ _ G c A d Δ n γ hcommon hlower hupper hrep j hj1 hjk mS hGw
    LW VW W w₀ v₀ TJ hTJ hF => ?_⟩
  exact writer22SpecJ_mono _ _ _ _ _ G c _ _ j _ mS _
    (EntryWriter22J.writer22J_of_family4 G c (EffectiveIteration.sourceDepth n)
      (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
      (StepP.MP G c (EffectiveIteration.sourceDepth n) j) mS hGw W w₀ v₀ TJ hF)
    ((hC G c A d Δ n γ hcommon hlower hupper hrep).2 j hj1 hjk TJ hTJ)

#print axioms writer22SpecJ_mono
#print axioms writer22J_uniform

open Turing BitMachineEncoding BitMachineStackEmbedding
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryPrepCopy

/-- **Segment 3, level-0 consumer form.** The admitted `EntryPrepFamily.level0_writer22` program
satisfies `OuterLevel0Full.Writer22Spec` for the machine `CutoffBitMachine.actualMachine c A d`
with the ONE clock `T22₀ = (n + |enc G| + 1)^C + 2^(C (n / (2k)))`; `C` is absolute (independent
of `c A d Δ γ`, the graph and `n`), under the endpoint hypotheses of `hprem`. -/
theorem writer22_0_uniform : ∃ C : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    OuterLevel0Full.Writer22Spec (CutoffBitMachine.actualMachine c A d)
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program
          (prepProg4 progF
            (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
          tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
          (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))))
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      ((n + EntryClockPoly.ellG G + 1) ^ C +
        2 ^ (C * (n / (2 * ETHTailGrowth.repetitions c A d n)))) G n c := by
  obtain ⟨C, hC⟩ := uniform_T22 0
  exact ⟨C, fun {V E} _ _ _ _ G c A d Δ n γ hcommon hlower hupper hrep =>
    EntryClockPoly.writer22Spec_mono (CutoffBitMachine.actualMachine c A d) _ _ _ G n c
      (hC G c A d Δ n γ hcommon hlower hupper hrep).1
      (EntryPrepFamily.level0_writer22 (CutoffBitMachine.actualMachine c A d) G n c)⟩

#print axioms writer22_0_uniform

#print axioms naming_at_levels
#print axioms naming_level0
#print axioms uniform_T22

end EthInapproximability.CurrentPaper.EntryClockPoly3
