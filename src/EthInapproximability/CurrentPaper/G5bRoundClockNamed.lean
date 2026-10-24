import EthInapproximability.CurrentPaper.G5bPrepNamed

/-!
# One round clock of the physical run at an ARBITRARY level, from named premises
(private lane owner:b-g5-2, segment 1 support; NOT the materialization theorem)

`StepP.roundBoundP G c b j mb mw T22 + StepP.installBoundP G c b j + 1` (the per-round clock that
`KShell.shell_run` needs in its premise `hT`) is bounded at the physical level `j` for ARBITRARY
`j` and `p` by `T22 + roundRest (|enc G|) p`, where `roundRest` is an explicit expression of the
form `poly(|enc G|) + 2^(O(p))` (no `n`, no `k`, no table size `T(n)`), from:

* `SourceNames ⟨G, c, b, y_j, j, M_j⟩ p` at the level record of the physical run
  (`y_j = StepP.yP`, `M_j = StepP.MP`);
* the output carrier names `clog rows(step) ≤ p`, `clog cols(step) ≤ p`;
* the next-state names of `ActualRoundParts.install_bound_named`
  (`clog c ≤ p`, `b ≤ p`, `clog (y_{j+1} + j + 1) ≤ p`, `clog rows_{j+1} ≤ p`, `clog cols_{j+1} ≤ p`);
* `1 ≤ c` and a blank master `N` cell.

The writer clock `T22` is left as a parameter (it is bounded separately by the replayed
`ActualWriterClock.writer_full_clock_source`).

NOT claimed: the level-0 round (`level0BoundP`); a run of the shell; any total machine.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5bRoundClockNamed

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualOrderFromCarrier

set_option maxHeartbeats 3000000

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

/-- The explicit rest of the round clock (everything except `T22`). -/
def roundRest [Fintype OuterLevel0Bridge.BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (C ps ps3 K ell p : ℕ) : ℕ :=
  ((1 + WeightedLevel0Clean.nClear * ps3) *
      ((1 + 9 * ps) * ((800 * (ell + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
        W12RowTime.Krow * (ell + 205 * 2 ^ (4 * p) + 1) ^ 9) +
    WeightedLevel0Clean.nClear * (5 * 2 ^ p + 2 * ell + 1) +
    WeightedLevel0Clean.nClear + 6 * 2 ^ p + 16 + K * (3 * 2 ^ p + 2 * ell + 7) ^ 2) +
  (2000000 * ClockD.Kc + 1000000) * (5 * 2 ^ p + ell + 1) ^ 6 +
  DimsClock1.Kd * (2 * 2 ^ p + 1) ^ 2 +
  ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 * (ell ^ 18 + 205 ^ 18 * 2 ^ (72 * p)) +
  2 ^ (2 * p) + 2 * 2 ^ (2 * p) +
  Level0CleanRun.nB * ((ell + 205 * 2 ^ (4 * p)) +
    BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
      (ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
        (ell ^ 18 + 205 ^ 18 * 2 ^ (72 * p)))) +
  Level0CleanRun.nB + (12 * 2 ^ p + 4 * ell + 30) + 20

theorem round_named [Fintype OuterLevel0Bridge.BStack]
    [Fintype MatrixTableInterlaceProtectedBridge.Label] :
    ∃ C ps ps3 K : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (c b j p T22 : ℕ) (mb : WeightedRawWords.Aux → List Bool),
      1 ≤ c → mb .N = [] →
      SourceNames ⟨V, E, G, c, b, StepP.yP G c b j, j, StepP.MP G c b j⟩ p →
      Nat.clog 2 (Iteration.step G c b (StepP.yP G c b j) j (StepP.MP G c b j)).rows ≤ p →
      Nat.clog 2 (Iteration.step G c b (StepP.yP G c b j) j (StepP.MP G c b j)).columns ≤ p →
      Nat.clog 2 c ≤ p → b ≤ p →
      Nat.clog 2 ((PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).budget +
        (j + 1)) ≤ p →
      Nat.clog 2 (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.rows ≤ p →
      Nat.clog 2 (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.columns ≤ p →
      StepP.roundBoundP G c b j mb
          (MatrixMaterialization.rowMajor
            (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix.entry) T22 +
        StepP.installBoundP G c b j + 1 ≤
      T22 + roundRest C ps ps3 K (ell3 G) p := by
  obtain ⟨C, ps, ps3, K, hP⟩ := G5bPrepNamed.prep_named_full
  refine ⟨C, ps, ps3, K, fun {V E} _ _ _ _ G c b j p T22 mb hc hN h hrows hcols hcc hb hy hr hcol => ?_⟩
  let i : LI := ⟨V, E, G, c, b, StepP.yP G c b j, j, StepP.MP G c b j⟩
  have hNj : StepP.mSj mb G c b j .N = [] := by
    unfold StepP.mSj
    rw [Function.update_of_ne (by intro h; cases h)]
    exact hN
  have hprep := hP i p (StepP.mSj mb G c b j) hNj h hrows hcols
  have hcost := ActualRoundParts.cost_bound_named i p h
  have hdims := ActualRoundParts.dims_bound_named i p hc hrows hcols
  have hbud := G5bRoundNamed.budget_named i p h hrows hcols
  have hout := G5bRoundNamed.output_named i p hrows hcols
  have hst := G5bRoundNamed.stacks_named i p h hrows hcols
  have hins := ActualRoundParts.install_bound_named G c b j p hcc hb hy hr hcol
  have hmw : (MatrixMaterialization.rowMajor
      (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix.entry).length ≤
        2 ^ (2 * p) := by
    rw [MatrixMaterialization.rowMajor_length, two_mul, pow_add]
    exact Nat.mul_le_mul (from_clog h.inputRows) (from_clog h.inputCols)
  have e1 : LevelJPrep.prepBoundJ i.G i.c i.b i.y i.lv i.M (StepP.mSj mb G c b j) =
      LevelJPrep.prepBoundJ G c b (StepP.yP G c b j) j (StepP.MP G c b j) (StepP.mSj mb G c b j) := rfl
  have e2 : CostUpdateMachine.costBound (Parameters.scale (PL i)) (PL i).nextDepth
      (PL i).sourceConstant (sI i) (Fintype.card i.E) (PL i).cost =
      CostUpdateMachine.costBound
        (Parameters.scale (LevelJPrep.Pj G c b (StepP.yP G c b j) j (StepP.MP G c b j))) b c
        (Parameters.bins (LevelJPrep.Pj G c b (StepP.yP G c b j) j (StepP.MP G c b j)))
        (Fintype.card E) (LevelJPrep.Pj G c b (StepP.yP G c b j) j (StepP.MP G c b j)).cost := rfl
  have e3 : NextDimsMachineTN.dimsBound
      (NextDimsEmbedTN.dimsIn (PL i) (Fintype.card i.V)
        (sI i * EffectiveIteration.familySize (PL i))) =
      NextDimsMachineTN.dimsBound (RoundP.dxJ G c b (StepP.yP G c b j) j (StepP.MP G c b j)) := rfl
  have e4 : ProtectedFullBankBridgeScratch.actualPhysicalBudget i.G i.c i.b i.y i.lv i.M =
      ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (StepP.yP G c b j) j
        (StepP.MP G c b j) := rfl
  have e5 : (ProtectedFullBankBridgeScratch.actualPhysicalOutput i.G i.c i.b i.y i.lv i.M).length =
      (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (StepP.yP G c b j) j
        (StepP.MP G c b j)).length := rfl
  have e6 : (∑ k : Fin Level0CleanRun.nB,
      (((ProtectedFullBankBridgeScratch.actualPhysicalStart i.G i.c i.b i.y i.lv i.M).stk
            ((Fintype.equivFin OuterLevel0Bridge.BStack).symm k)).length +
        BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
          ProtectedFullBankBridgeScratch.actualPhysicalBudget i.G i.c i.b i.y i.lv i.M)) =
      (∑ k : Fin Level0CleanRun.nB,
      (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c b (StepP.yP G c b j) j
            (StepP.MP G c b j)).stk ((Fintype.equivFin OuterLevel0Bridge.BStack).symm k)).length +
        BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
          ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (StepP.yP G c b j) j
            (StepP.MP G c b j))) := rfl
  have hell : ell3 i.G = ell3 G := rfl
  rw [e1, hell] at hprep
  rw [e2, hell] at hcost
  rw [e3] at hdims
  rw [e4, hell] at hbud
  rw [e5] at hout
  rw [e6, hell] at hst
  unfold StepP.roundBoundP roundRest
  omega

#print axioms round_named

end EthInapproximability.CurrentPaper.G5bRoundClockNamed
