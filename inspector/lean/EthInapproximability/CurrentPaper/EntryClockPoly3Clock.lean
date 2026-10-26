import EthInapproximability.CurrentPaper.EntryClockPoly3Core

/-!
# Lane owner:b-entry-clock-3, segment 1: the family clock pieces are uniformly polynomial

Each admitted clock of the level-family run is `PolyIn U` over all levels (`U` of `EC3Core`).
Pure arithmetic about admitted definitions and admitted bounds
(`ETHBinsOutputClockScratch.joinedBound_le_output_clock`,
`WeightedLevelPublicClock.graphQ_bound_public`,
`ProtectedBudgetNormalizationScratch.prepCost_quartic`, `BalanceOrderCost.fullTime_output_bound`,
`Paper2.WeightedThresholdArithmetic.totalTime_polynomial`).
-/

namespace EthInapproximability.CurrentPaper.EntryClockPoly3

open EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-! ## Atoms -/

theorem pT : PolyIn U (fun i => tI i) :=
  PolyIn.of_le (fun i => by obtain ⟨h, -⟩ := sizes i; exact h)

theorem p2T : PolyIn U (fun i => 2 ^ tI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, h, -⟩ := sizes i; exact h)

theorem pA : PolyIn U (fun i => aI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, h, -⟩ := sizes i; exact h)

theorem p2A : PolyIn U (fun i => 2 ^ aI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, h, -⟩ := sizes i; exact h)

theorem pS : PolyIn U (fun i => sI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, h, -⟩ := sizes i; exact h)

theorem pQOne : PolyIn U (fun i => Construction.qOne (aI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pFL : PolyIn U (fun i => Construction.firstLength (aI i) (sI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pQ : PolyIn U (fun i => qI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pRx : PolyIn U (fun i => rxI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pCy : PolyIn U (fun i => cyI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pL : PolyIn U (fun i => LI' i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pP : PolyIn U (fun i => pI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pPT : PolyIn U (fun i => pI i ^ tI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pWB : PolyIn U (fun i => MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pBB : PolyIn U (fun i => MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pBBS : PolyIn U (fun i => MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pCYS : PolyIn U (fun i => cyI i ^ (sI i + 1)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pScale : PolyIn U (fun i => Parameters.scale (PL i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pSC : PolyIn U (fun i => (PL i).sourceConstant) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pND : PolyIn U (fun i => (PL i).nextDepth) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pCost : PolyIn U (fun i => (PL i).cost) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pEdges : PolyIn U (fun i => (PL i).edges) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pEll : PolyIn U (fun i => ell3 i.G) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pVert : PolyIn U (fun i => (gI i).vertices) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := sizes i; exact h)

theorem pE : PolyIn U (fun i => eI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := sizes i; exact h)

/-- Put every atom in context. -/
macro "atoms" : tactic => `(tactic| (have := @pT; have := @p2T; have := @pA; have := @p2A; have := @pS; have := @pQOne; have := @pFL; have := @pQ; have := @pRx; have := @pCy; have := @pL; have := @pP; have := @pPT; have := @pWB; have := @pBB; have := @pBBS; have := @pCYS; have := @pScale; have := @pSC; have := @pND; have := @pCost; have := @pEdges; have := @pEll; have := @pVert; have := @pE))

/-- Close a `PolyIn` goal with atoms matched up to reducible unfolding only. -/
macro "pr" : tactic => `(tactic| repeat' (first
  | with_reducible assumption
  | with_reducible exact PolyIn.const _
  | with_reducible apply PolyIn.add
  | with_reducible apply PolyIn.mul
  | with_reducible apply PolyIn.pow
  | with_reducible apply PolyIn.sub
  | with_reducible apply PolyIn.max))

/-- The empty writer bank (`noW3`, restated). -/
def noW3 : Fin 64 → List Bool := fun _ => []

theorem pEnc : PolyIn U (fun i => (EncodedGraph.encode (gI i)).length) := pEll

theorem pBinsS : PolyIn U (fun i => ETHBinsStandaloneScratch.bins (Parameters.scale (PL i))) :=
  PolyIn.mono (fun i => le_of_eq rfl) pS

/-! ## The scalar chain -/

theorem hBinsG : PolyIn U (fun i => WeightedBinsGeneric.bound (PL i)) := by
  refine PolyIn.mono (g := fun i => ETHBinsOutputClockScratch.joinedOutputClock (PL i) +
      (2 * Parameters.bins (PL i) + 2) + 1) (fun i => ?_) ?_
  · dsimp only
    unfold WeightedBinsGeneric.bound
    have := ETHBinsOutputClockScratch.joinedBound_le_output_clock (PL i)
    omega
  · simp only [ETHBinsOutputClockScratch.joinedOutputClock, ETHScalePolynomialClock.polynomialClock,
      ETHScalePolynomialClock.logEnvelope, ETHScalePolynomialClock.preEnvelope,
      ETHScalePolynomialClock.width, ETHScalePolynomialClock.rawMax,
      ETHBinsOutputClockScratch.outputSize]
    atoms
    have := pBinsS
    pr

theorem hPrep : PolyIn U (fun i =>
    MatrixWeightedOrderPreparation.prepCost (gI i).vertices (sI i - 3) (4 * sI i)) := by
  refine PolyIn.mono (fun i => ProtectedBudgetNormalizationScratch.prepCost_quartic _ _ _
    ((gI i).vertices + 4 * sI i + 1) (by omega) (by omega) (by omega) (by omega)) ?_
  atoms
  pr

theorem hGQ : PolyIn U (fun i => WeightedGraphQJoined.bound (gI i) (sI i) (eI i)) := by
  refine PolyIn.mono (fun i => WeightedLevelPublicClock.graphQ_bound_public i.G (sI i)) ?_
  simp only [MatrixWeightedGraphItemCountsPrelude.cost, MatrixAddressMachine.exactTime]
  atoms
  have := pEnc
  have := hPrep
  pr

theorem hFull : PolyIn U (fun i => BalanceOrderCleanup.fullTime (Parameters.scale (PL i))) := by
  refine PolyIn.mono (g := fun i => 1000000000 * (tI i + 1) ^ 2) (fun i => ?_) ?_
  · simpa only [Parameters.balanceOrder, Parameters.balanceExponent,
      BalanceOrderArithmetic.exponent] using
      BalanceOrderCost.fullTime_output_bound (Parameters.scale (PL i))
  · atoms
    pr

theorem hSD : PolyIn U (fun i => WeightedScaleDerivedFromBins.bound (PL i)) := by
  simp only [WeightedScaleDerivedFromBins.bound, FirstExponentArithmetic.bound]
  atoms
  have := hFull
  pr

theorem hMT : PolyIn U (fun i => WeightedMTPrefix.bound (aI i) (rxI i) (qI i) (tI i)) := by
  simp only [WeightedMTPrefix.bound, WeightedMQJoin.cost, WeightedMJoin.cost,
    MatrixAddressMachine.exactTime]
  atoms
  pr

theorem hX : PolyIn U (fun i => PrimeSampler.threshold (qI i) (tI i) (mI i)) := by
  simp only [PrimeSampler.threshold]
  atoms
  pr

theorem hCPR : PolyIn U (fun i => ChosenPrimeRaw.bound (PrimeSampler.threshold (qI i) (tI i) (mI i))) := by
  simp only [ChosenPrimeRaw.bound, PrimeSamplerSearch.stepBound]
  have := hX
  pr

theorem hPowP : PolyIn U (fun i => MatrixWeightedPower.powerBound (pI i) (tI i)) := by
  refine PolyIn.mono (fun i => powerBound_le _ _) ?_
  atoms
  pr

theorem hTS : PolyIn U (fun i => WeightedThresholdToSize.bound (qI i) (tI i) (mI i)) := by
  simp only [WeightedThresholdToSize.bound, Paper2.WeightedThresholdArithmetic.size,
    ChosenSizeArbitraryWriter.bound, ChosenSizeSuffix.bound]
  atoms
  have := hX
  have := hCPR
  have := hPowP
  pr

theorem hScalar : PolyIn U (fun i =>
    WeightedScalarFromRawDimensions.bound (PL i) (gI i) (eI i) (qI i)) := by
  simp only [WeightedScalarFromRawDimensions.bound, WeightedScalarFromRawRows.bound,
    WeightedScalarComplete.bound, WeightedPrefixAT.bound, WeightedBinsGraphQ.bound,
    WeightedActualSizeSuffix.bound]
  atoms
  have := hBinsG
  have := hGQ
  have := hSD
  have := hMT
  have := hTS
  pr

/-! ## The level-field clocks -/

theorem hP16 : PolyIn U (fun i => WeightedLevelStagePrefix.publicBound16 (PL i) (gI i) (eI i)
    noW3 (aI i) (sI i) (qI i) (LI' i)) := by
  simp only [WeightedLevelStagePrefix.publicBound16, WeightedLevelPublicClock.publicBound,
    WeightedLevelPublicClock.clearPublic, WeightedLevelColumnSave.saveCost,
    ColumnInputStaging.stageCost, ColumnWriterJoin.joinCost, ColumnScalarOutput.polynomialCost,
    MatrixAddressMachine.exactTime, noW3, List.length_nil,
    Finset.sum_const_zero]
  atoms
  have := hScalar
  pr

theorem hCols : PolyIn U (fun i => MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) := by
  refine PolyIn.mono (g := fun i => cyI i ^ (sI i + 1) *
      MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i) (fun i => le_of_eq rfl) ?_
  atoms
  pr

theorem hPowB : PolyIn U (fun i => MatrixWeightedPower.powerBound
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i)) (sI i)) := by
  refine PolyIn.mono (fun i => powerBound_le _ _) ?_
  atoms
  pr

theorem hP1346 : PolyIn U (fun i => WeightedLevelFieldsIdentity.publicBound1346 (PL i) (gI i) (eI i)
    noW3 (aI i) (sI i) (qI i) (LI' i)
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
    (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i)) := by
  simp only [WeightedLevelFieldsIdentity.publicBound1346, MatrixAddressMachine.exactTime,
    noW3, List.length_nil]
  atoms
  have := hP16
  have := hCols
  have := hPowB
  pr

theorem hP15 : PolyIn U (fun i => WeightedLevelFields15.publicBound15 (PL i) (gI i) (eI i)
    noW3 (aI i) (sI i) (qI i) (LI' i)
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
    (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i)) := by
  simp only [WeightedLevelFields15.publicBound15, MatrixAddressMachine.exactTime]
  atoms
  have := hP1346
  pr

theorem hCopy : PolyIn U (fun i => EntryFamilyLevel.copyBound (aI i) (qI i) (LI' i) (rxI i) (tI i)) := by
  simp only [EntryFamilyLevel.copyBound]
  atoms
  pr

theorem hTT : PolyIn U (fun i => Paper2.WeightedThresholdArithmetic.totalTime (qI i) (tI i) (mI i)) := by
  refine PolyIn.mono (fun i => Paper2.WeightedThresholdArithmetic.totalTime_polynomial _ _ _) ?_
  simp only [Paper2.WeightedThresholdArithmetic.size]
  atoms
  have := hX
  pr

theorem hAsm : PolyIn U (fun i => EntryFamilyAssembly.assemblyBound (aI i) (qI i) (tI i) (rxI i)) := by
  simp only [EntryFamilyAssembly.assemblyBound, PrimeFromWords.fromBound, PrimeWordExact.wordBound,
    FamilyTableLoop.bodyBound, MatrixAddressMachine.exactTime]
  atoms
  have := hX
  have := hCPR
  have := hTT
  pr

/-- The admitted family clock of the level controller, at every level. -/
noncomputable def famClock (i : LI) : ℕ :=
  WeightedLevelFields15.publicBound15 (PL i) (gI i) (eI i) noW3 (aI i) (sI i)
      (qI i) (LI' i) (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
      (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i) +
    EntryFamilyLevel.copyBound (aI i) (qI i) (LI' i) (rxI i) (tI i) +
    EntryFamilyAssembly.assemblyBound (aI i) (qI i) (tI i) (rxI i) + 6

/-- Segment 1 core: ONE pair of absolute constants bounds the family clock at every level. -/
theorem famClock_poly : PolyIn U famClock := by
  unfold famClock
  have := hP15
  have := hCopy
  have := hAsm
  pr

#print axioms hScalar
#print axioms hP15
#print axioms hAsm
#print axioms famClock_poly


end EthInapproximability.CurrentPaper.EntryClockPoly3
