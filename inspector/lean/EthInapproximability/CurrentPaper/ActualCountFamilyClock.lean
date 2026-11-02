import EthInapproximability.CurrentPaper.ActualCountClock

/-! Mechanical rebasing of the production `EntryClockPoly3Clock` polynomial
clock proof to the sum of actual machine counts `ActualCountClock.A`.
The only changed atom proof is `actual_atom_bounds`; no coarse
`oneLevelBound` premise is used. This is a private experiment. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualCountFamilyClock

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualCountClock

/-! ## Atoms -/

theorem pT : PolyIn A (fun i => tI i) :=
  PolyIn.of_le (fun i => by obtain ⟨h, -⟩ := actual_atom_bounds i; exact h)

theorem p2T : PolyIn A (fun i => 2 ^ tI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, h, -⟩ := actual_atom_bounds i; exact h)

theorem pA : PolyIn A (fun i => aI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem p2A : PolyIn A (fun i => 2 ^ aI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pS : PolyIn A (fun i => sI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pQOne : PolyIn A (fun i => Construction.qOne (aI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pFL : PolyIn A (fun i => Construction.firstLength (aI i) (sI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pQ : PolyIn A (fun i => qI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pRx : PolyIn A (fun i => rxI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pCy : PolyIn A (fun i => cyI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pL : PolyIn A (fun i => LI' i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pP : PolyIn A (fun i => pI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pPT : PolyIn A (fun i => pI i ^ tI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pWB : PolyIn A (fun i => MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pBB : PolyIn A (fun i => MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pBBS : PolyIn A (fun i => MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pCYS : PolyIn A (fun i => cyI i ^ (sI i + 1)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pScale : PolyIn A (fun i => Parameters.scale (PL i)) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pSC : PolyIn A (fun i => (PL i).sourceConstant) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pND : PolyIn A (fun i => (PL i).nextDepth) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pCost : PolyIn A (fun i => (PL i).cost) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pEdges : PolyIn A (fun i => (PL i).edges) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pEll : PolyIn A (fun i => ell3 i.G) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pVert : PolyIn A (fun i => (gI i).vertices) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := actual_atom_bounds i; exact h)

theorem pE : PolyIn A (fun i => eI i) :=
  PolyIn.of_le (fun i => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := actual_atom_bounds i; exact h)

/-- Put every atom in context. -/
macro "atomsActual" : tactic => `(tactic| (have := @pT; have := @p2T; have := @pA; have := @p2A; have := @pS; have := @pQOne; have := @pFL; have := @pQ; have := @pRx; have := @pCy; have := @pL; have := @pP; have := @pPT; have := @pWB; have := @pBB; have := @pBBS; have := @pCYS; have := @pScale; have := @pSC; have := @pND; have := @pCost; have := @pEdges; have := @pEll; have := @pVert; have := @pE))

/-- Close a `PolyIn` goal with atomsActual matched up to reducible unfolding only. -/
macro "prActual" : tactic => `(tactic| repeat' (first
  | with_reducible assumption
  | with_reducible exact PolyIn.const _
  | with_reducible apply PolyIn.add
  | with_reducible apply PolyIn.mul
  | with_reducible apply PolyIn.pow
  | with_reducible apply PolyIn.sub
  | with_reducible apply PolyIn.max))

/-- The empty writer bank (`noW3`, restated). -/
def noW3 : Fin 64 → List Bool := fun _ => []

theorem pEnc : PolyIn A (fun i => (EncodedGraph.encode (gI i)).length) := pEll

theorem pBinsS : PolyIn A (fun i => ETHBinsStandaloneScratch.bins (Parameters.scale (PL i))) :=
  PolyIn.mono (fun i => le_of_eq rfl) pS

/-! ## The scalar chain -/

theorem hBinsG : PolyIn A (fun i => WeightedBinsGeneric.bound (PL i)) := by
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
    atomsActual
    have := pBinsS
    prActual

theorem hPrep : PolyIn A (fun i =>
    MatrixWeightedOrderPreparation.prepCost (gI i).vertices (sI i - 3) (4 * sI i)) := by
  refine PolyIn.mono (fun i => ProtectedBudgetNormalizationScratch.prepCost_quartic _ _ _
    ((gI i).vertices + 4 * sI i + 1) (by omega) (by omega) (by omega) (by omega)) ?_
  atomsActual
  prActual

theorem hGQ : PolyIn A (fun i => WeightedGraphQJoined.bound (gI i) (sI i) (eI i)) := by
  refine PolyIn.mono (fun i => WeightedLevelPublicClock.graphQ_bound_public i.G (sI i)) ?_
  simp only [MatrixWeightedGraphItemCountsPrelude.cost, MatrixAddressMachine.exactTime]
  atomsActual
  have := pEnc
  have := hPrep
  prActual

theorem hFull : PolyIn A (fun i => BalanceOrderCleanup.fullTime (Parameters.scale (PL i))) := by
  refine PolyIn.mono (g := fun i => 1000000000 * (tI i + 1) ^ 2) (fun i => ?_) ?_
  · simpa only [Parameters.balanceOrder, Parameters.balanceExponent,
      BalanceOrderArithmetic.exponent] using
      BalanceOrderCost.fullTime_output_bound (Parameters.scale (PL i))
  · atomsActual
    prActual

theorem hSD : PolyIn A (fun i => WeightedScaleDerivedFromBins.bound (PL i)) := by
  simp only [WeightedScaleDerivedFromBins.bound, FirstExponentArithmetic.bound]
  atomsActual
  have := hFull
  prActual

theorem hMT : PolyIn A (fun i => WeightedMTPrefix.bound (aI i) (rxI i) (qI i) (tI i)) := by
  simp only [WeightedMTPrefix.bound, WeightedMQJoin.cost, WeightedMJoin.cost,
    MatrixAddressMachine.exactTime]
  atomsActual
  prActual

theorem hX : PolyIn A (fun i => PrimeSampler.threshold (qI i) (tI i) (mI i)) := by
  simp only [PrimeSampler.threshold]
  atomsActual
  prActual

theorem hCPR : PolyIn A (fun i => ChosenPrimeRaw.bound (PrimeSampler.threshold (qI i) (tI i) (mI i))) := by
  simp only [ChosenPrimeRaw.bound, PrimeSamplerSearch.stepBound]
  have := hX
  prActual

theorem hPowP : PolyIn A (fun i => MatrixWeightedPower.powerBound (pI i) (tI i)) := by
  refine PolyIn.mono (fun i => powerBound_le _ _) ?_
  atomsActual
  prActual

theorem hTS : PolyIn A (fun i => WeightedThresholdToSize.bound (qI i) (tI i) (mI i)) := by
  simp only [WeightedThresholdToSize.bound, Paper2.WeightedThresholdArithmetic.size,
    ChosenSizeArbitraryWriter.bound, ChosenSizeSuffix.bound]
  atomsActual
  have := hX
  have := hCPR
  have := hPowP
  prActual

theorem hScalar : PolyIn A (fun i =>
    WeightedScalarFromRawDimensions.bound (PL i) (gI i) (eI i) (qI i)) := by
  simp only [WeightedScalarFromRawDimensions.bound, WeightedScalarFromRawRows.bound,
    WeightedScalarComplete.bound, WeightedPrefixAT.bound, WeightedBinsGraphQ.bound,
    WeightedActualSizeSuffix.bound]
  atomsActual
  have := hBinsG
  have := hGQ
  have := hSD
  have := hMT
  have := hTS
  prActual

/-! ## The level-field clocks -/

theorem hP16 : PolyIn A (fun i => WeightedLevelStagePrefix.publicBound16 (PL i) (gI i) (eI i)
    noW3 (aI i) (sI i) (qI i) (LI' i)) := by
  simp only [WeightedLevelStagePrefix.publicBound16, WeightedLevelPublicClock.publicBound,
    WeightedLevelPublicClock.clearPublic, WeightedLevelColumnSave.saveCost,
    ColumnInputStaging.stageCost, ColumnWriterJoin.joinCost, ColumnScalarOutput.polynomialCost,
    MatrixAddressMachine.exactTime, noW3, List.length_nil,
    Finset.sum_const_zero]
  atomsActual
  have := hScalar
  prActual

theorem hCols : PolyIn A (fun i => MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) := by
  refine PolyIn.mono (g := fun i => cyI i ^ (sI i + 1) *
      MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i) (fun i => le_of_eq rfl) ?_
  atomsActual
  prActual

theorem hPowB : PolyIn A (fun i => MatrixWeightedPower.powerBound
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i)) (sI i)) := by
  refine PolyIn.mono (fun i => powerBound_le _ _) ?_
  atomsActual
  prActual

theorem hP1346 : PolyIn A (fun i => WeightedLevelFieldsIdentity.publicBound1346 (PL i) (gI i) (eI i)
    noW3 (aI i) (sI i) (qI i) (LI' i)
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
    (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i)) := by
  simp only [WeightedLevelFieldsIdentity.publicBound1346, MatrixAddressMachine.exactTime,
    noW3, List.length_nil]
  atomsActual
  have := hP16
  have := hCols
  have := hPowB
  prActual

theorem hP15 : PolyIn A (fun i => WeightedLevelFields15.publicBound15 (PL i) (gI i) (eI i)
    noW3 (aI i) (sI i) (qI i) (LI' i)
    (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
    (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i)) := by
  simp only [WeightedLevelFields15.publicBound15, MatrixAddressMachine.exactTime]
  atomsActual
  have := hP1346
  prActual

theorem hCopy : PolyIn A (fun i => EntryFamilyLevel.copyBound (aI i) (qI i) (LI' i) (rxI i) (tI i)) := by
  simp only [EntryFamilyLevel.copyBound]
  atomsActual
  prActual

theorem hTT : PolyIn A (fun i => Paper2.WeightedThresholdArithmetic.totalTime (qI i) (tI i) (mI i)) := by
  refine PolyIn.mono (fun i => Paper2.WeightedThresholdArithmetic.totalTime_polynomial _ _ _) ?_
  simp only [Paper2.WeightedThresholdArithmetic.size]
  atomsActual
  have := hX
  prActual

theorem hAsm : PolyIn A (fun i => EntryFamilyAssembly.assemblyBound (aI i) (qI i) (tI i) (rxI i)) := by
  simp only [EntryFamilyAssembly.assemblyBound, PrimeFromWords.fromBound, PrimeWordExact.wordBound,
    FamilyTableLoop.bodyBound, MatrixAddressMachine.exactTime]
  atomsActual
  have := hX
  have := hCPR
  have := hTT
  prActual

/-- The admitted family clock of the level controller, at every level. -/
noncomputable def famClock (i : LI) : ℕ :=
  WeightedLevelFields15.publicBound15 (PL i) (gI i) (eI i) noW3 (aI i) (sI i)
      (qI i) (LI' i) (MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i))
      (MatrixStage4Codes.cols (aI i) (sI i) (qI i) (cyI i)) (sI i) +
    EntryFamilyLevel.copyBound (aI i) (qI i) (LI' i) (rxI i) (tI i) +
    EntryFamilyAssembly.assemblyBound (aI i) (qI i) (tI i) (rxI i) + 6

/-- Segment 1 core: ONE pair of absolute constants bounds the family clock at every level. -/
theorem famClock_poly : PolyIn A famClock := by
  unfold famClock
  have := hP15
  have := hCopy
  have := hAsm
  prActual


#print axioms hScalar
#print axioms hP15
#print axioms hAsm

end EthInapproximability.CurrentPaper.ActualCountFamilyClock

