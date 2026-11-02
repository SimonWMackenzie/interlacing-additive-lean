import EthInapproximability.CurrentPaper.WeightedLevelColumnSave
import EthInapproximability.CurrentPaper.QPublicGrowth
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import Mathlib.Tactic.DeriveFintype

/-! Unit 2, segment 4 (q public clock, consumed) and the public clock of the
checked scalar/column part of one weighted level.

1. `graphQ_bound_public`: the q arithmetic term `QArithmeticJoined.cost s |E|`
   inside the admitted `WeightedGraphQJoined.bound` is majorized by the
   checked private `QPublicGrowth.arithmetic_cost_graph_le`, polynomially in
   the literal graph-byte length and unary `s`. (The same-run cleanup bound
   for `QFinal.same_graph_q_clean_run` is the separately checked
   `QPublicGrowth.same_graph_q_clean_run_public`; it is not used here, because
   the actual weighted chain runs the uncleaned `WeightedGraphQJoined` q phase,
   whose clock contains only the arithmetic term.)
2. `clearCost_le_public`: the column-stage clearing time
   `WeightedColumnActualStage.clearCost`, which the frozen column stage charges
   by the actual lengths of the reached writer cells (hence through the
   existential scalar scratch banks), is bounded by the initial writer
   lengths plus `40 * perStep * u`, where `u` is the actual scalar run time and
   `perStep` is the fixed push constant of the fixed scalar controller
   (`BitMachineStackGrowth.run_growth`).
3. `save_column_public`: the segment-2 controller with that bound
   substituted, giving ONE clock expressed only in the six raw words, the
   literal graph code, the physically produced unary words (`q`, `a`, `s`,
   `L`, rows, columns) and the initial writer lengths. No existential bank
   appears in the clock.

Coefficient caveat: `perStep` is a finite classical supremum over the fixed
program's labels (`Finset.univ.sup`), not an evaluated numeral. The three
`deriving instance Fintype` lines below only supply the finiteness instances
that the frozen label inductives did not derive; they add no axiom. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelPublicClock

open Turing BitMachineEncoding BitMachineStackEmbedding

deriving instance Fintype for MatrixWeightedOrderPreparation.Label
deriving instance Fintype for WeightedColumnActualStage.ClearLabel
deriving instance Fintype for ColumnWriterJoin.Label

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

/-! ## q arithmetic inside the actual scalar chain -/

theorem graphQ_bound_public {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (s : ℕ) :
    let g := EncodedETHSource.serializeGraph G
    WeightedGraphQJoined.bound g s (Fintype.card E) ≤
      101 * ((EncodedGraph.encode g).length + 1)^3 +
      (2 * g.vertices + 2) +
      MatrixWeightedGraphItemCountsPrelude.cost g.vertices s +
      MatrixWeightedOrderPreparation.prepCost g.vertices (s-3) (4*s) + 3 +
      QPublicGrowth.arithmeticCoefficient *
        (s + (EncodedGraph.encode g).length + 1) ^ 4 + 1 := by
  intro g
  have h : QArithmeticJoined.cost s (Fintype.card E) ≤
      QPublicGrowth.arithmeticCoefficient *
        (s + (EncodedGraph.encode g).length + 1) ^ 4 :=
    QPublicGrowth.arithmetic_cost_graph_le G s
  unfold WeightedGraphQJoined.bound
  omega

/-! ## Stack growth of the fixed scalar controller -/

/-- The fixed push constant of the frozen raw-dimension scalar controller. -/
def scalarPush : ℕ :=
  BitMachineStackGrowth.perStep WeightedScalarFromRawDimensions.program

theorem initial_writer (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (k : Fin 64) :
    WeightedScalarFromRawDimensions.initialBank i g W
      (WeightedColumnActualStage.writerSlots k) = W k :=
  WeightedRawColumnsSource.initial_writer i g W k

theorem scalar_growth (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (u : ℕ)
    (hrun : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩)
    (k : Fin 64) :
    (T (WeightedColumnActualStage.writerSlots k)).length ≤
      (W k).length + scalarPush * u := by
  have h := BitMachineStackGrowth.run_growth
    WeightedScalarFromRawDimensions.program
    (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      WeightedScalarFromRawDimensions.initialControl,
      WeightedScalarFromRawDimensions.initialBank i g W⟩ :
      TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _)
    u (WeightedColumnActualStage.writerSlots k)
  rw [hrun] at h
  simpa only [initial_writer, scalarPush] using h

/-- Public majorant of the charged column clear on the reached bank. -/
def clearPublic (W : Fin 64 → List Bool) (B : ℕ) : ℕ :=
  (∑ j : Fin 40, (W (WeightedColumnActualStage.clearCells j)).length) +
    40 * (scalarPush * B) + 42

theorem clearCost_le_public (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (u B : ℕ) (huB : u ≤ B)
    (hrun : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩) :
    WeightedColumnActualStage.clearCost
        (fun k => T (WeightedColumnActualStage.writerSlots k)) ≤
      clearPublic W B := by
  unfold WeightedColumnActualStage.clearCost clearPublic
  dsimp only
  have hsum : (∑ j : Fin 40,
      (T (WeightedColumnActualStage.writerSlots
        (WeightedColumnActualStage.clearCells j))).length) ≤
      ∑ j : Fin 40, ((W (WeightedColumnActualStage.clearCells j)).length +
        scalarPush * B) := by
    apply Finset.sum_le_sum
    intro j _
    have hg := scalar_growth i g W T u hrun (WeightedColumnActualStage.clearCells j)
    have hm : scalarPush * u ≤ scalarPush * B := Nat.mul_le_mul_left _ huB
    omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-! ## The public clock of the segment-2 controller -/

/-- One public clock for the scalar/retention/column controller. -/
def publicBound (i : Parameters.Input) (g : EncodedGraph.Graph) (e : ℕ)
    (W : Fin 64 → List Bool) (a s q L : ℕ) : ℕ :=
  let B := WeightedScalarFromRawDimensions.bound i g e q
  B + WeightedLevelColumnSave.saveCost a q L s +
    (clearPublic W B + ColumnInputStaging.stageCost s i.rows i.columns +
      ColumnWriterJoin.joinCost a s q L i.rows i.columns + 2) + 2

theorem save_column_public {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (i : Parameters.Input)
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h27 : W 27 = []) (h63 : W 63 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let g := EncodedETHSource.serializeGraph G
    let s := Parameters.bins i
    let q := ParameterizedNP.GuardedSourceSlab.q2 G s
    let a := Parameters.firstExponent i
    let L := PrimeSampler.size q (Parameters.balanceOrder i)
      (Construction.qOne a * i.rows)
    let W'' := Function.update
      (Function.update W 27 (List.replicate i.columns true))
      17 (List.replicate i.rows true)
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
      let T := WeightedScalarComplete.finalBank i g W'' F Q P i.rows q
      ∃ u ≤ publicBound i g (Fintype.card E) W a s q L,
        ((advance WeightedLevelColumnSave.program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            WeightedLevelColumnSave.initialControl,
            WeightedLevelColumnSave.initialBank i g W⟩ :
            TM2.Cfg (fun _ : WeightedLevelColumnSave.Stack => Bool) _ _) =
          ⟨none, WeightedLevelColumnSave.initialControl,
            WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns⟩ ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.wcell 26) =
          List.replicate (MatrixStage4Digits.wordBase a s i.columns) true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.wcell 29) =
          List.replicate (MatrixStage4Digits.binBase a s q i.columns) true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.wcell 21) =
          List.replicate (MatrixStage4Codes.cols a s q i.columns) true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.wcell 28) = List.replicate s true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.wcell 17) = List.replicate i.rows true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.wcell 27) = List.replicate i.columns true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.save 0) = List.replicate a true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.save 1) = List.replicate q true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.save 2) = List.replicate L true ∧
        WeightedLevelColumnSave.exitBank T a s q L i.rows i.columns
            (WeightedLevelColumnSave.save 3) = List.replicate (s * L) true := by
  intro g s q a L W''
  obtain ⟨u, hu, -, F, Q, P, hrun, hr17, hr27, hr28, hr54, hr56, hr57⟩ :=
    WeightedRawDimensionsFrame.source_run_framed i G W h17 h62 h27 h63 h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T
  have hrun' : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩ := hrun
  have hu' : u ≤ WeightedScalarFromRawDimensions.bound i g
      (Fintype.card E) q := hu
  obtain ⟨w, hw, hfull⟩ := WeightedLevelColumnSave.composite_run i g W T u
    a s q L i.rows i.columns hrun' hr28 hr17 hr27 hr54 hr56 hr57
  have hclear := clearCost_le_public i g W T u
    (WeightedScalarFromRawDimensions.bound i g (Fintype.card E) q) hu' hrun'
  have h28s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (28 : Fin 64) := by decide
  have h17s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (17 : Fin 64) := by decide
  have h27s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (27 : Fin 64) := by decide
  have h28c : ∀ j : Fin 40, WeightedColumnActualStage.clearCells j ≠ (28 : Fin 64) := by
    decide
  have h17c : ∀ j : Fin 40, WeightedColumnActualStage.clearCells j ≠ (17 : Fin 64) := by
    decide
  have h27c : ∀ j : Fin 40, WeightedColumnActualStage.clearCells j ≠ (27 : Fin 64) := by
    decide
  obtain ⟨o26, o29, o21⟩ :=
    WeightedColumnActualStage.exit_outputs T a s q L i.rows i.columns
  refine ⟨w, ?_, hfull, o26, o29, o21, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · unfold publicBound
    unfold WeightedColumnActualStage.stageBound at hw
    dsimp only
    omega
  · exact (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      28 h28s h28c).trans hr28
  · exact (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      17 h17s h17c).trans hr17
  · exact (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      27 h27s h27c).trans hr27

#print axioms graphQ_bound_public
#print axioms initial_writer
#print axioms scalar_growth
#print axioms clearCost_le_public
#print axioms save_column_public

end
end EthInapproximability.CurrentPaper.WeightedLevelPublicClock
