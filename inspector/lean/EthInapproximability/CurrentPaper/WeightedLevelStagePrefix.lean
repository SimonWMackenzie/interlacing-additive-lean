import EthInapproximability.CurrentPaper.WeightedLevelIdentity

/-! Unit 2, segment 5 (partial, continued): the persistent field 16
(`stagePrefixRows = s*L`) moved into writer 16.

One fixed controller: the segment-2 controller (`WeightedLevelColumnSave.program`),
then a charged pop-until-empty clear of writer 16 (its reached content is not
assumed blank; every discarded cell is charged), then a charged copy of the
retained `s*L` word (fresh cell `save 3`) into writer 16. The public clock
bounds the clear by the initial length of writer 16 plus the scalar
controller's fixed push constant times the scalar time bound
(`BitMachineStackGrowth`), since neither the retention copies nor the column
stage touch writer 16. The same-constructor identity then covers seven
persistent writer fields: 16, 17, 21, 26, 27, 28, 29 of the SAME `actualD`,
plus the retained `a`, `q`, `L`. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelStagePrefix

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevelColumnSave

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

inductive ClearLabel where
  | pop | stop
  deriving DecidableEq, Fintype

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)
  | .pop => BitMachineClearBank.clearStep (wcell 16) ClearLabel.pop ClearLabel.stop
  | .stop => .halt

theorem clear_run (S : Stack → List Bool) :
    ((advance clearProgram)^[(S (wcell 16)).length + 2])
      (⟨some ClearLabel.pop, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), Function.update S (wcell 16) []⟩ := by
  have h := BitMachineClearBank.clear_one_run clearProgram (wcell 16)
    ClearLabel.pop ClearLabel.stop rfl () S
  rw [show (S (wcell 16)).length + 2 = 1 + ((S (wcell 16)).length + 1) by omega,
    Function.iterate_add_apply, h]
  rfl

def copy16 : Fin 3 ↪ Stack :=
  ⟨![save 3, wcell 16, save 4], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def tailProgram := BitMachineRawSequence.program clearProgram
  (copyProgram copy16) BitMachineCopy.Label.scan
  (((), none) : Unit × Option Bool) (none : Option Bool)

def tailInitial := ((((), none) : Unit × Option Bool), (none : Option Bool))

def program := BitMachineRawSequence.program WeightedLevelColumnSave.program
  tailProgram (BitMachineRawSequence.leftLabel ClearLabel.pop)
  WeightedLevelColumnSave.initialControl tailInitial

def initialControl := (WeightedLevelColumnSave.initialControl, tailInitial)

theorem tail_run (X : Stack → List Bool) (sL : ℕ)
    (h3 : X (save 3) = List.replicate sL true) (h4 : X (save 4) = []) :
    ∃ t ≤ (X (wcell 16)).length + 2 + (2 * sL + 2) + 1,
      ((advance tailProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ClearLabel.pop), tailInitial, X⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, tailInitial, Function.update X (wcell 16) (List.replicate sL true)⟩ := by
  let Y := Function.update X (wcell 16) []
  have hY3 : Y (copy16 0) = List.replicate sL true := by
    change Function.update X (wcell 16) [] (save 3) = _
    rw [Function.update_of_ne (by intro e; cases e)]
    exact h3
  have hY4 : Y (copy16 2) = [] := by
    change Function.update X (wcell 16) [] (save 4) = _
    rw [Function.update_of_ne (by intro e; cases e)]
    exact h4
  have hc := copy_run copy16 Y hY4
  rw [hY3, List.length_replicate] at hc
  have hfin : Function.update Y (copy16 1)
      (List.replicate sL true ++ Y (copy16 1)) =
      Function.update X (wcell 16) (List.replicate sL true) := by
    have e1 : copy16 1 = wcell 16 := rfl
    rw [e1]
    simp [Y]
  rw [hfin] at hc
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs clearProgram
    (copyProgram copy16) ClearLabel.pop BitMachineCopy.Label.scan
    (((), none) : Unit × Option Bool) (((), none) : Unit × Option Bool)
    (none : Option Bool) (none : Option Bool)
    X Y (Function.update X (wcell 16) (List.replicate sL true))
    ((X (wcell 16)).length + 2) (2 * sL + 2) (clear_run X) hc
  exact ⟨t, ht, by simpa only [tailProgram, tailInitial] using hr⟩

/-- Public clock of this controller. -/
def publicBound16 (i : Parameters.Input) (g : EncodedGraph.Graph) (e : ℕ)
    (W : Fin 64 → List Bool) (a s q L : ℕ) : ℕ :=
  WeightedLevelPublicClock.publicBound i g e W a s q L +
    ((W 16).length +
      WeightedLevelPublicClock.scalarPush *
        WeightedScalarFromRawDimensions.bound i g e q +
      2 + (2 * (s * L) + 2) + 1) + 1

theorem bank16 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 16 =
      List.replicate d.stagePrefixRows true := by
  simp [MatrixWeightedEntryController.persistentBank]

variable {VG EG : Type} [Fintype VG] [DecidableEq VG]
  [Fintype EG] [DecidableEq EG]

/-- One level, same constructor, one public clock: the seven persistent
writer fields 16, 17, 21, 26, 27, 28, 29 of `actualD` for the SAME step,
physically produced, plus the retained `a`, `q`, `L`. -/
theorem level_stage_prefix_identity (G : EndpointGraph VG EG) (c b y lvl : ℕ)
    (M : Iteration.Matrix) (W : Fin 64 → List Bool)
    (h17 : W 17 = []) (h62 : W 62 = [])
    (h27 : W 27 = []) (h63 : W 63 = [])
    (h28 : W 28 = []) (h61 : W 61 = [])
    (h7 : W 7 = []) (h8 : W 8 = []) (h9 : W 9 = [])
    (h10 : W 10 = []) (h11 : W 11 = []) (h12 : W 12 = [])
    (h13 : W 13 = []) (h14 : W 14 = [])
    (h15 : W 15 = []) (h18 : W 18 = [])
    (h54 : W 54 = []) (h55 : W 55 = []) (h56 : W 56 = [])
    (h57 : W 57 = []) (h58 : W 58 = []) (h60 : W 60 = []) :
    let d := ProtectedFullBankBridgeScratch.actualD G c b y lvl M
    let i := Iteration.stepParameters G c b y lvl M
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
      let X := Function.update (exitBank T a s q L i.rows i.columns)
        (wcell 16) (List.replicate (s * L) true)
      ∃ u ≤ publicBound16 i g (Fintype.card EG) W a s q L,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
            initialControl, WeightedLevelColumnSave.initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, initialControl, X⟩ ∧
        X (wcell 16) = MatrixWeightedEntryController.persistentBank d 16 ∧
        X (wcell 17) = MatrixWeightedEntryController.persistentBank d 17 ∧
        X (wcell 27) = MatrixWeightedEntryController.persistentBank d 27 ∧
        X (wcell 28) = MatrixWeightedEntryController.persistentBank d 28 ∧
        X (wcell 21) = MatrixWeightedEntryController.persistentBank d 21 ∧
        X (wcell 26) = MatrixWeightedEntryController.persistentBank d 26 ∧
        X (wcell 29) = MatrixWeightedEntryController.persistentBank d 29 ∧
        X (save 0) = List.replicate (Iteration.a G c b y lvl M) true ∧
        X (save 1) = List.replicate (Iteration.q₂ G c b y lvl M) true ∧
        X (save 2) = List.replicate (Iteration.labels G c b y lvl M) true ∧
        X (save 3) = List.replicate d.stagePrefixRows true := by
  intro d i g s q a L W''
  obtain ⟨p17, p27, p28, p21, p26, p29, pst⟩ :=
    WeightedLevelIdentity.persistent_fields G c b y lvl M
  obtain ⟨u, hu, -, F, Q, P, hrun, hr17, hr27, hr28, hr54, hr56, hr57⟩ :=
    WeightedRawDimensionsFrame.source_run_framed i G W h17 h62 h27 h63 h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T X
  have hrun' : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩ := hrun
  have hu' : u ≤ WeightedScalarFromRawDimensions.bound i g
      (Fintype.card EG) q := hu
  obtain ⟨w, hw, hfull⟩ := composite_run i g W T u
    a s q L i.rows i.columns hrun' hr28 hr17 hr27 hr54 hr56 hr57
  have hclear := WeightedLevelPublicClock.clearCost_le_public i g W T u
    (WeightedScalarFromRawDimensions.bound i g (Fintype.card EG) q) hu' hrun'
  -- writer 16 is untouched by the retention copies and the column stage
  have h16s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (16 : Fin 64) := by decide
  have h16c : ∀ j : Fin 40, WeightedColumnActualStage.clearCells j ≠ (16 : Fin 64) := by
    decide
  have hx16 : exitBank T a s q L i.rows i.columns (wcell 16) =
      T (WeightedColumnActualStage.writerSlots 16) :=
    WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns 16 h16s h16c
  have hg16 := WeightedLevelPublicClock.scalar_growth i g W T u hrun' 16
  have hm : WeightedLevelPublicClock.scalarPush * u ≤
      WeightedLevelPublicClock.scalarPush *
        WeightedScalarFromRawDimensions.bound i g (Fintype.card EG) q :=
    Nat.mul_le_mul_left _ hu'
  obtain ⟨t, ht, htail⟩ := tail_run (exitBank T a s q L i.rows i.columns) (s * L)
    rfl rfl
  obtain ⟨v, hv, hr⟩ := BitMachineRawSequence.runs
    WeightedLevelColumnSave.program tailProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (BitMachineRawSequence.leftLabel ClearLabel.pop)
    WeightedLevelColumnSave.initialControl WeightedLevelColumnSave.initialControl
    tailInitial tailInitial
    (WeightedLevelColumnSave.initialBank i g W)
    (exitBank T a s q L i.rows i.columns) X w t hfull htail
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
  have o28 := (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      28 h28s h28c).trans hr28
  have o17 := (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      17 h17s h17c).trans hr17
  have o27 := (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      27 h27s h27c).trans hr27
  have nX (k : Fin 64) (hk : k ≠ 16) :
      X (wcell k) = exitBank T a s q L i.rows i.columns (wcell k) := by
    have hne : wcell k ≠ wcell 16 := by
      intro e
      exact hk (WeightedColumnActualStage.writerSlots.injective (Sum.inl_injective e))
    simp only [X, Function.update_of_ne hne]
  have nS (j : Fin 7) :
      X (save j) = exitBank T a s q L i.rows i.columns (save j) := by
    have hne : save j ≠ wcell 16 := by intro e; cases e
    simp only [X, Function.update_of_ne hne]
  refine ⟨v, ?_, by simpa only [program, initialControl] using hr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl16 : (exitBank T a s q L i.rows i.columns (wcell 16)).length =
        (T (WeightedColumnActualStage.writerSlots 16)).length := by rw [hx16]
    unfold WeightedColumnActualStage.stageBound at hw
    show v ≤ (WeightedScalarFromRawDimensions.bound i g (Fintype.card EG) q +
        saveCost a q L s +
        (WeightedLevelPublicClock.clearPublic W
            (WeightedScalarFromRawDimensions.bound i g (Fintype.card EG) q) +
          ColumnInputStaging.stageCost s i.rows i.columns +
          ColumnWriterJoin.joinCost a s q L i.rows i.columns + 2) + 2) +
      ((W 16).length + WeightedLevelPublicClock.scalarPush *
          WeightedScalarFromRawDimensions.bound i g (Fintype.card EG) q +
        2 + (2 * (s * L) + 2) + 1) + 1
    omega
  · simp only [X, Function.update_self]
    rw [bank16, pst]
  · rw [nX 17 (by decide)]; exact o17.trans p17.symm
  · rw [nX 27 (by decide)]; exact o27.trans p27.symm
  · rw [nX 28 (by decide)]; exact o28.trans p28.symm
  · rw [nX 21 (by decide)]; exact o21.trans p21.symm
  · rw [nX 26 (by decide)]; exact o26.trans p26.symm
  · rw [nX 29 (by decide)]; exact o29.trans p29.symm
  · rw [nS 0]; rfl
  · rw [nS 1]; rfl
  · rw [nS 2]; rfl
  · rw [nS 3, pst]; rfl

#print axioms clear_run
#print axioms tail_run
#print axioms bank16
#print axioms level_stage_prefix_identity

end
end EthInapproximability.CurrentPaper.WeightedLevelStagePrefix
