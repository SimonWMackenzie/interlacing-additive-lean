import EthInapproximability.CurrentPaper.WeightedColumnActualStage
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! Unit 2, segment 2 successor: the column stage on the actual writer bank,
with the scalar words that the frozen column cleanup consumes retained.

The frozen `WeightedColumnActualStage.column_stage_run` (checked privately by
lane `repair:b-weighted-column-stage`) ends with writer 54/56/57 (`a`, `q`,
`L`) emptied by the frozen `ColumnWriterJoin` cleanup. The raw Stage--4 row
decoder and the persistent entry bank still need `L`, `s*L`, `a` and `q`.
This module builds ONE fixed controller on the scalar stack extended by a
fresh seven-cell region:

1. the frozen raw-dimension scalar controller
   (`WeightedScalarFromRawDimensions.program`, the witness of
   `WeightedRawDimensionsFrame.source_run_framed`), lifted unchanged;
2. three charged source-preserving copies writer54 -> save0 (`a`),
   writer56 -> save1 (`q`), writer57 -> save2 (`L`) (`copy_run`);
3. one charged unary multiplication writer28 x save2 -> save3 (`s*L`)
   (`multiply_run`), with blank scratch save4..6 restored;
4. the frozen lifted column stage (`WeightedColumnActualStage.lifted_run`:
   charged clear, three copies, frozen `ColumnWriterJoin` producer/cleanup).

Every handoff is charged by `BitMachineRawSequence.runs`. The exit bank is
explicit: the scalar-stack part is exactly the frozen
`WeightedColumnActualStage.exitBank`, and the fresh region holds exactly
`unary a, unary q, unary L, unary (s*L)` and three blank cells. No word is
supplied a second time: `a`, `q`, `L` are copied from the cells the frozen
scalar controller physically produced, and `s*L` is physically multiplied. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelColumnSave

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps

noncomputable section

abbrev Base := WeightedScalarFromRawDimensions.Stack
abbrev Stack := Base ⊕ Fin 7

def baseSlots : Base ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

/-- Writer cell `k` of the frozen scalar controller, inside the extended stack. -/
def wcell (k : Fin 64) : Stack := .inl (WeightedColumnActualStage.writerSlots k)

/-- Fresh retained region: 0 `a`, 1 `q`, 2 `L`, 3 `s*L`, 4..6 scratch. -/
def save (j : Fin 7) : Stack := .inr j

def copySlots (k : Fin 64) (j : Fin 7) (hj : j ≠ 4) : Fin 3 ↪ Stack :=
  ⟨![wcell k, save j, save 4], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def copyA : Fin 3 ↪ Stack := copySlots 54 0 (by decide)
def copyQ : Fin 3 ↪ Stack := copySlots 56 1 (by decide)
def copyL : Fin 3 ↪ Stack := copySlots 57 2 (by decide)

def mulSlots : Fin 6 ↪ Stack :=
  ⟨![wcell 28, save 2, save 4, save 5, save 6, save 3], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

/-! ## Programs -/

def scalarProgram := fun l =>
  stackStmt baseSlots (WeightedScalarFromRawDimensions.program l)

def columnProgram := fun l =>
  stackStmt baseSlots (WeightedColumnActualStage.liftedProgram l)

abbrev CopyControl := Option Bool

def saveL := BitMachineRawSequence.program (copyProgram copyL)
  (multiplyProgram mulSlots) MatrixAddressMachine.Label.outer
  (none : CopyControl) false

def saveQ := BitMachineRawSequence.program (copyProgram copyQ) saveL
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  (none : CopyControl) ((none : CopyControl), false)

def saveProgram := BitMachineRawSequence.program (copyProgram copyA) saveQ
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  (none : CopyControl) ((none : CopyControl), ((none : CopyControl), false))

def saveInitial : CopyControl × (CopyControl × (CopyControl × Bool)) :=
  (none, (none, (none, false)))

def tailProgram := BitMachineRawSequence.program saveProgram columnProgram
  (BitMachineRawSequence.leftLabel (WeightedColumnActualStage.ClearLabel.clear 0))
  saveInitial WeightedColumnActualStage.initial

def tailInitial := (saveInitial, WeightedColumnActualStage.initial)

/-- The fixed controller of this segment. -/
def program := BitMachineRawSequence.program scalarProgram tailProgram
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
  WeightedScalarFromRawDimensions.initialControl tailInitial

def initialControl := (WeightedScalarFromRawDimensions.initialControl, tailInitial)

/-! ## Banks -/

def savedWords (a q L sL : ℕ) : Fin 7 → List Bool :=
  ![List.replicate a true, List.replicate q true, List.replicate L true,
    List.replicate sL true, [], [], []]

def initialBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) : Stack → List Bool :=
  Sum.elim (WeightedScalarFromRawDimensions.initialBank i g W) (fun _ => [])

def exitBank (T : Base → List Bool) (a s q L rx cy : ℕ) : Stack → List Bool :=
  Sum.elim (WeightedColumnActualStage.exitBank T a s q L rx cy)
    (savedWords a q L (s * L))

def saveCost (a q L s : ℕ) : ℕ :=
  (2 * a + 2) + (2 * q + 2) + (2 * L + 2) +
    MatrixAddressMachine.exactTime s L 0 + 3

/-! ## Component runs -/

private theorem save_stage (T : Base → List Bool) (a q L s : ℕ)
    (h54 : T (WeightedColumnActualStage.writerSlots 54) = List.replicate a true)
    (h56 : T (WeightedColumnActualStage.writerSlots 56) = List.replicate q true)
    (h57 : T (WeightedColumnActualStage.writerSlots 57) = List.replicate L true)
    (h28 : T (WeightedColumnActualStage.writerSlots 28) = List.replicate s true) :
    ∃ t ≤ saveCost a q L s,
      ((advance saveProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          saveInitial, Sum.elim T (fun _ => [])⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, saveInitial, Sum.elim T (savedWords a q L (s * L))⟩ := by
  let S0 : Stack → List Bool := Sum.elim T (fun _ => [])
  let S1 : Stack → List Bool := Sum.elim T
    ![List.replicate a true, [], [], [], [], [], []]
  let S2 : Stack → List Bool := Sum.elim T
    ![List.replicate a true, List.replicate q true, [], [], [], [], []]
  let S3 : Stack → List Bool := Sum.elim T
    ![List.replicate a true, List.replicate q true, List.replicate L true,
      [], [], [], []]
  let S4 : Stack → List Bool := Sum.elim T (savedWords a q L (s * L))
  have c0 := copy_run copyA S0 rfl
  have c1 := copy_run copyQ S1 rfl
  have c2 := copy_run copyL S2 rfl
  have e0 : S0 (copyA 0) = List.replicate a true := h54
  have e1 : S1 (copyQ 0) = List.replicate q true := h56
  have e2 : S2 (copyL 0) = List.replicate L true := h57
  rw [e0, List.length_replicate] at c0
  rw [e1, List.length_replicate] at c1
  rw [e2, List.length_replicate] at c2
  have u0 : Function.update S0 (copyA 1) (List.replicate a true ++ S0 (copyA 1)) =
      S1 := by
    funext x
    rcases x with x | j
    · rfl
    · fin_cases j <;> first
        | rfl
        | simp [S0, S1, copyA, copySlots, save]
  have u1 : Function.update S1 (copyQ 1) (List.replicate q true ++ S1 (copyQ 1)) =
      S2 := by
    funext x
    rcases x with x | j
    · rfl
    · fin_cases j <;> first
        | rfl
        | simp [S1, S2, copyQ, copySlots, save]
  have u2 : Function.update S2 (copyL 1) (List.replicate L true ++ S2 (copyL 1)) =
      S3 := by
    funext x
    rcases x with x | j
    · rfl
    · fin_cases j <;> first
        | rfl
        | simp [S2, S3, copyL, copySlots, save]
  rw [u0] at c0
  rw [u1] at c1
  rw [u2] at c2
  have m := multiply_run mulSlots S3 s L h28 rfl rfl rfl rfl
  have u3 : Function.update S3 (mulSlots 5)
      (List.replicate (s * L) true ++ S3 (mulSlots 5)) = S4 := by
    funext x
    rcases x with x | j
    · rfl
    · fin_cases j <;> first
        | rfl
        | simp [S3, S4, mulSlots, save, savedWords]
  rw [u3] at m
  obtain ⟨t3, ht3, r3⟩ := BitMachineRawSequence.runs
    (copyProgram copyL) (multiplyProgram mulSlots)
    BitMachineCopy.Label.scan MatrixAddressMachine.Label.outer
    (none : CopyControl) (none : CopyControl) false false
    S2 S3 S4 (2 * L + 2) (MatrixAddressMachine.exactTime s L 0) c2 m
  obtain ⟨t2, ht2, r2⟩ := BitMachineRawSequence.runs
    (copyProgram copyQ) saveL
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none : CopyControl) (none : CopyControl)
    ((none : CopyControl), false) ((none : CopyControl), false)
    S1 S2 S4 (2 * q + 2) t3 c1 r3
  obtain ⟨t1, ht1, r1⟩ := BitMachineRawSequence.runs
    (copyProgram copyA) saveQ
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none : CopyControl) (none : CopyControl)
    ((none : CopyControl), ((none : CopyControl), false))
    ((none : CopyControl), ((none : CopyControl), false))
    S0 S1 S4 (2 * a + 2) t2 c0 r2
  refine ⟨t1, ?_, r1⟩
  unfold saveCost
  omega

private theorem column_stage (T : Base → List Bool) (a s q L rx cy : ℕ)
    (saved : Fin 7 → List Bool)
    (h28 : T (WeightedColumnActualStage.writerSlots 28) = List.replicate s true)
    (h17 : T (WeightedColumnActualStage.writerSlots 17) = List.replicate rx true)
    (h27 : T (WeightedColumnActualStage.writerSlots 27) = List.replicate cy true)
    (h54 : T (WeightedColumnActualStage.writerSlots 54) = List.replicate a true)
    (h56 : T (WeightedColumnActualStage.writerSlots 56) = List.replicate q true)
    (h57 : T (WeightedColumnActualStage.writerSlots 57) = List.replicate L true) :
    ∃ t ≤ WeightedColumnActualStage.stageBound
        (fun k => T (WeightedColumnActualStage.writerSlots k)) a s q L rx cy,
      ((advance columnProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (WeightedColumnActualStage.ClearLabel.clear 0)),
          WeightedColumnActualStage.initial, Sum.elim T saved⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, WeightedColumnActualStage.initial,
          Sum.elim (WeightedColumnActualStage.exitBank T a s q L rx cy) saved⟩ := by
  obtain ⟨t, ht, hr⟩ := WeightedColumnActualStage.lifted_run T a s q L rx cy
    h28 h17 h27 h54 h56 h57
  refine ⟨t, ht, ?_⟩
  have he := BitMachineStackRun.run baseSlots (Sum.elim T saved)
    WeightedColumnActualStage.liftedProgram
    ⟨some (BitMachineRawSequence.leftLabel
        (WeightedColumnActualStage.ClearLabel.clear 0)),
      WeightedColumnActualStage.initial, T⟩ t
  rw [hr] at he
  have hi : bank baseSlots (Sum.elim T saved) T = Sum.elim T saved :=
    bank_eq_self baseSlots _ _ (fun _ => rfl)
  have ho : bank baseSlots (Sum.elim T saved)
      (WeightedColumnActualStage.exitBank T a s q L rx cy) =
      Sum.elim (WeightedColumnActualStage.exitBank T a s q L rx cy) saved := by
    funext x
    rcases x with x | j
    · exact bank_at baseSlots _ _ x
    · rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩; cases hk
  simpa only [columnProgram, stackCfg, hi, ho] using he

/-- Composition from any halted run of the frozen scalar controller: the
retention copies, the multiplication and the lifted column stage follow on
the same stacks, with all handoffs charged. -/
theorem composite_run (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (T : Base → List Bool) (u a s q L rx cy : ℕ)
    (hrun' : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩)
    (hT28 : T (WeightedColumnActualStage.writerSlots 28) = List.replicate s true)
    (hT17 : T (WeightedColumnActualStage.writerSlots 17) = List.replicate rx true)
    (hT27 : T (WeightedColumnActualStage.writerSlots 27) = List.replicate cy true)
    (hT54 : T (WeightedColumnActualStage.writerSlots 54) = List.replicate a true)
    (hT56 : T (WeightedColumnActualStage.writerSlots 56) = List.replicate q true)
    (hT57 : T (WeightedColumnActualStage.writerSlots 57) = List.replicate L true) :
    ∃ w ≤ u + saveCost a q L s +
        WeightedColumnActualStage.stageBound
          (fun k => T (WeightedColumnActualStage.writerSlots k)) a s q L rx cy + 2,
      ((advance program)^[w])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          initialControl, initialBank i g W⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, initialControl, exitBank T a s q L rx cy⟩ := by
  -- lift the frozen scalar run to the extended stack
  have hscalar : ((advance scalarProgram)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl, initialBank i g W⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl,
        Sum.elim T (fun _ => [])⟩ := by
    have he := BitMachineStackRun.run baseSlots (initialBank i g W)
      WeightedScalarFromRawDimensions.program
      ⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ u
    rw [hrun'] at he
    have hi : bank baseSlots (initialBank i g W)
        (WeightedScalarFromRawDimensions.initialBank i g W) =
        initialBank i g W :=
      bank_eq_self baseSlots _ _ (fun _ => rfl)
    have ho : bank baseSlots (initialBank i g W) T =
        Sum.elim T (fun _ => []) := by
      funext x
      rcases x with x | j
      · exact bank_at baseSlots _ _ x
      · rw [bank_outside]
        · rfl
        · rintro ⟨k, hk⟩; cases hk
    simpa only [scalarProgram, stackCfg, hi, ho] using he
  obtain ⟨us, hus, hsave⟩ := save_stage T a q L s hT54 hT56 hT57 hT28
  obtain ⟨uc, huc, hcol⟩ := column_stage T a s q L rx cy
    (savedWords a q L (s * L)) hT28 hT17 hT27 hT54 hT56 hT57
  obtain ⟨ut, hut, htail⟩ := BitMachineRawSequence.runs
    saveProgram columnProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (WeightedColumnActualStage.ClearLabel.clear 0))
    saveInitial saveInitial
    WeightedColumnActualStage.initial WeightedColumnActualStage.initial
    (Sum.elim T (fun _ => [])) (Sum.elim T (savedWords a q L (s * L)))
    (Sum.elim (WeightedColumnActualStage.exitBank T a s q L rx cy)
      (savedWords a q L (s * L)))
    us uc hsave hcol
  obtain ⟨w, hw, hfull⟩ := BitMachineRawSequence.runs
    scalarProgram tailProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    WeightedScalarFromRawDimensions.initialControl
    WeightedScalarFromRawDimensions.initialControl
    tailInitial tailInitial
    (initialBank i g W) (Sum.elim T (fun _ => []))
    (Sum.elim (WeightedColumnActualStage.exitBank T a s q L rx cy)
      (savedWords a q L (s * L)))
    u ut hscalar (by simpa only [tailProgram, tailInitial] using htail)
  refine ⟨w, by omega, ?_⟩
  simpa only [program, initialControl, exitBank] using hfull

/-! ## The segment theorem -/

/-- One fixed controller: frozen raw-dimension scalar controller, charged
retention copies of `a`, `q`, `L`, a charged multiplication producing `s*L`,
then the frozen lifted column stage. Hypotheses are exactly the 22 blank
writer cells of the frozen `WeightedRawDimensionsFrame.source_run_framed`. -/
theorem save_column_run {V E : Type*} [Fintype V] [DecidableEq V]
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
      ∃ u ≤ WeightedScalarFromRawDimensions.bound i g (Fintype.card E) q +
          saveCost a q L s +
          WeightedColumnActualStage.stageBound
            (fun k => T (WeightedColumnActualStage.writerSlots k))
            a s q L i.rows i.columns + 2,
        ((advance program)^[u])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            initialControl, initialBank i g W⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, initialControl, exitBank T a s q L i.rows i.columns⟩ ∧
        exitBank T a s q L i.rows i.columns (wcell 26) =
          List.replicate (MatrixStage4Digits.wordBase a s i.columns) true ∧
        exitBank T a s q L i.rows i.columns (wcell 29) =
          List.replicate (MatrixStage4Digits.binBase a s q i.columns) true ∧
        exitBank T a s q L i.rows i.columns (wcell 21) =
          List.replicate (MatrixStage4Codes.cols a s q i.columns) true ∧
        exitBank T a s q L i.rows i.columns (wcell 28) =
          List.replicate s true ∧
        exitBank T a s q L i.rows i.columns (wcell 17) =
          List.replicate i.rows true ∧
        exitBank T a s q L i.rows i.columns (wcell 27) =
          List.replicate i.columns true ∧
        exitBank T a s q L i.rows i.columns (save 0) = List.replicate a true ∧
        exitBank T a s q L i.rows i.columns (save 1) = List.replicate q true ∧
        exitBank T a s q L i.rows i.columns (save 2) = List.replicate L true ∧
        exitBank T a s q L i.rows i.columns (save 3) =
          List.replicate (s * L) true ∧
        exitBank T a s q L i.rows i.columns (save 4) = [] ∧
        exitBank T a s q L i.rows i.columns (save 5) = [] ∧
        exitBank T a s q L i.rows i.columns (save 6) = [] ∧
        (∀ k : Fin 64, (∀ j : Fin 40, ColumnWriterJoin.slots j ≠ k) →
          (∀ j : Fin 40, WeightedColumnActualStage.clearCells j ≠ k) →
          exitBank T a s q L i.rows i.columns (wcell k) =
            T (WeightedColumnActualStage.writerSlots k)) ∧
        (∀ x : Base, (∀ k : Fin 64, WeightedColumnActualStage.writerSlots k ≠ x) →
          exitBank T a s q L i.rows i.columns (.inl x) = T x) := by
  intro g s q a L W''
  obtain ⟨u, hu, -, F, Q, P, hrun, hr17, hr27, hr28, hr54, hr56, hr57⟩ :=
    WeightedRawDimensionsFrame.source_run_framed i G W h17 h62 h27 h63 h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T
  have hT28 : T (WeightedColumnActualStage.writerSlots 28) =
      List.replicate s true := hr28
  have hT17 : T (WeightedColumnActualStage.writerSlots 17) =
      List.replicate i.rows true := hr17
  have hT27 : T (WeightedColumnActualStage.writerSlots 27) =
      List.replicate i.columns true := hr27
  have hT54 : T (WeightedColumnActualStage.writerSlots 54) =
      List.replicate a true := hr54
  have hT56 : T (WeightedColumnActualStage.writerSlots 56) =
      List.replicate q true := hr56
  have hT57 : T (WeightedColumnActualStage.writerSlots 57) =
      List.replicate L true := hr57
  have hrun' : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩ := hrun
  have hu' : u ≤ WeightedScalarFromRawDimensions.bound i g
      (Fintype.card E) q := hu
  obtain ⟨w, hw, hfull⟩ := composite_run i g W T u a s q L i.rows i.columns
    hrun' hT28 hT17 hT27 hT54 hT56 hT57
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
  refine ⟨w, ?_, hfull, o26, o29, o21, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_⟩
  · omega
  · exact (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      28 h28s h28c).trans hT28
  · exact (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      17 h17s h17c).trans hT17
  · exact (WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns
      27 h27s h27c).trans hT27
  · exact fun k hs hc =>
      WeightedColumnActualStage.exit_preserved T a s q L i.rows i.columns k hs hc
  · exact fun x hx =>
      WeightedColumnActualStage.exit_foreign T a s q L i.rows i.columns x hx

#print axioms composite_run
#print axioms save_column_run

end
end EthInapproximability.CurrentPaper.WeightedLevelColumnSave
