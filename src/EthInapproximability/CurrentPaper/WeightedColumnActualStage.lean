import EthInapproximability.CurrentPaper.WeightedColumnGenericStage
import EthInapproximability.CurrentPaper.WeightedRawDimensionsFrame
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! The Stage--4 column stage on the actual writer bank reached by the frozen
raw-dimension scalar controller.

One fixed Fin64 controller first pops, cell by cell, every column-writer slot
except the live inputs 54/56/57, together with the copy scratch 61/62/63.
Its time is the actual number of discarded Boolean cells plus the empty tests
and control exits. The cleared bank is then literally the generic three-copy
input bank (`WeightedColumnGenericStage.partialBank`) of itself; no synthetic
`ColumnInputStaging.partialBank` or semantic metadata bank is used. The three
physical copies 28->55, 17->58, 27->59 and the frozen `ColumnWriterJoin`
producer/cleanup follow. The Fin64 controller is lifted to the weighted scalar
stack with `BitMachineStackRun.run` and sequenced after the frozen
`WeightedRawDimensionsFrame.source_run_framed` witness. -/

namespace EthInapproximability.CurrentPaper.WeightedColumnActualStage

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

/-- The 37 column-writer slots other than the live inputs 54/56/57, then the
copy scratch 61/62/63. -/
def clearCells : Fin 40 ↪ Fin 64 :=
  ⟨![55,58,59,0,2,26,29,5,7,21,
      8,9,10,11,12,13,14,19,20,23,24,25,30,31,32,33,34,
      35,36,37,38,39,40,41,42,43,44,61,62,63], by decide⟩

inductive ClearLabel where
  | clear (i : Fin 41)
  | done

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Fin 64 => Bool) ClearLabel (Unit × Option Bool)
  | .clear i => if h : i.val < 40 then
      BitMachineClearBank.clearStep (clearCells ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => ()) .done
  | .done => .halt

/-- Actual charged clearing time on the reached bank `S`. -/
def clearCost (S : Fin 64 → List Bool) : ℕ :=
  (∑ i : Fin 40, (S (clearCells i)).length) + 42

def clearedBank (S : Fin 64 → List Bool) : Fin 64 → List Bool :=
  BitMachineClearBank.cleared clearCells S

theorem clear_run (S : Fin 64 → List Bool) :
    ((advance clearProgram)^[clearCost S])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), clearedBank S⟩ := by
  have hs (i : Fin 40) : clearProgram (.clear i.castSucc) =
      BitMachineClearBank.clearStep (clearCells i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [clearProgram, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : clearProgram (.clear (Fin.last 40)) =
      BitMachineClearBank.finishStep (fun _ => ()) .done := by
    simp only [clearProgram, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run clearProgram
    (fun _ => ()) ClearLabel.done 40 clearCells clearCells.injective
    ClearLabel.clear hs hf () S
  have hd : advance clearProgram
      (⟨some .done, ((), none), BitMachineClearBank.cleared clearCells S⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells S⟩ := rfl
  rw [clearCost, show (∑ i : Fin 40, (S (clearCells i)).length) + 42 =
      1 + ((∑ i : Fin 40, (S (clearCells i)).length) + 40 + 1) by omega,
    Function.iterate_add_apply, hr]
  exact hd

theorem cleared_foreign (S : Fin 64 → List Bool) (k : Fin 64)
    (hk : ∀ i : Fin 40, clearCells i ≠ k) : clearedBank S k = S k :=
  BitMachineClearBank.cleared_foreign _ _ _ hk

set_option maxRecDepth 8192 in
theorem cleared_partial (S : Fin 64 → List Bool) (a q L : ℕ)
    (h54 : S 54 = List.replicate a true)
    (h56 : S 56 = List.replicate q true)
    (h57 : S 57 = List.replicate L true) :
    WeightedColumnGenericStage.partialBank (clearedBank S) a q L =
      clearedBank S := by
  unfold WeightedColumnGenericStage.partialBank
  apply bank_eq_self
  have hmem : ∀ k : Fin 40, k ≠ 0 → k ≠ 2 → k ≠ 3 →
      ∃ i : Fin 40, clearCells i = ColumnWriterJoin.slots k := by decide
  have h0 : ∀ i : Fin 40, clearCells i ≠ (54 : Fin 64) := by decide
  have h2 : ∀ i : Fin 40, clearCells i ≠ (56 : Fin 64) := by decide
  have h3 : ∀ i : Fin 40, clearCells i ≠ (57 : Fin 64) := by decide
  intro k
  by_cases k0 : k = 0
  · subst k0
    rw [show ColumnWriterJoin.slots 0 = (54 : Fin 64) from rfl,
      cleared_foreign S 54 h0, h54]
    simp [ColumnInputStaging.partialLocalBank]
  by_cases k2 : k = 2
  · subst k2
    rw [show ColumnWriterJoin.slots 2 = (56 : Fin 64) from rfl,
      cleared_foreign S 56 h2, h56]
    simp [ColumnInputStaging.partialLocalBank]
  by_cases k3 : k = 3
  · subst k3
    rw [show ColumnWriterJoin.slots 3 = (57 : Fin 64) from rfl,
      cleared_foreign S 57 h3, h57]
    simp [ColumnInputStaging.partialLocalBank]
  obtain ⟨i, hi⟩ := hmem k k0 k2 k3
  rw [← hi, clearedBank, BitMachineClearBank.cleared_bank]
  simp [ColumnInputStaging.partialLocalBank, k0, k2, k3]

/-- Clear, three physical copies, frozen column producer and cleanup. -/
def program := BitMachineRawSequence.program clearProgram
  ColumnInputStaging.program ColumnInputStaging.start
  (((), none) : Unit × Option Bool) ColumnInputStaging.initial

def initial := ((((), none) : Unit × Option Bool), ColumnInputStaging.initial)

def stageBound (S : Fin 64 → List Bool) (a s q L rx cy : ℕ) : ℕ :=
  clearCost S + ColumnInputStaging.stageCost s rx cy +
    ColumnWriterJoin.joinCost a s q L rx cy + 2

theorem writer_run (S : Fin 64 → List Bool) (a s q L rx cy : ℕ)
    (h28 : S 28 = List.replicate s true)
    (h17 : S 17 = List.replicate rx true)
    (h27 : S 27 = List.replicate cy true)
    (h54 : S 54 = List.replicate a true)
    (h56 : S 56 = List.replicate q true)
    (h57 : S 57 = List.replicate L true) :
    ∃ t ≤ stageBound S a s q L rx cy,
      ((advance program)^[t])
        ⟨some (BitMachineRawSequence.leftLabel (ClearLabel.clear 0)),
          initial, S⟩ =
      ⟨none, initial,
        ColumnWriterJoin.readyBank (clearedBank S) a s q L rx cy⟩ := by
  have hC28 : clearedBank S 28 = List.replicate s true :=
    (cleared_foreign S 28 (by decide)).trans h28
  have hC17 : clearedBank S 17 = List.replicate rx true :=
    (cleared_foreign S 17 (by decide)).trans h17
  have hC27 : clearedBank S 27 = List.replicate cy true :=
    (cleared_foreign S 27 (by decide)).trans h27
  have hC61 : clearedBank S 61 = [] :=
    BitMachineClearBank.cleared_bank clearCells S 37
  have hC62 : clearedBank S 62 = [] :=
    BitMachineClearBank.cleared_bank clearCells S 38
  have hC63 : clearedBank S 63 = [] :=
    BitMachineClearBank.cleared_bank clearCells S 39
  obtain ⟨u, hu, hstage⟩ := WeightedColumnGenericStage.three_run
    (clearedBank S) a s q L rx cy hC28 hC17 hC27 hC61 hC62 hC63
  rw [cleared_partial S a q L h54 h56 h57] at hstage
  obtain ⟨v, hv, hjoin⟩ := ColumnWriterJoin.embedded_run
    (clearedBank S) a s q L rx cy
  rw [ColumnWriterJoin.clearCost_produced] at hv
  obtain ⟨w, hw, hcol⟩ := ColumnInputStaging.Raw.runs
    ColumnInputStaging.P123 ColumnWriterJoin.program
    (ColumnInputStaging.Raw.leftLabel
      (ColumnInputStaging.Raw.leftLabel BitMachineCopy.Label.scan))
    ColumnWriterJoin.start
    ((none,none),none) ((none,none),none)
    ColumnWriterJoin.initial ColumnWriterJoin.initial
    (clearedBank S)
    (ColumnWriterJoin.sourceBank (clearedBank S) a s q L rx cy)
    (ColumnWriterJoin.readyBank (clearedBank S) a s q L rx cy)
    u v (by simpa only [ColumnInputStaging.P123] using hstage)
    (by simpa only [ColumnWriterJoin.run, ColumnWriterJoin.cfg] using hjoin)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    clearProgram ColumnInputStaging.program
    (ClearLabel.clear 0) ColumnInputStaging.start
    (((), none) : Unit × Option Bool) (((), none) : Unit × Option Bool)
    ColumnInputStaging.initial ColumnInputStaging.initial
    S (clearedBank S)
    (ColumnWriterJoin.readyBank (clearedBank S) a s q L rx cy)
    (clearCost S) w (clear_run S)
    (by simpa only [ColumnInputStaging.program, ColumnInputStaging.start,
      ColumnInputStaging.initial] using hcol)
  refine ⟨t, ?_, ?_⟩
  · unfold stageBound ColumnWriterJoin.joinCost
    omega
  · simpa only [program, initial] using hr

/-- The weighted writer inside the actual scalar-controller stack. -/
def writerSlots : Fin 64 ↪ WeightedScalarFromRawDimensions.Stack :=
  ⟨WeightedScalarComplete.writer, by
    intro a b h
    simpa [WeightedScalarComplete.writer, WeightedActualSizeSuffix.writer,
      WeightedMTPrefix.writer, WeightedPrefixAT.writer,
      WeightedScaleDerivedFromBins.writer, WeightedBinsGraphQ.writer,
      WeightedGraphQJoined.writer] using h⟩

def liftedProgram := fun l => stackStmt writerSlots (program l)

/-- Explicit exit bank: every non-writer cell and every writer cell outside
the column slots and the clear list keep the reached value from `T`. -/
def exitBank (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) : WeightedScalarFromRawDimensions.Stack → List Bool :=
  bank writerSlots T
    (ColumnWriterJoin.readyBank (clearedBank (fun k => T (writerSlots k)))
      a s q L rx cy)

theorem lifted_run (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ)
    (h28 : T (writerSlots 28) = List.replicate s true)
    (h17 : T (writerSlots 17) = List.replicate rx true)
    (h27 : T (writerSlots 27) = List.replicate cy true)
    (h54 : T (writerSlots 54) = List.replicate a true)
    (h56 : T (writerSlots 56) = List.replicate q true)
    (h57 : T (writerSlots 57) = List.replicate L true) :
    ∃ t ≤ stageBound (fun k => T (writerSlots k)) a s q L rx cy,
      ((advance liftedProgram)^[t])
        ⟨some (BitMachineRawSequence.leftLabel (ClearLabel.clear 0)),
          initial, T⟩ =
      ⟨none, initial, exitBank T a s q L rx cy⟩ := by
  obtain ⟨t, ht, hr⟩ := writer_run (fun k => T (writerSlots k))
    a s q L rx cy h28 h17 h27 h54 h56 h57
  refine ⟨t, ht, ?_⟩
  have he := BitMachineStackRun.run writerSlots T program
    ⟨some (BitMachineRawSequence.leftLabel (ClearLabel.clear 0)),
      initial, fun k => T (writerSlots k)⟩ t
  rw [hr] at he
  simpa only [stackCfg, bank_restrict, liftedProgram, exitBank] using he

/-- Full fixed controller: frozen raw-dimension scalar controller, one handoff,
then the lifted column stage. -/
def fullProgram := BitMachineRawSequence.program
  WeightedScalarFromRawDimensions.program liftedProgram
  (BitMachineRawSequence.leftLabel (ClearLabel.clear 0))
  WeightedScalarFromRawDimensions.initialControl initial

def fullInitial := (WeightedScalarFromRawDimensions.initialControl, initial)

theorem exit_writer_slot (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) (k : Fin 64) :
    exitBank T a s q L rx cy (writerSlots k) =
      ColumnWriterJoin.readyBank (clearedBank (fun k => T (writerSlots k)))
        a s q L rx cy k :=
  bank_at writerSlots T _ k

theorem exit_foreign (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) (x : WeightedScalarFromRawDimensions.Stack)
    (hx : ∀ k : Fin 64, writerSlots k ≠ x) :
    exitBank T a s q L rx cy x = T x :=
  bank_outside writerSlots T _ x (by rintro ⟨k, hk⟩; exact hx k hk)

theorem exit_outputs (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) :
    exitBank T a s q L rx cy (writerSlots 26) =
      List.replicate (MatrixStage4Digits.wordBase a s cy) true ∧
    exitBank T a s q L rx cy (writerSlots 29) =
      List.replicate (MatrixStage4Digits.binBase a s q cy) true ∧
    exitBank T a s q L rx cy (writerSlots 21) =
      List.replicate (MatrixStage4Codes.cols a s q cy) true := by
  simp only [exit_writer_slot]
  exact ColumnWriterJoin.ready_outputs _ a s q L rx cy

theorem exit_preserved (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) (k : Fin 64)
    (hs : ∀ i : Fin 40, ColumnWriterJoin.slots i ≠ k)
    (hc : ∀ i : Fin 40, clearCells i ≠ k) :
    exitBank T a s q L rx cy (writerSlots k) = T (writerSlots k) := by
  rw [exit_writer_slot, ColumnWriterJoin.ready_frame _ a s q L rx cy k hs,
    cleared_foreign _ k hc]

theorem exit_blank (T : WeightedScalarFromRawDimensions.Stack → List Bool)
    (a s q L rx cy : ℕ) :
    (∀ j : Fin 10, exitBank T a s q L rx cy
      (writerSlots (ColumnWriterJoin.cleanupSlots j)) = []) ∧
    (∀ j : Fin 40, 13 ≤ j.val → exitBank T a s q L rx cy
      (writerSlots (ColumnWriterJoin.slots j)) = []) ∧
    exitBank T a s q L rx cy (writerSlots 61) = [] ∧
    exitBank T a s q L rx cy (writerSlots 62) = [] ∧
    exitBank T a s q L rx cy (writerSlots 63) = [] := by
  have h61 : ∀ i : Fin 40, ColumnWriterJoin.slots i ≠ (61 : Fin 64) := by decide
  have h62 : ∀ i : Fin 40, ColumnWriterJoin.slots i ≠ (62 : Fin 64) := by decide
  have h63 : ∀ i : Fin 40, ColumnWriterJoin.slots i ≠ (63 : Fin 64) := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [exit_writer_slot]
    exact ColumnWriterJoin.ready_cleanup _ a s q L rx cy j
  · intro j hj
    rw [exit_writer_slot]
    exact ColumnWriterJoin.ready_local_scratch _ a s q L rx cy j hj
  · rw [exit_writer_slot, ColumnWriterJoin.ready_frame _ a s q L rx cy 61 h61]
    exact BitMachineClearBank.cleared_bank clearCells _ 37
  · rw [exit_writer_slot, ColumnWriterJoin.ready_frame _ a s q L rx cy 62 h62]
    exact BitMachineClearBank.cleared_bank clearCells _ 38
  · rw [exit_writer_slot, ColumnWriterJoin.ready_frame _ a s q L rx cy 63 h63]
    exact BitMachineClearBank.cleared_bank clearCells _ 39

/-- The column stage on the actual reached writer bank, sequenced after the
same frozen raw-dimension scalar controller. The time bound charges the frozen
scalar bound, the actual clearing of the reached bank, the three copies, the
frozen column producer and cleanup, and all handoffs. -/
theorem column_stage_run {V E : Type*} [Fintype V] [DecidableEq V]
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
          stageBound (fun k => T (writerSlots k)) a s q L i.rows i.columns + 1,
        ((advance fullProgram)^[u])
          ⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            fullInitial, WeightedScalarFromRawDimensions.initialBank i g W⟩ =
          ⟨none, fullInitial, exitBank T a s q L i.rows i.columns⟩ ∧
        exitBank T a s q L i.rows i.columns (writerSlots 26) =
          List.replicate (MatrixStage4Digits.wordBase a s i.columns) true ∧
        exitBank T a s q L i.rows i.columns (writerSlots 29) =
          List.replicate (MatrixStage4Digits.binBase a s q i.columns) true ∧
        exitBank T a s q L i.rows i.columns (writerSlots 21) =
          List.replicate (MatrixStage4Codes.cols a s q i.columns) true ∧
        exitBank T a s q L i.rows i.columns (writerSlots 28) =
          List.replicate s true ∧
        exitBank T a s q L i.rows i.columns (writerSlots 17) =
          List.replicate i.rows true ∧
        exitBank T a s q L i.rows i.columns (writerSlots 27) =
          List.replicate i.columns true ∧
        (∀ k : Fin 64, (∀ j : Fin 40, ColumnWriterJoin.slots j ≠ k) →
          (∀ j : Fin 40, clearCells j ≠ k) →
          exitBank T a s q L i.rows i.columns (writerSlots k) =
            T (writerSlots k)) ∧
        (∀ x : WeightedScalarFromRawDimensions.Stack,
          (∀ k : Fin 64, writerSlots k ≠ x) →
          exitBank T a s q L i.rows i.columns x = T x) := by
  intro g s q a L W''
  obtain ⟨u, hu, -, F, Q, P, hrun, hr17, hr27, hr28, hr54, hr56, hr57⟩ :=
    WeightedRawDimensionsFrame.source_run_framed i G W h17 h62 h27 h63 h28 h61
      h7 h8 h9 h10 h11 h12 h13 h14 h15 h18 h54 h55 h56 h57 h58 h60
  refine ⟨F, Q, P, ?_⟩
  intro T
  have hT28 : T (writerSlots 28) = List.replicate s true := hr28
  have hT17 : T (writerSlots 17) = List.replicate i.rows true := hr17
  have hT27 : T (writerSlots 27) = List.replicate i.columns true := hr27
  have hT54 : T (writerSlots 54) = List.replicate a true := hr54
  have hT56 : T (writerSlots 56) = List.replicate q true := hr56
  have hT57 : T (writerSlots 57) = List.replicate L true := hr57
  have hrun' : ((advance WeightedScalarFromRawDimensions.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        WeightedScalarFromRawDimensions.initialControl,
        WeightedScalarFromRawDimensions.initialBank i g W⟩ :
        TM2.Cfg (fun _ : WeightedScalarFromRawDimensions.Stack => Bool) _ _) =
      ⟨none, WeightedScalarFromRawDimensions.initialControl, T⟩ := hrun
  have hu' : u ≤ WeightedScalarFromRawDimensions.bound i g
      (Fintype.card E) q := hu
  obtain ⟨t, ht, hcol⟩ := lifted_run T a s q L i.rows i.columns
    hT28 hT17 hT27 hT54 hT56 hT57
  obtain ⟨w, hw, hfull⟩ := BitMachineRawSequence.runs
    WeightedScalarFromRawDimensions.program liftedProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel (ClearLabel.clear 0))
    WeightedScalarFromRawDimensions.initialControl
    WeightedScalarFromRawDimensions.initialControl
    initial initial
    (WeightedScalarFromRawDimensions.initialBank i g W) T
    (exitBank T a s q L i.rows i.columns)
    u t hrun' hcol
  have h28s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (28 : Fin 64) := by decide
  have h17s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (17 : Fin 64) := by decide
  have h27s : ∀ j : Fin 40, ColumnWriterJoin.slots j ≠ (27 : Fin 64) := by decide
  have h28c : ∀ j : Fin 40, clearCells j ≠ (28 : Fin 64) := by decide
  have h17c : ∀ j : Fin 40, clearCells j ≠ (17 : Fin 64) := by decide
  have h27c : ∀ j : Fin 40, clearCells j ≠ (27 : Fin 64) := by decide
  obtain ⟨o26, o29, o21⟩ := exit_outputs T a s q L i.rows i.columns
  refine ⟨w, ?_, ?_, o26, o29, o21, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · simpa only [fullProgram, fullInitial] using hfull
  · exact (exit_preserved T a s q L i.rows i.columns 28 h28s h28c).trans hT28
  · exact (exit_preserved T a s q L i.rows i.columns 17 h17s h17c).trans hT17
  · exact (exit_preserved T a s q L i.rows i.columns 27 h27s h27c).trans hT27
  · exact fun k hs hc => exit_preserved T a s q L i.rows i.columns k hs hc
  · exact fun x hx => exit_foreign T a s q L i.rows i.columns x hx

#print axioms WeightedColumnGenericStage.partial_live
#print axioms WeightedColumnGenericStage.partial_blank
#print axioms WeightedColumnGenericStage.s_run
#print axioms WeightedColumnGenericStage.rx_run
#print axioms WeightedColumnGenericStage.cy_run
#print axioms WeightedColumnGenericStage.after_three_eq_full
#print axioms WeightedColumnGenericStage.three_run
#print axioms clear_run
#print axioms cleared_foreign
#print axioms cleared_partial
#print axioms writer_run
#print axioms lifted_run
#print axioms exit_writer_slot
#print axioms exit_foreign
#print axioms exit_outputs
#print axioms exit_preserved
#print axioms exit_blank
#print axioms column_stage_run

end
end EthInapproximability.CurrentPaper.WeightedColumnActualStage
