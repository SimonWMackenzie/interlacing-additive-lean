import EthInapproximability.CurrentPaper.ColumnScalarOutput
import EthInapproximability.CurrentPaper.MatrixWeightedEntrySemantic
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Data.Fin.VecNotation

/-! A literal fixed embedding of the checked Fin40 column-scalar machine
into the weighted writer's Fin64 global bank. -/

namespace EthInapproximability.CurrentPaper.ColumnWriterJoin

open Turing BitMachineEncoding BitMachineStackEmbedding
open ColumnScalarPrefix

abbrev Stack := Fin 64

/-- Input words occupy 54--59; live outputs go straight to writer 26,29,21.
All other images are disposable scratch, avoiding every other persistent
weighted-writer cell. -/
def slots : Fin 40 ↪ Stack :=
  ⟨![54,55,56,57,58,59,0,2,26,29,5,7,21,
      8,9,10,11,12,13,14,19,20,23,24,25,30,31,32,33,34,
      35,36,37,38,39,40,41,42,43,44], by decide⟩

/-- The six staged inputs and four non-output intermediates. -/
def cleanupSlots : Fin 10 ↪ Stack :=
  ⟨![54,55,56,57,58,59,0,2,5,7], by decide⟩

def cleanupLocal : Fin 10 → Fin 40 :=
  ![0,1,2,3,4,5,6,7,10,11]

theorem cleanupSlots_eq (i : Fin 10) :
    cleanupSlots i = slots (cleanupLocal i) := by
  fin_cases i <;> rfl

inductive Label where
  | scalar (l : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label MatrixUnaryPower.Label
                  ColumnScalarPrefix.PopLabel)
                (BitMachineRawSequence.Label
                  (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
                  ColumnScalarPrefix.PushLabel))
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
                MatrixWeightedPower.Label))
            MatrixAddressMachine.Label)
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label BitMachineCopy.Label ColumnScalarTailPower.Admin)
            MatrixWeightedPower.Label))
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label BitMachineCopy.Label ColumnScalarBinPower.SeedLabel)
          MatrixWeightedPower.Label))
      MatrixAddressMachine.Label)
  | clear (i : Fin 11)
  | done

abbrev ScalarControl :=
  ((((((MatrixUnaryPower.Control × Unit) ×
    ((Option Bool × Option Bool) × Unit)) ×
    ((Option Bool × Unit) × MatrixWeightedPower.Control)) × Bool) ×
    ((Option Bool × Unit) × MatrixWeightedPower.Control)) ×
    ((Option Bool × Unit) × MatrixWeightedPower.Control)) × Bool
abbrev Control := ScalarControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scalar l => stmt slots Label.scalar (fun v => (v, none)) Prod.fst
      (some (.clear 0)) (ColumnScalarJoin.program l)
  | .clear i => if h : i.val < 10 then
      BitMachineClearBank.clearStep (cleanupSlots ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => ColumnScalarJoin.control) .done
  | .done => .halt

def start : Label := .scalar ColumnScalarJoin.start
def initial : Control := (ColumnScalarJoin.control, none)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l, v, S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

/-- All three target words are blank before the producer runs. Other
pre-existing writer cells may contain their own semantic data. -/
noncomputable def sourceBank (base : Stack → List Bool)
    (a s q L rx cy : ℕ) : Stack → List Bool :=
  bank slots base (inputBank a s q L rx cy)

noncomputable def producedBank (base : Stack → List Bool)
    (a s q L rx cy : ℕ) : Stack → List Bool :=
  bank slots base (ColumnScalarOutput.finalBank a s q L rx cy)

noncomputable def readyBank (base : Stack → List Bool)
    (a s q L rx cy : ℕ) : Stack → List Bool :=
  BitMachineClearBank.cleared cleanupSlots
    (producedBank base a s q L rx cy)

def clearCost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin 10, (S (cleanupSlots i)).length) + 12

theorem clearCost_produced (base : Stack → List Bool)
    (a s q L rx cy : ℕ) :
    clearCost (producedBank base a s q L rx cy) =
      a+s+q+L+rx+cy + Construction.qOne a +
      Construction.firstLength a s + cy^(s+1) +
      (MatrixStage4Digits.binBase a s q cy)^s + 12 := by
  unfold clearCost producedBank
  simp_rw [cleanupSlots_eq, bank_at]
  simp [Fin.sum_univ_succ, cleanupLocal,
    ColumnScalarOutput.finalBank, ColumnScalarWidth.outputBank,
    ColumnScalarWidth.sourceBank, ColumnScalarBinPower.outputBank,
    ColumnScalarBinPower.sourceBank, ColumnScalarTailPower.outputBank,
    ColumnScalarTailPower.sourceBank, ColumnScalarBinBase.outputBank,
    ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
    ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
    ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]
  omega

/-- Exact explicit unary-length budget for the embedded producer, physical
cleanup, and the exit transition from the scalar phase. -/
def joinCost (a s q L rx cy : ℕ) : ℕ :=
  ColumnScalarOutput.polynomialCost a s q cy +
    a+s+q+L+rx+cy + Construction.qOne a +
    Construction.firstLength a s + cy^(s+1) +
    (MatrixStage4Digits.binBase a s q cy)^s + 12

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem clear_run (S : Stack → List Bool) :
    run (clearCost S) (cfg (some (.clear 0)) initial S) =
      cfg none initial (BitMachineClearBank.cleared cleanupSlots S) := by
  have hs (i : Fin 10) : program (.clear i.castSucc) =
      BitMachineClearBank.clearStep (cleanupSlots i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [program, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : program (.clear (Fin.last 10)) =
      BitMachineClearBank.finishStep (fun _ => ColumnScalarJoin.control) .done := by
    simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ => ColumnScalarJoin.control) Label.done 10 cleanupSlots
    cleanupSlots.injective Label.clear hs hf ColumnScalarJoin.control S
  have hd : run 1
      (cfg (some .done) initial (BitMachineClearBank.cleared cleanupSlots S)) =
      cfg none initial (BitMachineClearBank.cleared cleanupSlots S) := rfl
  simpa only [clearCost, Nat.add_assoc] using (run_add hr 1).trans hd

theorem source_targets_empty (base : Stack → List Bool) (a s q L rx cy : ℕ) :
    sourceBank base a s q L rx cy 26 = [] ∧
    sourceBank base a s q L rx cy 29 = [] ∧
    sourceBank base a s q L rx cy 21 = [] := by
  simp [sourceBank, show (26 : Stack) = slots 8 from rfl,
    show (29 : Stack) = slots 9 from rfl,
    show (21 : Stack) = slots 12 from rfl,
    bank_at, inputBank]

theorem embedded_run (base : Stack → List Bool) (a s q L rx cy : ℕ) :
    ∃ t ≤ ColumnScalarOutput.polynomialCost a s q cy +
        clearCost (producedBank base a s q L rx cy),
      run t (cfg (some start) initial (sourceBank base a s q L rx cy)) =
        cfg none initial (readyBank base a s q L rx cy) := by
  obtain ⟨n, hn, hr⟩ := ColumnScalarOutput.physical_run_polynomial a s q L rx cy
  have hhalt :
      (((advance ColumnScalarJoin.program)^[n])
        ⟨some ColumnScalarJoin.start, ColumnScalarJoin.control,
          inputBank a s q L rx cy⟩).l = none := by rw [hr]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs slots base
    Label.scalar (fun v => (v, none)) Prod.fst (by intro v; rfl)
    (some (.clear 0)) ColumnScalarJoin.program program (by intro l; rfl)
    ⟨some ColumnScalarJoin.start, ColumnScalarJoin.control,
      inputBank a s q L rx cy⟩ n hhalt
  rw [hr] at he
  have hphase :
      run u (cfg (some start) initial (sourceBank base a s q L rx cy)) =
        cfg (some (.clear 0)) initial (producedBank base a s q L rx cy) := by
    simpa only [run, cfg, start, initial, sourceBank, producedBank,
      BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg] using he
  refine ⟨u + clearCost (producedBank base a s q L rx cy), ?_, ?_⟩
  · omega
  · exact (run_add hphase _).trans (clear_run _)

theorem ready_outputs (base : Stack → List Bool) (a s q L rx cy : ℕ) :
    readyBank base a s q L rx cy 26 =
      List.replicate (MatrixStage4Digits.wordBase a s cy) true ∧
    readyBank base a s q L rx cy 29 =
      List.replicate (MatrixStage4Digits.binBase a s q cy) true ∧
    readyBank base a s q L rx cy 21 =
      List.replicate (MatrixStage4Codes.cols a s q cy) true := by
  have h26 : ∀ i : Fin 10, cleanupSlots i ≠ (26 : Stack) := by decide
  have h29 : ∀ i : Fin 10, cleanupSlots i ≠ (29 : Stack) := by decide
  have h21 : ∀ i : Fin 10, cleanupSlots i ≠ (21 : Stack) := by decide
  have h := ColumnScalarOutput.exact_outputs a s q L rx cy
  constructor
  · rw [readyBank, BitMachineClearBank.cleared_foreign cleanupSlots _ _ h26]
    exact (bank_at slots base _ (8 : Fin 40)).trans h.1
  constructor
  · rw [readyBank, BitMachineClearBank.cleared_foreign cleanupSlots _ _ h29]
    exact (bank_at slots base _ (9 : Fin 40)).trans h.2.1
  · rw [readyBank, BitMachineClearBank.cleared_foreign cleanupSlots _ _ h21]
    exact (bank_at slots base _ (12 : Fin 40)).trans h.2.2

theorem ready_cleanup (base : Stack → List Bool) (a s q L rx cy : ℕ)
    (i : Fin 10) : readyBank base a s q L rx cy (cleanupSlots i) = [] :=
  BitMachineClearBank.cleared_bank cleanupSlots _ i

theorem ready_local_scratch (base : Stack → List Bool)
    (a s q L rx cy : ℕ) (i : Fin 40) (hi : 13 ≤ i.val) :
    readyBank base a s q L rx cy (slots i) = [] := by
  have hd : ∀ i : Fin 40, 13 ≤ i.val →
      ∀ j : Fin 10, cleanupSlots j ≠ slots i := by decide
  rw [readyBank, BitMachineClearBank.cleared_foreign cleanupSlots _ _ (hd i hi),
    producedBank, bank_at]
  exact ColumnScalarOutput.scratch_cleared a s q L rx cy i hi

theorem ready_frame (base : Stack → List Bool) (a s q L rx cy : ℕ)
    (k : Stack) (hk : ∀ i : Fin 40, slots i ≠ k) :
    readyBank base a s q L rx cy k = base k := by
  have hclean : ∀ i : Fin 10, cleanupSlots i ≠ k := by
    intro i hi
    have himage : ∀ i : Fin 10, ∃ j : Fin 40, cleanupSlots i = slots j := by
      intro j
      fin_cases j <;> decide
    obtain ⟨j, hj⟩ := himage i
    exact hk j (hj.symm.trans hi)
  rw [readyBank, BitMachineClearBank.cleared_foreign cleanupSlots _ k hclean]
  exact bank_outside slots base _ k (by
    rintro ⟨i, hi⟩; exact hk i hi)

theorem ready_eq_base (base : Stack → List Bool) (a s q L rx cy : ℕ)
    (hw : base 26 = List.replicate (MatrixStage4Digits.wordBase a s cy) true)
    (hb : base 29 = List.replicate (MatrixStage4Digits.binBase a s q cy) true)
    (hr : base 21 = List.replicate (MatrixStage4Codes.cols a s q cy) true)
    (hblank : ∀ i : Fin 40, i ≠ 8 → i ≠ 9 → i ≠ 12 → base (slots i) = []) :
    readyBank base a s q L rx cy = base := by
  funext k
  by_cases himage : ∃ i : Fin 40, slots i = k
  · obtain ⟨i, rfl⟩ := himage
    by_cases h8 : i = 8
    · subst i; exact (ready_outputs base a s q L rx cy).1.trans hw.symm
    by_cases h9 : i = 9
    · subst i; exact (ready_outputs base a s q L rx cy).2.1.trans hb.symm
    by_cases h12 : i = 12
    · subst i; exact (ready_outputs base a s q L rx cy).2.2.trans hr.symm
    have hcase : (∃ j : Fin 10, cleanupSlots j = slots i) ∨ 13 ≤ i.val := by
      have hall : ∀ i : Fin 40, i = 8 ∨ i = 9 ∨ i = 12 ∨
          (∃ j : Fin 10, cleanupSlots j = slots i) ∨ 13 ≤ i.val := by decide
      rcases hall i with hi8 | hi9 | hi12 | hrest
      · exact (h8 hi8).elim
      · exact (h9 hi9).elim
      · exact (h12 hi12).elim
      · exact hrest
    rcases hcase with ⟨j,hj⟩ | hi
    · rw [← hj, ready_cleanup]
      have hb0 := hblank i h8 h9 h12
      rw [← hj] at hb0
      exact hb0.symm
    · exact (ready_local_scratch base a s q L rx cy i hi).trans
        (hblank i h8 h9 h12).symm
  · exact ready_frame base a s q L rx cy k (by
      intro i hi; exact himage ⟨i,hi⟩)

/-- Existing semantic fields are held fixed, but the three derived output
cells are physically empty at the start and written by the embedded program. -/
def strippedBank (d : MatrixWeightedEntryController.Input) :
    Stack → List Bool :=
  fun k => if k = 21 ∨ k = 26 ∨ k = 29 then []
    else MatrixWeightedEntryController.persistentBank d k

theorem embedded_ignores_target_base
    (d : MatrixWeightedEntryController.Input) (S : Fin 40 → List Bool) :
    bank slots (strippedBank d) S =
      bank slots (MatrixWeightedEntryController.persistentBank d) S := by
  funext k
  by_cases himage : ∃ i : Fin 40, slots i = k
  · obtain ⟨i, rfl⟩ := himage
    simp only [bank_at]
  · rw [bank_outside slots _ S k himage,
      bank_outside slots _ S k himage]
    have h21 : k ≠ (21 : Stack) := by
      intro h; exact himage ⟨12, by simpa [slots] using h.symm⟩
    have h26 : k ≠ (26 : Stack) := by
      intro h; exact himage ⟨8, by simpa [slots] using h.symm⟩
    have h29 : k ≠ (29 : Stack) := by
      intro h; exact himage ⟨9, by simpa [slots] using h.symm⟩
    simp [strippedBank, h21, h26, h29]

noncomputable def actualSource {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    Stack → List Bool :=
  let d := MatrixWeightedEntrySemantic.actualInput
    R a s q L nv nb hs family order vectors cap
  sourceBank (strippedBank d) a s q L rx cy

theorem actual_ready_eq_writer {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput
      R a s q L nv nb hs family order vectors cap
    readyBank (MatrixWeightedEntryController.persistentBank d)
      a s q L rx cy = MatrixWeightedEntryController.persistentBank d := by
  dsimp
  apply ready_eq_base
  · rfl
  · rfl
  · rfl
  · intro i h8 h9 h12
    fin_cases i <;> simp_all [MatrixWeightedEntryController.persistentBank, slots]

theorem actual_embedded_run {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput
      R a s q L nv nb hs family order vectors cap
    ∃ t ≤ ColumnScalarOutput.polynomialCost a s q cy +
        clearCost (producedBank (strippedBank d)
          a s q L rx cy),
      run t (cfg (some start) initial
        (actualSource R a s q L nv nb hs family order vectors cap)) =
      cfg none initial (MatrixWeightedEntryController.persistentBank d) := by
  dsimp [actualSource]
  obtain ⟨t, ht, hr⟩ := embedded_run
    (strippedBank
      (MatrixWeightedEntrySemantic.actualInput
        R a s q L nv nb hs family order vectors cap)) a s q L rx cy
  refine ⟨t, ht, ?_⟩
  rw [hr]
  have he := embedded_ignores_target_base
    (MatrixWeightedEntrySemantic.actualInput
      R a s q L nv nb hs family order vectors cap)
    (ColumnScalarOutput.finalBank a s q L rx cy)
  have hready : readyBank
      (strippedBank (MatrixWeightedEntrySemantic.actualInput
        R a s q L nv nb hs family order vectors cap))
      a s q L rx cy =
      MatrixWeightedEntryController.persistentBank
        (MatrixWeightedEntrySemantic.actualInput
          R a s q L nv nb hs family order vectors cap) := by
    change BitMachineClearBank.cleared cleanupSlots
      (bank slots (strippedBank (MatrixWeightedEntrySemantic.actualInput
        R a s q L nv nb hs family order vectors cap))
        (ColumnScalarOutput.finalBank a s q L rx cy)) = _
    rw [he]
    exact actual_ready_eq_writer R a s q L nv nb hs family order vectors cap
  rw [hready]

theorem actual_source_targets_empty {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    actualSource R a s q L nv nb hs family order vectors cap 26 = [] ∧
    actualSource R a s q L nv nb hs family order vectors cap 29 = [] ∧
    actualSource R a s q L nv nb hs family order vectors cap 21 = [] := by
  exact source_targets_empty _ a s q L rx cy

theorem actual_run_joinCost {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput
      R a s q L nv nb hs family order vectors cap
    ∃ t ≤ joinCost a s q L rx cy,
      run t (cfg (some start) initial
        (actualSource R a s q L nv nb hs family order vectors cap)) =
      cfg none initial (MatrixWeightedEntryController.persistentBank d) := by
  obtain ⟨t,ht,hr⟩ := actual_embedded_run
    R a s q L nv nb hs family order vectors cap
  refine ⟨t, ?_, hr⟩
  rw [clearCost_produced] at ht
  unfold joinCost
  omega

#print axioms source_targets_empty
#print axioms clearCost_produced
#print axioms embedded_run
#print axioms ready_outputs
#print axioms ready_cleanup
#print axioms ready_local_scratch
#print axioms ready_frame
#print axioms ready_eq_base
#print axioms embedded_ignores_target_base
#print axioms actual_ready_eq_writer
#print axioms actual_embedded_run
#print axioms actual_source_targets_empty
#print axioms actual_run_joinCost

end EthInapproximability.CurrentPaper.ColumnWriterJoin
