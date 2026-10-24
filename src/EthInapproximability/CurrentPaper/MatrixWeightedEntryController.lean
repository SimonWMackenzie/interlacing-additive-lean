import EthInapproximability.CurrentPaper.MatrixWeightedRowController
import EthInapproximability.CurrentPaper.MatrixWeightedDiagonalMachine
import EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachine
import EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachineRun
import EthInapproximability.CurrentPaper.MatrixTableLookup
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# One literal protected-entry controller

The writer's row and column index words remain in its three distinguished
cell stacks.  This fixed controller physically copies them into work banks,
decodes the weighted 182:2 column and four row supports, computes the joint-
tail diagonal or order-translated raw addresses, reads the literal raw table,
and clears every temporary bank before returning one answer bit.  Correctness
and uniform runtime for the complete controller are separate theorems; the
finite program itself carries no semantic cell oracle.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedEntryController

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := MatrixTableWriter.CellStack 64

/-- Explicit supplied unary dimensions and literal payload tables.  A
constructor from the original instance remains a distinct charged runtime
obligation; no entry evaluation is hidden in this record. -/
structure Input where
  uniform : ℕ
  fullBoundary : ℕ
  fullDivisor : ℕ
  diagonalDivisor : ℕ
  nb : ℕ
  stagePrefixRows : ℕ
  rx : ℕ
  nv : ℕ
  rawWidth : ℕ
  wordBase : ℕ
  cy : ℕ
  s : ℕ
  binBase : ℕ
  rowBoundary₁ : ℕ
  rowBoundary₂ : ℕ
  rowBoundary₃ : ℕ
  rowDivisor₀ : ℕ
  rowDivisor₁ : ℕ
  rowDivisor₂ : ℕ
  rowDivisor₃ : ℕ
  rawBits : List Bool
  orderBits : List Bool

def persistentBank (d : Input) : Fin 64 → List Bool :=
  fun k =>
    if k = 1 then List.replicate d.uniform true
    else if k = 3 then List.replicate d.fullBoundary true
    else if k = 4 then List.replicate d.fullDivisor true
    else if k = 6 then List.replicate d.diagonalDivisor true
    else if k = 15 then List.replicate d.nb true
    else if k = 16 then List.replicate d.stagePrefixRows true
    else if k = 17 then List.replicate d.rx true
    else if k = 18 then List.replicate d.nv true
    else if k = 21 then List.replicate d.rawWidth true
    else if k = 22 then d.rawBits
    else if k = 26 then List.replicate d.wordBase true
    else if k = 27 then List.replicate d.cy true
    else if k = 28 then List.replicate d.s true
    else if k = 29 then List.replicate d.binBase true
    else if k = 47 then List.replicate d.rowBoundary₁ true
    else if k = 48 then List.replicate d.rowBoundary₂ true
    else if k = 49 then List.replicate d.rowBoundary₃ true
    else if k = 50 then List.replicate d.rowDivisor₀ true
    else if k = 51 then List.replicate d.rowDivisor₁ true
    else if k = 52 then List.replicate d.rowDivisor₂ true
    else if k = 53 then List.replicate d.rowDivisor₃ true
    else if k = 60 then d.orderBits
    else []

def cellBank (d : Input) (x y : ℕ) (answer : List Bool) : Stack → List Bool :=
  Sum.elim (persistentBank d)
    (![List.replicate x true, List.replicate y true, answer] : Fin 3 → List Bool)

def afterCopies (d : Input) (x y : ℕ) (answer : List Bool) : Stack → List Bool :=
  Function.update
    (Function.update (cellBank d x y answer) (.inl 0)
      (List.replicate x true))
    (.inl 20) (List.replicate y true)

def rowCopiedBank (d : Input) (y : ℕ) : Fin 64 → List Bool :=
  Function.update (persistentBank d) 20 (List.replicate y true)

def writerExtra (x y : ℕ) (answer : List Bool) : Fin 3 → List Bool :=
  ![List.replicate x true, List.replicate y true, answer]

theorem afterCopies_columnSeed (d : Input) (x y : ℕ)
    (answer : List Bool) :
    afterCopies d x y answer =
      Sum.elim
        (MatrixWeightedColumnController.seed (rowCopiedBank d y)
          x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
        (writerExtra x y answer) := by
  funext k
  cases k with
  | inl k =>
      fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

inductive State where
  | copy (v : Option Bool)
  | column (v : MatrixWeightedColumnController.State)
  | row (v : MatrixWeightedRowController.State)
  | diagonal (v : MatrixWeightedDiagonalMachine.State)
  | order (v : MatrixWeightedRowOrderMachine.State)
  | lookup (v : MatrixTableLookup.Control)
  deriving Fintype

abbrev Control := State × Option Bool

inductive Label where
  | copyColumn (l : BitMachineCopy.Label)
  | copyRowInit | copyRow (l : BitMachineCopy.Label)
  | columnInit | column (l : MatrixWeightedColumnController.Label)
  | afterColumn | diagonalInit
  | diagonal (l : MatrixWeightedDiagonalMachine.Label)
  | rowInit | row (l : MatrixWeightedRowController.Label)
  | clearRowWork | clearRowOne | afterRow
  | directInit | direct (l : BitMachineCopy.Label)
  | orderInit (aux : Bool) | order (l : MatrixWeightedRowOrderMachine.Label)
  | lookupInit | lookup (l : MatrixTableLookup.Label)
  | clear (i : Fin 42) | done
  deriving Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (.copy none, none)
def getCopy : Control → Option Bool
  | (.copy v, _) => v
  | _ => none
def getColumn : Control → MatrixWeightedColumnController.State
  | (.column v, _) => v
  | _ => MatrixWeightedColumnController.initial
def getRow : Control → MatrixWeightedRowController.State
  | (.row v, _) => v
  | _ => MatrixWeightedRowController.initial
def getDiagonal : Control → MatrixWeightedDiagonalMachine.State
  | (.diagonal v, _) => v
  | _ => MatrixWeightedDiagonalMachine.initial
def getOrder : Control → MatrixWeightedRowOrderMachine.State
  | (.order v, _) => v
  | _ => MatrixWeightedRowOrderMachine.initial
def getLookup : Control → MatrixTableLookup.Control
  | (.lookup v, _) => v
  | _ => MatrixTableLookup.initial

def diagonalFlag : Control → Bool
  | (.column (.terminal v), _) => v
  | _ => false
def chosenGroup : Control → Fin 4
  | (.row (.chosen g), _) => g
  | _ => 0

def copyColumnSlots : Fin 3 ↪ Stack :=
  ⟨![.inr 0, .inl 0, .inl 14], by decide⟩
def copyRowSlots : Fin 3 ↪ Stack :=
  ⟨![.inr 1, .inl 20, .inl 14], by decide⟩
def directSlots : Fin 3 ↪ Stack :=
  ⟨![.inl 54, .inl 25, .inl 14], by decide⟩
def globalSlots : Fin 64 ↪ Stack :=
  ⟨Sum.inl, by intro i j h; cases h; rfl⟩
def diagonalSlots : MatrixWeightedDiagonalMachine.Stack ↪ Stack :=
  ⟨fun i => .inl ((![5,26,27,28,29,19,30,31,32,33,34,35,36,37,38,
      39,40,41,42,43,44,45,46] : Fin 23 → Fin 64) i), by decide⟩
def orderSlots : MatrixWeightedRowOrderMachine.Stack ↪ Stack where
  toFun i := .inl (MatrixWeightedRowOrderMachine.globalSlots i)
  inj' := by
    intro i j h
    exact MatrixWeightedRowOrderMachine.globalSlots.injective (Sum.inl.inj h)
def lookupSlots : MatrixTableLookup.Stack ↪ Stack :=
  ⟨![.inl 25, .inl 21, .inl 19, .inl 30, .inl 31, .inl 32,
      .inl 22, .inr 2, .inl 33, .inl 34], by decide⟩

/-- Exactly the work stacks; writer coordinates, raw bits, order bits, and all
supplied unary dimensions lie outside this list. -/
def workSlot : Fin 41 → Stack :=
  (![.inl 0, .inl 2, .inl 5,
    .inl 7, .inl 8, .inl 9, .inl 10, .inl 11, .inl 12, .inl 13, .inl 14,
    .inl 19, .inl 20, .inl 23, .inl 25,
    .inl 30, .inl 31, .inl 32, .inl 33, .inl 34, .inl 35, .inl 36,
    .inl 37, .inl 38, .inl 39, .inl 40, .inl 41, .inl 42, .inl 43,
    .inl 44, .inl 45, .inl 46,
    .inl 54, .inl 55, .inl 56, .inl 57, .inl 58, .inl 59,
    .inl 61, .inl 62, .inl 63] : Fin 41 → Stack)

theorem workSlot_injective : Function.Injective workSlot := by decide

theorem cellBank_work_empty (d : Input) (x y : ℕ)
    (answer : List Bool) (i : Fin 41) :
    cellBank d x y answer (workSlot i) = [] := by
  fin_cases i <;> rfl

theorem cleared_to_cellBank (d : Input) (x y : ℕ)
    (answer : List Bool) (S : Stack → List Bool)
    (hstable : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      S k = cellBank d x y answer k) :
    BitMachineClearBank.cleared workSlot S = cellBank d x y answer := by
  funext k
  by_cases h : ∃ i, workSlot i = k
  · obtain ⟨i, rfl⟩ := h
    rw [BitMachineClearBank.cleared_bank]
    exact (cellBank_work_empty d x y answer i).symm
  · rw [BitMachineClearBank.cleared_foreign workSlot S k]
    · exact hstable k (by intro i hi; exact h ⟨i,hi⟩)
    · intro i hi
      exact h ⟨i,hi⟩

theorem global_bank (S T : Fin 64 → List Bool)
    (extra : Fin 3 → List Bool) :
    BitMachineStackEmbedding.bank globalSlots (Sum.elim S extra) T =
      Sum.elim T extra := by
  funext j
  cases j with
  | inl k => exact bank_at globalSlots (Sum.elim S extra) T k
  | inr k =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copyColumn l => stmt copyColumnSlots Label.copyColumn
      (fun v => (.copy v, none)) getCopy (some .copyRowInit)
      (BitMachineCopy.program l)
  | .copyRowInit => load (fun _ => (.copy none, none))
      (goto (fun _ => .copyRow .scan))
  | .copyRow l => stmt copyRowSlots Label.copyRow
      (fun v => (.copy v, none)) getCopy (some .columnInit)
      (BitMachineCopy.program l)
  | .columnInit => load (fun _ => (.column MatrixWeightedColumnController.initial, none))
      (goto (fun _ => .column MatrixWeightedColumnController.start))
  | .column l => stmt globalSlots Label.column (fun v => (.column v, none))
      getColumn (some .afterColumn) (MatrixWeightedColumnController.program l)
  | .afterColumn => branch diagonalFlag
      (goto (fun _ => .diagonalInit)) (goto (fun _ => .rowInit))
  | .diagonalInit => load (fun _ => (.diagonal MatrixWeightedDiagonalMachine.initial, none))
      (goto (fun _ => .diagonal MatrixWeightedDiagonalMachine.start))
  | .diagonal l => stmt diagonalSlots Label.diagonal
      (fun v => (.diagonal v, none)) getDiagonal (some .rowInit)
      (MatrixWeightedDiagonalMachine.program l)
  | .rowInit => load (fun _ => (.row MatrixWeightedRowController.initial, none))
      (goto (fun _ => .row MatrixWeightedRowController.start))
  | .row l => stmt globalSlots Label.row (fun v => (.row v, none))
      getRow (some .clearRowWork) (MatrixWeightedRowController.program l)
  | .clearRowWork => BitMachineClearBank.clearStep
      (.inl 23) .clearRowWork .clearRowOne
  | .clearRowOne => BitMachineClearBank.clearStep
      (.inl 63) .clearRowOne .afterRow
  | .afterRow => branch (fun v => (chosenGroup v).val < 2)
      (goto (fun _ => .directInit))
      (goto (fun v => .orderInit (chosenGroup v == 3)))
  | .directInit => load (fun _ => (.copy none, none))
      (goto (fun _ => .direct .scan))
  | .direct l => stmt directSlots Label.direct (fun v => (.copy v, none))
      getCopy (some .lookupInit) (BitMachineCopy.program l)
  | .orderInit aux => load (fun _ => (.order MatrixWeightedRowOrderMachine.initial, none))
      (goto (fun _ => .order (MatrixWeightedRowOrderMachine.start aux)))
  | .order l => stmt orderSlots Label.order (fun v => (.order v, none))
      getOrder (some .lookupInit) (MatrixWeightedRowOrderMachine.program l)
  | .lookupInit => load (fun _ => (.lookup MatrixTableLookup.initial, none))
      (goto (fun _ => .lookup MatrixTableLookup.start))
  | .lookup l => stmt lookupSlots Label.lookup (fun v => (.lookup v, none))
      getLookup (some (.clear 0)) (MatrixTableLookup.program l)
  | .clear i => if h : i.val < 41 then
      BitMachineClearBank.clearStep (workSlot ⟨i.val, h⟩) (.clear i)
        (.clear ⟨i.val + 1, by omega⟩)
      else BitMachineClearBank.finishStep (fun _ => initial.1) .done
  | .done => halt

def start : Label := .copyColumn .scan
def cfg (l : Option Label) (v : Control) (bank : Stack → List Bool) : Config :=
  ⟨l,v,bank⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

/-- Any terminating Fin64 phase is charged transition-for-transition in the
writer's cell stack; the three writer-owned coordinate/answer stacks frame. -/
theorem lift_global_phase {L V : Type*}
    (P : L → TM2.Stmt (fun _ : Fin 64 => Bool) L V)
    (labels : L → Label) (embed : V → Control) (read : Control → V)
    (hread : Function.LeftInverse read embed) (next : Label)
    (hprogram : ∀ l, program (labels l) =
      stmt globalSlots labels embed read (some next) (P l))
    (l : L) (v w : V) (S T : Fin 64 → List Bool)
    (extra : Fin 3 → List Bool) (bound : ℕ)
    (hrun : ((advance P)^[bound]) ⟨some l,v,S⟩ = ⟨none,w,T⟩) :
    ∃ t ≤ bound,
      run t (cfg (some (labels l)) (embed v) (Sum.elim S extra)) =
      cfg (some next) (embed w) (Sum.elim T extra) := by
  let c : TM2.Cfg (fun _ : Fin 64 => Bool) L V := ⟨some l,v,S⟩
  have hhalt : (((advance P)^[bound]) c).l = none := by
    rw [hrun]
  obtain ⟨t, ht, he⟩ := outputs globalSlots (Sum.elim S extra)
    labels embed read hread (some next) P program hprogram c bound hhalt
  rw [hrun] at he
  refine ⟨t, ht, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    global_bank, cfg, run] using he

theorem clear_run (v : State) (S : Stack → List Bool) :
    run ((∑ i, (S (workSlot i)).length) + 43)
      (cfg (some (.clear 0)) (v, none) S) =
      cfg none initial (BitMachineClearBank.cleared workSlot S) := by
  have hs (i : Fin 41) : program (.clear i.castSucc) =
      BitMachineClearBank.clearStep (workSlot i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [program, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : program (.clear (Fin.last 41)) =
      BitMachineClearBank.finishStep (fun _ => initial.1) .done := by
    simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run program
    (fun _ => initial.1) .done 41 workSlot workSlot_injective
    Label.clear hs hf v S
  have hd : run 1
      (cfg (some .done) initial (BitMachineClearBank.cleared workSlot S)) =
      cfg none initial (BitMachineClearBank.cleared workSlot S) := rfl
  simpa only [Nat.add_assoc] using (run_add hr 1).trans hd

theorem copy_stage (slots : Fin 3 ↪ Stack)
    (label : BitMachineCopy.Label → Label) (next : Label)
    (hprogram : ∀ l, program (label l) =
      stmt slots label (fun v => (.copy v, none)) getCopy (some next)
        (BitMachineCopy.program l))
    (S : Stack → List Bool) (source target : Stack) (n : ℕ)
    (hslots : slots 0 = source ∧ slots 1 = target)
    (hs : S source = List.replicate n true)
    (ht : S target = []) (hw : S (slots 2) = []) :
    ∃ t ≤ 2*n+2,
      run t (cfg (some (label .scan)) (.copy none, none) S) =
        cfg (some next) (.copy none, none)
          (Function.update S target (List.replicate n true)) := by
  let c := BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] []
  have hrun := BitMachineCopy.run_correct none (List.replicate n true) []
  simp only [List.length_replicate, List.append_nil] at hrun
  have hhalt : (((advance BitMachineCopy.program)^[2*n+2]) c).l = none := by
    change (BitMachineCopy.run (2*n+2) c).l = none
    rw [hrun]
    rfl
  obtain ⟨t, ht', he⟩ := outputs slots S label
    (fun v => (.copy v, none)) getCopy (fun _ => rfl) (some next)
    BitMachineCopy.program program hprogram c (2*n+2) hhalt
  have hrun' : ((advance BitMachineCopy.program)^[2*n+2]) c =
      BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) [] := hrun
  rw [hrun'] at he
  have hinit : BitMachineStackEmbedding.bank slots S c.stk = S := by
    apply bank_eq_self
    intro i
    fin_cases i <;> simp [c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hslots.1, hslots.2, hs, ht, hw]
  have hfinal : BitMachineStackEmbedding.bank slots S
      (BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) []).stk =
      Function.update S target (List.replicate n true) := by
    have hu : (BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) []).stk =
        Function.update c.stk 1 (List.replicate n true) := by
      funext i
      fin_cases i <;> rfl
    rw [hu, bank_update, hslots.2, hinit]
  exact ⟨t, ht', by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hinit, hfinal,
    cfg, run] using he⟩

theorem copy_column_run (d : Input) (x y : ℕ) (answer : List Bool) :
    ∃ t ≤ 2*x+2,
      run t (cfg (some start) initial (cellBank d x y answer)) =
      cfg (some .copyRowInit) initial
        (Function.update (cellBank d x y answer) (.inl 0)
          (List.replicate x true)) := by
  apply copy_stage copyColumnSlots Label.copyColumn .copyRowInit
    (by intro l; rfl) (cellBank d x y answer) (.inr 0) (.inl 0) x
  · exact ⟨rfl,rfl⟩
  · rfl
  · simp [cellBank, persistentBank]
  · simp [cellBank, persistentBank, copyColumnSlots]

theorem copy_coordinates_run (d : Input) (x y : ℕ)
    (answer : List Bool) :
    ∃ t ≤ (2*x+2) + (2*y+3),
      run t (cfg (some start) initial (cellBank d x y answer)) =
      cfg (some .columnInit) initial (afterCopies d x y answer) := by
  obtain ⟨tx, htx, hx⟩ := copy_column_run d x y answer
  let S := Function.update (cellBank d x y answer) (.inl 0)
    (List.replicate x true)
  have hs : S (.inr 1) = List.replicate y true := by
    rfl
  have ht : S (.inl 20) = [] := by
    rfl
  have hw : S (copyRowSlots 2) = [] := by
    rfl
  obtain ⟨ty, hty, hy⟩ := copy_stage copyRowSlots Label.copyRow
    .columnInit (by intro l; rfl) S (.inr 1) (.inl 20) y
    ⟨rfl,rfl⟩ hs ht hw
  have hinit : advance program
      (cfg (some .copyRowInit) initial S) =
      cfg (some (.copyRow .scan)) initial S := rfl
  have hrow : run (ty+1) (cfg (some .copyRowInit) initial S) =
      cfg (some .columnInit) initial
        (Function.update S (.inl 20) (List.replicate y true)) := by
    rw [run_succ hinit ty]
    exact hy
  refine ⟨tx + (ty+1), by omega, ?_⟩
  rw [run_add hx]
  simpa only [afterCopies, S] using hrow

def afterFullColumn (d : Input) (x y : ℕ)
    (answer : List Bool) : Stack → List Bool :=
  Sum.elim
    (MatrixWeightedColumnController.afterFull (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    (writerExtra x y answer)

def afterDiagonalColumn (d : Input) (x y : ℕ)
    (answer : List Bool) : Stack → List Bool :=
  Sum.elim
    (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    (writerExtra x y answer)

def fullCore (d : Input) (x y : ℕ) : Fin 64 → List Bool :=
  MatrixWeightedColumnController.afterFull (rowCopiedBank d y)
    x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor

def diagonalCode (d : Input) (x : ℕ) : ℕ :=
  (x / d.uniform - d.fullBoundary) / d.diagonalDivisor

def diagonalCore (d : Input) (x y : ℕ) : Fin 64 → List Bool :=
  Function.update
    (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    19 (List.replicate
      (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
        d.wordBase d.cy d.s d.binBase) true)

def vertexLabel (d : Input) (y : ℕ) : ℕ :=
  (y-d.rowBoundary₁-d.rowBoundary₂) / d.rowDivisor₂

def auxiliaryLabel (d : Input) (y : ℕ) : ℕ :=
  (y-d.rowBoundary₁-d.rowBoundary₂-d.rowBoundary₃) / d.rowDivisor₃

def fullLabel (d : Input) (y : ℕ) : ℕ := y / d.rowDivisor₀

def templateLabel (d : Input) (y : ℕ) : ℕ :=
  (y-d.rowBoundary₁) / d.rowDivisor₁

def fullRowResult (d : Input) (S : Fin 64 → List Bool) (y : ℕ) :
    Fin 64 → List Bool :=
  Function.update
    (MatrixWeightedRowController.afterCut1 S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
    54 (List.replicate (fullLabel d y) true)

def templateRowResult (d : Input) (S : Fin 64 → List Bool) (y : ℕ) :
    Fin 64 → List Bool :=
  Function.update
    (MatrixWeightedRowController.afterCut2 S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
    54 (List.replicate (templateLabel d y) true)

def vertexRowResult (d : Input) (S : Fin 64 → List Bool) (y : ℕ) :
    Fin 64 → List Bool :=
  Function.update
    (MatrixWeightedRowController.afterCut3 S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
    54 (List.replicate (vertexLabel d y) true)

def auxiliaryRowResult (d : Input) (S : Fin 64 → List Bool) (y : ℕ) :
    Fin 64 → List Bool :=
  Function.update
    (MatrixWeightedRowController.afterCut3 S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
    54 (List.replicate (auxiliaryLabel d y) true)

theorem diagonal_input_frame (d : Input) (x y : ℕ)
    (answer : List Bool) (i : MatrixWeightedDiagonalMachine.Stack) :
    afterDiagonalColumn d x y answer (diagonalSlots i) =
      MatrixWeightedDiagonalMachine.unary
        (MatrixWeightedDiagonalMachine.inputWords
          (diagonalCode d x) d.wordBase d.cy d.s d.binBase) i := by
  fin_cases i <;> rfl

theorem full_row_seed_frame (d : Input) (x y : ℕ)
    (answer : List Bool) :
    MatrixWeightedRowController.seed
      (MatrixWeightedColumnController.afterFull (rowCopiedBank d y)
        x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
      y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ =
    MatrixWeightedColumnController.afterFull (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor := by
  funext k
  fin_cases k <;> rfl

theorem diagonal_row_seed_frame (d : Input) (x y rawOrdinal : ℕ)
    (answer : List Bool) :
    MatrixWeightedRowController.seed
      (Function.update
        (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
          x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
        19 (List.replicate rawOrdinal true))
      y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ =
    Function.update
      (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
        x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
      19 (List.replicate rawOrdinal true) := by
  funext k
  fin_cases k <;> rfl

theorem column_full_run (d : Input) (x y : ℕ) (answer : List Bool)
    (hfull : x / d.uniform < d.fullBoundary) :
    ∃ t ≤ 1 +
      ((11*x + 3*d.uniform + 7) +
        (3*min (x/d.uniform) d.fullBoundary + 5) +
        (11*(x/d.uniform) + 3*d.fullDivisor + 10)),
      run t (cfg (some .columnInit) initial (afterCopies d x y answer)) =
      cfg (some .afterColumn) (.column (.terminal false), none)
        (afterFullColumn d x y answer) := by
  obtain ⟨tc, htc, hc⟩ :=
    MatrixWeightedColumnController.full_controller_run (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor hfull
  have hlocal : ((advance MatrixWeightedColumnController.program)^[tc])
      (MatrixWeightedColumnController.cfg
        (some MatrixWeightedColumnController.start)
        MatrixWeightedColumnController.initial
        (MatrixWeightedColumnController.seed (rowCopiedBank d y)
          x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)) =
      MatrixWeightedColumnController.cfg none (.terminal false)
        (MatrixWeightedColumnController.afterFull (rowCopiedBank d y)
          x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor) := hc
  obtain ⟨t, ht, he⟩ := lift_global_phase
    MatrixWeightedColumnController.program Label.column
    (fun v => (.column v, none)) getColumn (by intro v; rfl) .afterColumn
    (by intro l; rfl)
    MatrixWeightedColumnController.start MatrixWeightedColumnController.initial
    (.terminal false)
    (MatrixWeightedColumnController.seed (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    (MatrixWeightedColumnController.afterFull (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    (writerExtra x y answer) tc hlocal
  have hinit : advance program
      (cfg (some .columnInit) initial (afterCopies d x y answer)) =
      cfg (some (.column MatrixWeightedColumnController.start))
        (.column MatrixWeightedColumnController.initial, none)
        (Sum.elim
          (MatrixWeightedColumnController.seed (rowCopiedBank d y)
            x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
          (writerExtra x y answer)) := by
    rw [afterCopies_columnSeed]
    rfl
  refine ⟨t+1, by omega, ?_⟩
  rw [run_succ hinit t]
  exact he

theorem column_diagonal_run (d : Input) (x y : ℕ)
    (answer : List Bool) (hdiag : d.fullBoundary ≤ x / d.uniform) :
    ∃ t ≤ 1 +
      ((11*x + 3*d.uniform + 7) +
        (3*min (x/d.uniform) d.fullBoundary + 5) +
        (11*(x/d.uniform-d.fullBoundary) + 3*d.diagonalDivisor + 10)),
      run t (cfg (some .columnInit) initial (afterCopies d x y answer)) =
      cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y answer) := by
  obtain ⟨tc, htc, hc⟩ :=
    MatrixWeightedColumnController.diagonal_controller_run (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor hdiag
  have hlocal : ((advance MatrixWeightedColumnController.program)^[tc])
      (MatrixWeightedColumnController.cfg
        (some MatrixWeightedColumnController.start)
        MatrixWeightedColumnController.initial
        (MatrixWeightedColumnController.seed (rowCopiedBank d y)
          x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)) =
      MatrixWeightedColumnController.cfg none (.terminal true)
        (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
          x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor) := hc
  obtain ⟨t, ht, he⟩ := lift_global_phase
    MatrixWeightedColumnController.program Label.column
    (fun v => (.column v, none)) getColumn (by intro v; rfl) .afterColumn
    (by intro l; rfl)
    MatrixWeightedColumnController.start MatrixWeightedColumnController.initial
    (.terminal true)
    (MatrixWeightedColumnController.seed (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
      x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
    (writerExtra x y answer) tc hlocal
  have hinit : advance program
      (cfg (some .columnInit) initial (afterCopies d x y answer)) =
      cfg (some (.column MatrixWeightedColumnController.start))
        (.column MatrixWeightedColumnController.initial, none)
        (Sum.elim
          (MatrixWeightedColumnController.seed (rowCopiedBank d y)
            x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor)
          (writerExtra x y answer)) := by
    rw [afterCopies_columnSeed]
    rfl
  refine ⟨t+1, by omega, ?_⟩
  rw [run_succ hinit t]
  exact he

theorem diagonal_stage (d : Input) (x y : ℕ)
    (answer : List Bool) (rawOrdinal bound : ℕ)
    (hrun : ∃ t ≤ bound,
      MatrixWeightedDiagonalMachine.run t
        (MatrixWeightedDiagonalMachine.cfg
          (some MatrixWeightedDiagonalMachine.start)
          MatrixWeightedDiagonalMachine.initial
          (MatrixWeightedDiagonalMachine.unary
            (MatrixWeightedDiagonalMachine.inputWords
              (diagonalCode d x) d.wordBase d.cy d.s d.binBase))) =
      MatrixWeightedDiagonalMachine.cfg none .idle
        (MatrixWeightedDiagonalMachine.unary
          (Function.update
            (MatrixWeightedDiagonalMachine.inputWords
              (diagonalCode d x) d.wordBase d.cy d.s d.binBase)
            5 rawOrdinal))) :
    ∃ t ≤ bound,
      run t
        (cfg (some (.diagonal MatrixWeightedDiagonalMachine.start))
          (.diagonal MatrixWeightedDiagonalMachine.initial, none)
          (afterDiagonalColumn d x y answer)) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Function.update (afterDiagonalColumn d x y answer)
          (.inl 19) (List.replicate rawOrdinal true)) := by
  obtain ⟨td, htd, hd⟩ := hrun
  let S := afterDiagonalColumn d x y answer
  let lc := MatrixWeightedDiagonalMachine.cfg
    (some MatrixWeightedDiagonalMachine.start)
    MatrixWeightedDiagonalMachine.initial
    (MatrixWeightedDiagonalMachine.unary
      (MatrixWeightedDiagonalMachine.inputWords
        (diagonalCode d x) d.wordBase d.cy d.s d.binBase))
  have hhalt : (((advance MatrixWeightedDiagonalMachine.program)^[td]) lc).l = none := by
    change (MatrixWeightedDiagonalMachine.run td lc).l = none
    rw [hd]
    rfl
  obtain ⟨t, ht, he⟩ := outputs diagonalSlots S Label.diagonal
    (fun v => (.diagonal v, none)) getDiagonal (by intro v; rfl)
    (some .rowInit) MatrixWeightedDiagonalMachine.program program
    (by intro l; rfl) lc td hhalt
  have hd' : ((advance MatrixWeightedDiagonalMachine.program)^[td]) lc =
      MatrixWeightedDiagonalMachine.cfg none .idle
        (MatrixWeightedDiagonalMachine.unary
          (Function.update
            (MatrixWeightedDiagonalMachine.inputWords
              (diagonalCode d x) d.wordBase d.cy d.s d.binBase)
            5 rawOrdinal)) := hd
  rw [hd'] at he
  have hinit : BitMachineStackEmbedding.bank diagonalSlots S lc.stk = S := by
    apply bank_eq_self
    intro k
    exact (diagonal_input_frame d x y answer k).symm
  have hinit' : BitMachineStackEmbedding.bank diagonalSlots S
      (MatrixWeightedDiagonalMachine.unary
        (MatrixWeightedDiagonalMachine.inputWords
          (diagonalCode d x) d.wordBase d.cy d.s d.binBase)) = S := by
    simpa only [lc, MatrixWeightedDiagonalMachine.cfg] using hinit
  have hfinal : BitMachineStackEmbedding.bank diagonalSlots S
      (MatrixWeightedDiagonalMachine.unary
        (Function.update
          (MatrixWeightedDiagonalMachine.inputWords
            (diagonalCode d x) d.wordBase d.cy d.s d.binBase)
          5 rawOrdinal)) =
      Function.update S (.inl 19) (List.replicate rawOrdinal true) := by
    rw [← MatrixWeightedDiagonalMachine.unary_update,
      bank_update, hinit']
    rfl
  have hi : BitMachineStackEmbedding.cfg diagonalSlots S Label.diagonal
      (fun v => (.diagonal v, none)) (some .rowInit) lc =
      cfg (some (.diagonal MatrixWeightedDiagonalMachine.start))
        (.diagonal MatrixWeightedDiagonalMachine.initial, none) S := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg cfg
    congr 1
  have ho : BitMachineStackEmbedding.cfg diagonalSlots S Label.diagonal
      (fun v => (.diagonal v, none)) (some .rowInit)
      (MatrixWeightedDiagonalMachine.cfg none .idle
        (MatrixWeightedDiagonalMachine.unary
          (Function.update
            (MatrixWeightedDiagonalMachine.inputWords
              (diagonalCode d x) d.wordBase d.cy d.s d.binBase)
            5 rawOrdinal))) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Function.update S (.inl 19) (List.replicate rawOrdinal true)) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg cfg
    congr 1
  exact ⟨t, ht.trans htd, by simpa only [hi, ho, run] using he⟩

theorem diagonal_phase (d : Input) (x y : ℕ)
    (answer : List Bool) (rawOrdinal bound : ℕ)
    (hrun : ∃ t ≤ bound,
      MatrixWeightedDiagonalMachine.run t
        (MatrixWeightedDiagonalMachine.cfg
          (some MatrixWeightedDiagonalMachine.start)
          MatrixWeightedDiagonalMachine.initial
          (MatrixWeightedDiagonalMachine.unary
            (MatrixWeightedDiagonalMachine.inputWords
              (diagonalCode d x) d.wordBase d.cy d.s d.binBase))) =
      MatrixWeightedDiagonalMachine.cfg none .idle
        (MatrixWeightedDiagonalMachine.unary
          (Function.update
            (MatrixWeightedDiagonalMachine.inputWords
              (diagonalCode d x) d.wordBase d.cy d.s d.binBase)
            5 rawOrdinal))) :
    ∃ t ≤ bound + 2,
      run t (cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y answer)) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Function.update (afterDiagonalColumn d x y answer)
          (.inl 19) (List.replicate rawOrdinal true)) := by
  obtain ⟨td, htd, hd⟩ := diagonal_stage d x y answer rawOrdinal bound hrun
  let S := afterDiagonalColumn d x y answer
  have hdispatch : advance program
      (cfg (some .afterColumn) (.column (.terminal true), none) S) =
      cfg (some .diagonalInit) (.column (.terminal true), none) S := rfl
  have hinit : advance program
      (cfg (some .diagonalInit) (.column (.terminal true), none) S) =
      cfg (some (.diagonal MatrixWeightedDiagonalMachine.start))
        (.diagonal MatrixWeightedDiagonalMachine.initial, none) S := rfl
  have htwo : run 2
      (cfg (some .afterColumn) (.column (.terminal true), none) S) =
      cfg (some (.diagonal MatrixWeightedDiagonalMachine.start))
        (.diagonal MatrixWeightedDiagonalMachine.initial, none) S := by
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero, id_eq]
    rw [hdispatch, hinit]
  exact ⟨2+td, by omega, (run_add htwo td).trans hd⟩

theorem diagonal_arithmetic_phase (d : Input) (x y : ℕ)
    (answer : List Bool) :
    ∃ t ≤ MatrixWeightedDiagonalMachine.bound
        (diagonalCode d x) d.wordBase d.cy d.s d.binBase + 2,
      run t (cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y answer)) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Function.update (afterDiagonalColumn d x y answer)
          (.inl 19)
          (List.replicate
            (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
              d.wordBase d.cy d.s d.binBase) true)) := by
  let code := diagonalCode d x
  let value := MatrixWeightedDiagonalMachine.rawValue code
    d.wordBase d.cy d.s d.binBase
  have hwords : MatrixWeightedDiagonalMachine.outputWords code
      d.wordBase d.cy d.s d.binBase =
      Function.update
        (MatrixWeightedDiagonalMachine.inputWords code
          d.wordBase d.cy d.s d.binBase) 5 value := by
    funext k
    fin_cases k <;> rfl
  have hr := MatrixWeightedDiagonalMachine.run_arithmetic code
    d.wordBase d.cy d.s d.binBase
  rw [hwords] at hr
  simpa only [code, value] using diagonal_phase d x y answer value
    (MatrixWeightedDiagonalMachine.bound code d.wordBase d.cy d.s d.binBase) hr

/-- Generic charged embedding of any of the four already proved row paths.
The bank-frame equality is an exact initialization condition, subsequently
discharged from `persistentBank`; it is not an entry-oracle hypothesis. -/
theorem row_phase_from (S T : Fin 64 → List Bool)
    (extra : Fin 3 → List Bool) (v : State) (g : Fin 4) (bound : ℕ)
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T) :
    ∃ t ≤ bound + 1,
      run t (cfg (some .rowInit) (v, none) (Sum.elim S extra)) =
      cfg (some .clearRowWork) (.row (.chosen g), none)
        (Sum.elim T extra) := by
  obtain ⟨tr, htr, hr⟩ := hrun
  obtain ⟨t, ht, he⟩ := lift_global_phase
    MatrixWeightedRowController.program Label.row
    (fun v => (.row v, none)) getRow (by intro v; rfl) .clearRowWork
    (by intro l; rfl)
    MatrixWeightedRowController.start MatrixWeightedRowController.initial
    (.chosen g) S T extra tr hr
  have hinit : advance program
      (cfg (some .rowInit) (v, none) (Sum.elim S extra)) =
      cfg (some (.row MatrixWeightedRowController.start))
        (.row MatrixWeightedRowController.initial, none)
        (Sum.elim S extra) := rfl
  refine ⟨t+1, by omega, ?_⟩
  rw [run_succ hinit t]
  exact he

theorem row_phase (S T : Fin 64 → List Bool)
    (extra : Fin 3 → List Bool) (g : Fin 4) (bound : ℕ)
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T) :
    ∃ t ≤ bound + 1,
      run t (cfg (some .rowInit) initial (Sum.elim S extra)) =
      cfg (some .clearRowWork) (.row (.chosen g), none)
        (Sum.elim T extra) :=
  row_phase_from S T extra initial.1 g bound hrun

theorem full_row_stage (d : Input) (y : ℕ)
    (S : Fin 64 → List Bool) (extra : Fin 3 → List Bool)
    (hframe : MatrixWeightedRowController.seed S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ = S)
    (hfull : y < d.rowBoundary₁) :
    ∃ t ≤ (11*y + 11) + (3*min y d.rowBoundary₁ + 5) +
      (11*y + 3*d.rowDivisor₀ + 10) + 1,
      run t (cfg (some .rowInit) initial (Sum.elim S extra)) =
      cfg (some .clearRowWork) (.row (.chosen 0), none)
        (Sum.elim
          (Function.update
            (MatrixWeightedRowController.afterCut1 S y
              d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
              d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
            54 (List.replicate (y / d.rowDivisor₀) true)) extra) := by
  have hr := MatrixWeightedRowController.full_controller_run S y
    d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ hfull
  rw [hframe] at hr
  exact row_phase S _ extra 0 _ hr

theorem template_row_stage (d : Input) (y : ℕ)
    (S : Fin 64 → List Bool) (extra : Fin 3 → List Bool)
    (hframe : MatrixWeightedRowController.seed S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ = S)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y - d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t ≤ (11*y + 11) + (3*min y d.rowBoundary₁ + 5) +
      (3*min (y-d.rowBoundary₁) d.rowBoundary₂ + 6) +
      (11*(y-d.rowBoundary₁) + 3*d.rowDivisor₁ + 10) + 1,
      run t (cfg (some .rowInit) initial (Sum.elim S extra)) =
      cfg (some .clearRowWork) (.row (.chosen 1), none)
        (Sum.elim
          (Function.update
            (MatrixWeightedRowController.afterCut2 S y
              d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
              d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
            54 (List.replicate
              ((y-d.rowBoundary₁) / d.rowDivisor₁) true)) extra) := by
  have hr := MatrixWeightedRowController.template_controller_run S y
    d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ h₁ htemplate
  rw [hframe] at hr
  exact row_phase S _ extra 1 _ hr

theorem vertex_row_stage (d : Input) (y : ℕ)
    (S : Fin 64 → List Bool) (extra : Fin 3 → List Bool)
    (hframe : MatrixWeightedRowController.seed S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ = S)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t ≤ (11*y + 11) + (3*min y d.rowBoundary₁ + 5) +
      (3*min (y-d.rowBoundary₁) d.rowBoundary₂ + 6) +
      (3*min (y-d.rowBoundary₁-d.rowBoundary₂) d.rowBoundary₃ + 6) +
      (11*(y-d.rowBoundary₁-d.rowBoundary₂) + 3*d.rowDivisor₂ + 10) + 1,
      run t (cfg (some .rowInit) initial (Sum.elim S extra)) =
      cfg (some .clearRowWork) (.row (.chosen 2), none)
        (Sum.elim
          (Function.update
            (MatrixWeightedRowController.afterCut3 S y
              d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
              d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
            54 (List.replicate
              ((y-d.rowBoundary₁-d.rowBoundary₂) / d.rowDivisor₂) true)) extra) := by
  have hr := MatrixWeightedRowController.vertex_controller_run S y
    d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ hvertex
  rw [hframe] at hr
  exact row_phase S _ extra 2 _ hr

theorem auxiliary_row_stage (d : Input) (y : ℕ)
    (S : Fin 64 → List Bool) (extra : Fin 3 → List Bool)
    (hframe : MatrixWeightedRowController.seed S y
      d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
      d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ = S)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t ≤ (11*y + 11) + (3*min y d.rowBoundary₁ + 5) +
      (3*min (y-d.rowBoundary₁) d.rowBoundary₂ + 6) +
      (3*min (y-d.rowBoundary₁-d.rowBoundary₂) d.rowBoundary₃ + 6) +
      (11*(y-d.rowBoundary₁-d.rowBoundary₂-d.rowBoundary₃) +
        3*d.rowDivisor₃ + 10) + 1,
      run t (cfg (some .rowInit) initial (Sum.elim S extra)) =
      cfg (some .clearRowWork) (.row (.chosen 3), none)
        (Sum.elim
          (Function.update
            (MatrixWeightedRowController.afterCut3 S y
              d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
              d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃)
            54 (List.replicate
              ((y-d.rowBoundary₁-d.rowBoundary₂-d.rowBoundary₃) /
                d.rowDivisor₃) true)) extra) := by
  have hr := MatrixWeightedRowController.auxiliary_controller_run S y
    d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ haux
  rw [hframe] at hr
  exact row_phase S _ extra 3 _ hr

def afterRowClear (S : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update S (.inl 23) []) (.inl 63) []

theorem clear_row_work_run (v : State) (S : Stack → List Bool) :
    run ((S (.inl 23)).length + (S (.inl 63)).length + 2)
      (cfg (some .clearRowWork) (v, none) S) =
      cfg (some .afterRow) (v, none) (afterRowClear S) := by
  have h23 := BitMachineClearBank.clear_one_run program
    (.inl 23) .clearRowWork .clearRowOne (by rfl) v S
  let S₁ := Function.update S (.inl 23) []
  have h63 := BitMachineClearBank.clear_one_run program
    (.inl 63) .clearRowOne .afterRow (by rfl) v S₁
  have hlen : (S₁ (.inl 63)).length = (S (.inl 63)).length := by
    simp [S₁]
  rw [← hlen]
  rw [show (S (.inl 23)).length + (S₁ (.inl 63)).length + 2 =
    ((S (.inl 23)).length + 1) + ((S₁ (.inl 63)).length + 1) by omega]
  exact (run_add h23 _).trans h63

theorem direct_row_run (S : Stack → List Bool) (g : Fin 4) (n : ℕ)
    (hg : g.val < 2)
    (hlabel : S (.inl 54) = List.replicate n true)
    (hraw : S (.inl 25) = []) (hscratch : S (.inl 14) = []) :
    ∃ t ≤ 2*n + 4,
      run t (cfg (some .afterRow) (.row (.chosen g), none) S) =
      cfg (some .lookupInit) (.copy none, none)
        (Function.update S (.inl 25) (List.replicate n true)) := by
  obtain ⟨tc, htc, hc⟩ := copy_stage directSlots Label.direct
    .lookupInit (by intro l; rfl) S (.inl 54) (.inl 25) n
    ⟨rfl,rfl⟩ hlabel hraw (by simpa [directSlots] using hscratch)
  have hdispatch : advance program
      (cfg (some .afterRow) (.row (.chosen g), none) S) =
      cfg (some .directInit) (.row (.chosen g), none) S := by
    have hh : decide (g.val ≤ 1) = true := by simp; omega
    simp [advance, TM2.step, TM2.stepAux, program, chosenGroup, hh, cfg]
  have hinit : advance program
      (cfg (some .directInit) (.row (.chosen g), none) S) =
      cfg (some (.direct .scan)) (.copy none, none) S := rfl
  have htwo : run 2
      (cfg (some .afterRow) (.row (.chosen g), none) S) =
      cfg (some (.direct .scan)) (.copy none, none) S := by
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero, id_eq]
    rw [hdispatch, hinit]
  exact ⟨2+tc, by omega, (run_add htwo tc).trans hc⟩

theorem order_stage (S : Stack → List Bool) (aux : Bool)
    (localIn localOut : MatrixWeightedRowOrderMachine.Stack → List Bool)
    (v : MatrixWeightedRowOrderMachine.State) (bound : ℕ)
    (hinput : ∀ k, localIn k = S (orderSlots k))
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowOrderMachine.run t
        (⟨some (MatrixWeightedRowOrderMachine.start aux),
          MatrixWeightedRowOrderMachine.initial, localIn⟩ :
          MatrixWeightedRowOrderMachine.Config) =
        (⟨none,v,localOut⟩ : MatrixWeightedRowOrderMachine.Config)) :
    ∃ t ≤ bound,
      run t
        (cfg (some (.order (MatrixWeightedRowOrderMachine.start aux)))
          (.order MatrixWeightedRowOrderMachine.initial, none) S) =
      cfg (some .lookupInit) (.order v, none)
        (BitMachineStackEmbedding.bank orderSlots S localOut) := by
  obtain ⟨tOrder, hto, ho⟩ := hrun
  let lc : MatrixWeightedRowOrderMachine.Config :=
    ⟨some (MatrixWeightedRowOrderMachine.start aux),
      MatrixWeightedRowOrderMachine.initial, localIn⟩
  have hhalt : (((advance MatrixWeightedRowOrderMachine.program)^[tOrder]) lc).l = none := by
    change (MatrixWeightedRowOrderMachine.run tOrder lc).l = none
    rw [ho]
  obtain ⟨t, ht, he⟩ := outputs orderSlots S Label.order
    (fun z => (.order z, none)) getOrder (by intro z; rfl)
    (some .lookupInit) MatrixWeightedRowOrderMachine.program program
    (by intro l; rfl) lc tOrder hhalt
  have ho' : ((advance MatrixWeightedRowOrderMachine.program)^[tOrder]) lc =
      (⟨none,v,localOut⟩ : MatrixWeightedRowOrderMachine.Config) := ho
  rw [ho'] at he
  have hinit : BitMachineStackEmbedding.bank orderSlots S localIn = S :=
    bank_eq_self orderSlots S localIn hinput
  have hinit' : BitMachineStackEmbedding.bank orderSlots S lc.stk = S := hinit
  exact ⟨t, ht.trans hto, by
    simpa only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      hinit', cfg, run] using he⟩

def orderBound {nv nb : ℕ} (order : Construction.ItemOrder nv nb)
    (j : Fin (nv + nb)) (label width sL : ℕ) (aux : Bool) : ℕ :=
  10 * label + 3 * width + 7 +
  (if aux then 2 * nv + 4 else 1) +
  MatrixAddressMachine.exactTime (label / width) 1
    (if aux then nv else 0) + 1 +
  (2 * (MatrixWeightedRowOrderLookup.orderWord order).length +
    2 * j.val + 3) + 1 +
  (2 * sL + 2) + 1 +
  MatrixAddressMachine.exactTime (order j).val width (label % width)

theorem order_actual_stage {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb))
    (label width sL : ℕ) (aux : Bool) (hw : 0 < width)
    (hj : j.val = label / width + (if aux then nv else 0))
    (S : Stack → List Bool)
    (hinput : ∀ k,
      MatrixWeightedRowOrderMachineRun.inputBank label width nv sL
        (MatrixWeightedRowOrderLookup.orderWord order) [] k = S (orderSlots k)) :
    ∃ t ≤ orderBound order j label width sL aux,
      run t
        (cfg (some (.order (MatrixWeightedRowOrderMachine.start aux)))
          (.order MatrixWeightedRowOrderMachine.initial, none) S) =
      cfg (some .lookupInit) (.order (.address false), none)
        (BitMachineStackEmbedding.bank orderSlots S
          (MatrixWeightedRowOrderMachineRun.terminalBank label width nv sL
            (MatrixWeightedRowOrderLookup.orderWord order) []
            aux j.val (order j).val)) := by
  have hr := MatrixWeightedRowOrderMachineRun.run order j label width sL
    aux hw hj []
  simpa only [orderBound] using order_stage S aux
    (MatrixWeightedRowOrderMachineRun.inputBank label width nv sL
      (MatrixWeightedRowOrderLookup.orderWord order) [])
    (MatrixWeightedRowOrderMachineRun.terminalBank label width nv sL
      (MatrixWeightedRowOrderLookup.orderWord order) []
      aux j.val (order j).val)
    (.address false) (orderBound order j label width sL aux) hinput hr

theorem vertex_order_frame_full (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (x y : ℕ) (k : MatrixWeightedRowOrderMachine.Stack) :
    MatrixWeightedRowOrderMachineRun.inputBank
      (vertexLabel d y) d.rx d.nv d.stagePrefixRows
      (MatrixWeightedRowOrderLookup.orderWord order) [] k =
    afterRowClear
      (Sum.elim (vertexRowResult d (fullCore d x y) y)
        (writerExtra x y [])) (orderSlots k) := by
  rw [← horder]
  fin_cases k <;> rfl

theorem auxiliary_order_frame_full (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (x y : ℕ) (k : MatrixWeightedRowOrderMachine.Stack) :
    MatrixWeightedRowOrderMachineRun.inputBank
      (auxiliaryLabel d y) d.rx d.nv d.stagePrefixRows
      (MatrixWeightedRowOrderLookup.orderWord order) [] k =
    afterRowClear
      (Sum.elim (auxiliaryRowResult d (fullCore d x y) y)
        (writerExtra x y [])) (orderSlots k) := by
  rw [← horder]
  fin_cases k <;> rfl

theorem vertex_order_frame_diagonal (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (x y : ℕ) (k : MatrixWeightedRowOrderMachine.Stack) :
    MatrixWeightedRowOrderMachineRun.inputBank
      (vertexLabel d y) d.rx d.nv d.stagePrefixRows
      (MatrixWeightedRowOrderLookup.orderWord order) [] k =
    afterRowClear
      (Sum.elim (vertexRowResult d (diagonalCore d x y) y)
        (writerExtra x y [])) (orderSlots k) := by
  rw [← horder]
  fin_cases k <;> rfl

theorem auxiliary_order_frame_diagonal (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (x y : ℕ) (k : MatrixWeightedRowOrderMachine.Stack) :
    MatrixWeightedRowOrderMachineRun.inputBank
      (auxiliaryLabel d y) d.rx d.nv d.stagePrefixRows
      (MatrixWeightedRowOrderLookup.orderWord order) [] k =
    afterRowClear
      (Sum.elim (auxiliaryRowResult d (diagonalCore d x y) y)
        (writerExtra x y [])) (orderSlots k) := by
  rw [← horder]
  fin_cases k <;> rfl

theorem order_phase {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb))
    (label width sL : ℕ) (g : Fin 4) (aux : Bool)
    (hg : 2 ≤ g.val) (haux : aux = (g == 3))
    (hw : 0 < width)
    (hj : j.val = label / width + (if aux then nv else 0))
    (S : Stack → List Bool)
    (hinput : ∀ k,
      MatrixWeightedRowOrderMachineRun.inputBank label width nv sL
        (MatrixWeightedRowOrderLookup.orderWord order) [] k = S (orderSlots k)) :
    ∃ t ≤ orderBound order j label width sL aux + 2,
      run t (cfg (some .afterRow) (.row (.chosen g), none) S) =
      cfg (some .lookupInit) (.order (.address false), none)
        (BitMachineStackEmbedding.bank orderSlots S
          (MatrixWeightedRowOrderMachineRun.terminalBank label width nv sL
            (MatrixWeightedRowOrderLookup.orderWord order) []
            aux j.val (order j).val)) := by
  obtain ⟨to', hto', ho'⟩ := order_actual_stage order j label width sL
    aux hw hj S hinput
  have hdispatch : advance program
      (cfg (some .afterRow) (.row (.chosen g), none) S) =
      cfg (some (.orderInit aux)) (.row (.chosen g), none) S := by
    have hsmall : decide (g.val ≤ 1) = false := by
      simp
      omega
    simp [advance, TM2.step, TM2.stepAux, program,
      chosenGroup, hsmall, haux, cfg]
  have hinit : advance program
      (cfg (some (.orderInit aux)) (.row (.chosen g), none) S) =
      cfg (some (.order (MatrixWeightedRowOrderMachine.start aux)))
        (.order MatrixWeightedRowOrderMachine.initial, none) S := rfl
  have htwo : run 2 (cfg (some .afterRow) (.row (.chosen g), none) S) =
      cfg (some (.order (MatrixWeightedRowOrderMachine.start aux)))
        (.order MatrixWeightedRowOrderMachine.initial, none) S := by
    simp only [run, Function.iterate_succ_apply, Function.iterate_zero, id_eq]
    rw [hdispatch, hinit]
  exact ⟨2+to', by omega, (run_add htwo to').trans ho'⟩

def fullFullRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (fullRowResult d (fullCore d x y) y) (writerExtra x y [])

def fullFullPreLookup (d : Input) (x y : ℕ) : Stack → List Bool :=
  Function.update (afterRowClear (fullFullRowBank d x y))
    (.inl 25) (List.replicate (fullLabel d y) true)

theorem fullFull_lookup_frame (d : Input) (x y : ℕ) :
    let S := fullFullPreLookup d x y
    S (lookupSlots 0) = List.replicate (fullLabel d y) true ∧
    S (lookupSlots 1) = List.replicate d.rawWidth true ∧
    S (lookupSlots 2) =
      List.replicate ((x / d.uniform) / d.fullDivisor) true ∧
    S (lookupSlots 6) = d.rawBits ∧
    S (lookupSlots 7) = [] ∧
    (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro k hk0 hk1 hk2 hk6 hk7
  fin_cases k <;> simp_all [lookupSlots] <;> rfl

theorem lookup_stage (S : Stack → List Bool) (row width col : ℕ)
    (source out : List Bool)
    (hrow : S (lookupSlots 0) = List.replicate row true)
    (hwidth : S (lookupSlots 1) = List.replicate width true)
    (hcol : S (lookupSlots 2) = List.replicate col true)
    (hsource : S (lookupSlots 6) = source)
    (hout : S (lookupSlots 7) = out)
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) :
    ∃ t ≤ 32*(row+width+col+source.length+1)^2,
      run t (cfg (some (.lookup MatrixTableLookup.start))
        (.lookup MatrixTableLookup.initial, none) S) =
      cfg (some (.clear 0)) (.lookup MatrixTableLookup.initial, none)
        (Function.update S (.inr 2)
          (source[row*width+col]?.getD false::out)) := by
  let c := MatrixTableLookup.cfg (some MatrixTableLookup.start)
    MatrixTableLookup.initial (List.replicate row true)
    (List.replicate width true) (List.replicate col true) [] source out
  obtain ⟨tl, htl, hl⟩ :=
    MatrixTableLookup.lookup_run row width col source out
  have hhalt : (((advance MatrixTableLookup.program)^[tl]) c).l = none := by
    change (MatrixTableLookup.run tl c).l = none
    rw [hl]
    rfl
  obtain ⟨t, ht, he⟩ := outputs lookupSlots S Label.lookup
    (fun v => (.lookup v, none)) getLookup (by intro v; rfl)
    (some (.clear 0)) MatrixTableLookup.program program
    (by intro l; rfl) c tl hhalt
  have hl' : ((advance MatrixTableLookup.program)^[tl]) c =
      MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate row true) (List.replicate width true)
        (List.replicate col true) [] source
        (source[row*width+col]?.getD false::out) := hl
  rw [hl'] at he
  have hinit : BitMachineStackEmbedding.bank lookupSlots S c.stk = S := by
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [c, MatrixTableLookup.cfg, hrow, hwidth,
      hcol, hsource, hout, hwork]
  have hfinal : BitMachineStackEmbedding.bank lookupSlots S
      (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate row true) (List.replicate width true)
        (List.replicate col true) [] source
        (source[row*width+col]?.getD false::out)).stk =
      Function.update S (.inr 2)
        (source[row*width+col]?.getD false::out) := by
    have hu : (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate row true) (List.replicate width true)
        (List.replicate col true) [] source
        (source[row*width+col]?.getD false::out)).stk =
        Function.update c.stk 7
          (source[row*width+col]?.getD false::out) := by
      funext k
      fin_cases k <;> rfl
    rw [hu, bank_update, hinit]
    rfl
  exact ⟨t, ht.trans htl, by
    simpa only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      hinit, hfinal, cfg, run] using he⟩

theorem lookup_phase (v : State) (S : Stack → List Bool)
    (row width col : ℕ) (source out : List Bool)
    (hrow : S (lookupSlots 0) = List.replicate row true)
    (hwidth : S (lookupSlots 1) = List.replicate width true)
    (hcol : S (lookupSlots 2) = List.replicate col true)
    (hsource : S (lookupSlots 6) = source)
    (hout : S (lookupSlots 7) = out)
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) :
    ∃ t ≤ 32*(row+width+col+source.length+1)^2 + 1,
      run t (cfg (some .lookupInit) (v,none) S) =
      cfg (some (.clear 0)) (.lookup MatrixTableLookup.initial, none)
        (Function.update S (.inr 2)
          (source[row*width+col]?.getD false::out)) := by
  obtain ⟨t, ht, he⟩ := lookup_stage S row width col source out
    hrow hwidth hcol hsource hout hwork
  have hinit : advance program (cfg (some .lookupInit) (v,none) S) =
      cfg (some (.lookup MatrixTableLookup.start))
        (.lookup MatrixTableLookup.initial, none) S := rfl
  refine ⟨t+1, by omega, ?_⟩
  rw [run_succ hinit t]
  exact he

/-- The complete physical path for a full column and a full-row support.
The remaining seven support pairs use the same entry program. -/
theorem full_full_to_lookup (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (hrow : y < d.rowBoundary₁) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.copy none, none)
        (fullFullPreLookup d x y) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁⟩ := column_full_run d x y [] hcolumn
  have hdispatch : run 1
      (cfg (some .afterColumn) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y []) := rfl
  have hr := MatrixWeightedRowController.full_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ hrow
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  obtain ⟨t₂, -, h₂⟩ := row_phase_from (fullCore d x y)
    (fullRowResult d (fullCore d x y) y) (writerExtra x y [])
    (.column (.terminal false)) 0 _ hr
  have hrow' : run t₂
      (cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .clearRowWork) (.row (.chosen 0), none)
        (fullFullRowBank d x y) := by
    simpa only [afterFullColumn, fullCore, fullFullRowBank,
      fullRowResult] using h₂
  have hclear := clear_row_work_run (.row (.chosen 0))
    (fullFullRowBank d x y)
  have hdirect := direct_row_run
    (afterRowClear (fullFullRowBank d x y)) 0 (fullLabel d y)
    (by decide) (by rfl) (by rfl) (by rfl)
  obtain ⟨t₃, -, h₃⟩ := hdirect
  refine ⟨t₀ + t₁ + 1 + t₂ +
    ((fullFullRowBank d x y (.inl 23)).length +
      (fullFullRowBank d x y (.inl 63)).length + 2) + t₃, ?_⟩
  have h01 := (run_add h₀ (t₁ + 1 + t₂ +
    ((fullFullRowBank d x y (.inl 23)).length +
      (fullFullRowBank d x y (.inl 63)).length + 2) + t₃))
  simp only [Nat.add_assoc] at h01 ⊢
  rw [h01]
  have h12 := (run_add h₁ (1 + t₂ +
    ((fullFullRowBank d x y (.inl 23)).length +
      (fullFullRowBank d x y (.inl 63)).length + 2) + t₃))
  simp only [Nat.add_assoc] at h12
  rw [h12]
  rw [run_add hdispatch]
  rw [run_add hrow']
  simp only [← Nat.add_assoc]
  rw [run_add hclear]
  exact h₃

theorem fullFull_stable (d : Input) (x y : ℕ)
    (k : Stack) (hk : ∀ i : Fin 41, workSlot i ≠ k) :
    fullFullPreLookup d x y k = cellBank d x y [] k := by
  have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
    rintro ⟨i, hi⟩
    exact hk i hi
  cases k with
  | inl k =>
      fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
  | inr k => fin_cases k <;> rfl

/-- Shared charged suffix from any physically prepared address bank. The
premises concern concrete stack contents and persistence, not a free entry
evaluator; the lookup and cleanup are executed by this program. -/
theorem lookup_and_clear (d : Input) (x y row col : ℕ)
    (v : State) (S : Stack → List Bool)
    (hrow : S (lookupSlots 0) = List.replicate row true)
    (hwidth : S (lookupSlots 1) = List.replicate d.rawWidth true)
    (hcol : S (lookupSlots 2) = List.replicate col true)
    (hsource : S (lookupSlots 6) = d.rawBits)
    (hout : S (lookupSlots 7) = [])
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = [])
    (hstable : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      S k = cellBank d x y [] k) :
    ∃ t, run t (cfg (some .lookupInit) (v,none) S) =
      cfg none initial
        (cellBank d x y [d.rawBits[row*d.rawWidth+col]?.getD false]) := by
  obtain ⟨tl, -, hl⟩ := lookup_phase v S row d.rawWidth col d.rawBits []
    hrow hwidth hcol hsource hout hwork
  let bit := d.rawBits[row*d.rawWidth+col]?.getD false
  let S' := Function.update S (.inr 2) [bit]
  have hc := clear_run (.lookup MatrixTableLookup.initial) S'
  have hs : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      S' k = cellBank d x y [bit] k := by
    intro k hk
    by_cases heq : k = .inr 2
    · subst k
      rfl
    · simp only [S', Function.update_of_ne heq]
      rw [hstable k hk]
      cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> simp_all [cellBank]
  have hf : BitMachineClearBank.cleared workSlot S' =
      cellBank d x y [bit] :=
    cleared_to_cellBank d x y [bit] S' hs
  refine ⟨tl + ((∑ i, (S' (workSlot i)).length)+43), ?_⟩
  rw [run_add hl, hc, hf]

/-- A reusable uninterrupted row-branch path for the two direct supports.
The caller supplies a checked row-controller execution; the label transfer
and work cleanup are still performed physically here. -/
theorem direct_row_to_lookup (S T : Fin 64 → List Bool)
    (extra : Fin 3 → List Bool) (v : State) (g : Fin 4)
    (n bound : ℕ) (hg : g.val < 2)
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T)
    (hlabel : T 54 = List.replicate n true)
    (hraw : T 25 = []) (hscratch : T 14 = []) :
    ∃ t, run t (cfg (some .rowInit) (v,none) (Sum.elim S extra)) =
      cfg (some .lookupInit) (.copy none, none)
        (Function.update (afterRowClear (Sum.elim T extra))
          (.inl 25) (List.replicate n true)) := by
  obtain ⟨tr, -, hr⟩ := row_phase_from S T extra v g bound hrun
  let B := Sum.elim T extra
  have hc := clear_row_work_run (.row (.chosen g)) B
  obtain ⟨td, -, hd⟩ := direct_row_run (afterRowClear B) g n hg
    (by simpa only [afterRowClear, B] using hlabel)
    (by simpa only [afterRowClear, B] using hraw)
    (by simpa only [afterRowClear, B] using hscratch)
  refine ⟨tr + ((B (.inl 23)).length + (B (.inl 63)).length + 2) + td, ?_⟩
  rw [show tr + ((B (.inl 23)).length + (B (.inl 63)).length + 2) + td =
      tr + (((B (.inl 23)).length + (B (.inl 63)).length + 2) + td) by omega]
  rw [run_add hr, run_add hc]
  exact hd

/-- The corresponding uninterrupted path through the physical serialized
item-order lookup for the vertex and auxiliary supports. -/
theorem ordered_row_to_lookup {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv+nb))
    (S T : Fin 64 → List Bool) (extra : Fin 3 → List Bool)
    (v : State) (g : Fin 4) (aux : Bool)
    (label width sL bound : ℕ)
    (hg : 2 ≤ g.val) (haux : aux = (g == 3))
    (hw : 0 < width)
    (hj : j.val = label / width + (if aux then nv else 0))
    (hrun : ∃ t ≤ bound,
      MatrixWeightedRowController.run t
        (MatrixWeightedRowController.cfg
          (some MatrixWeightedRowController.start)
          MatrixWeightedRowController.initial S) =
      MatrixWeightedRowController.cfg none (.chosen g) T)
    (hinput : ∀ k,
      MatrixWeightedRowOrderMachineRun.inputBank label width nv sL
        (MatrixWeightedRowOrderLookup.orderWord order) [] k =
      afterRowClear (Sum.elim T extra) (orderSlots k)) :
    ∃ t, run t (cfg (some .rowInit) (v,none) (Sum.elim S extra)) =
      cfg (some .lookupInit) (.order (.address false), none)
        (BitMachineStackEmbedding.bank orderSlots
          (afterRowClear (Sum.elim T extra))
          (MatrixWeightedRowOrderMachineRun.terminalBank label width nv sL
            (MatrixWeightedRowOrderLookup.orderWord order) []
            aux j.val (order j).val)) := by
  obtain ⟨tr, -, hr⟩ := row_phase_from S T extra v g bound hrun
  let B := Sum.elim T extra
  have hc := clear_row_work_run (.row (.chosen g)) B
  obtain ⟨torder, -, ho⟩ := order_phase order j label width sL g aux
    hg haux hw hj (afterRowClear B) hinput
  refine ⟨tr + ((B (.inl 23)).length + (B (.inl 63)).length + 2) + torder, ?_⟩
  rw [show tr + ((B (.inl 23)).length + (B (.inl 63)).length + 2) + torder =
      tr + (((B (.inl 23)).length + (B (.inl 63)).length + 2) + torder) by omega]
  rw [run_add hr, run_add hc]
  exact ho

def fullTemplateRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (templateRowResult d (fullCore d x y) y) (writerExtra x y [])

def fullTemplatePreLookup (d : Input) (x y : ℕ) : Stack → List Bool :=
  Function.update (afterRowClear (fullTemplateRowBank d x y))
    (.inl 25) (List.replicate (templateLabel d y) true)

theorem full_template_to_lookup (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y - d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.copy none, none)
        (fullTemplatePreLookup d x y) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁'⟩ := column_full_run d x y [] hcolumn
  have hdispatch : run 1
      (cfg (some .afterColumn) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y []) := rfl
  have hr := MatrixWeightedRowController.template_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ htemplate
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  obtain ⟨t₂, h₂⟩ := direct_row_to_lookup (fullCore d x y)
    (templateRowResult d (fullCore d x y) y) (writerExtra x y [])
    (.column (.terminal false)) 1 (templateLabel d y) _ (by decide) hr
    (by rfl) (by rfl) (by rfl)
  have h₂' : run t₂
      (cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .lookupInit) (.copy none, none)
        (fullTemplatePreLookup d x y) := by
    simpa only [afterFullColumn, fullCore, fullTemplatePreLookup,
      fullTemplateRowBank] using h₂
  refine ⟨t₀+(t₁+(1+t₂)), ?_⟩
  rw [run_add h₀, run_add h₁', run_add hdispatch]
  exact h₂'

theorem fullTemplate_lookup_frame (d : Input) (x y : ℕ) :
    let S := fullTemplatePreLookup d x y
    S (lookupSlots 0) = List.replicate (templateLabel d y) true ∧
    S (lookupSlots 1) = List.replicate d.rawWidth true ∧
    S (lookupSlots 2) =
      List.replicate ((x / d.uniform) / d.fullDivisor) true ∧
    S (lookupSlots 6) = d.rawBits ∧
    S (lookupSlots 7) = [] ∧
    (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro k hk0 hk1 hk2 hk6 hk7
  fin_cases k <;> simp_all [lookupSlots] <;> rfl

theorem fullTemplate_stable (d : Input) (x y : ℕ)
    (k : Stack) (hk : ∀ i : Fin 41, workSlot i ≠ k) :
    fullTemplatePreLookup d x y k = cellBank d x y [] k := by
  have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
    rintro ⟨i, hi⟩
    exact hk i hi
  cases k with
  | inl k =>
      fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
  | inr k => fin_cases k <;> rfl

theorem full_template_run (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y - d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[templateLabel d y*d.rawWidth+
            ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  obtain ⟨tp, hp⟩ := full_template_to_lookup d x y
    hcolumn h₁ htemplate
  obtain ⟨hr, hw, hc, hs, ho, hwork⟩ :=
    fullTemplate_lookup_frame d x y
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y (templateLabel d y)
    ((x/d.uniform)/d.fullDivisor) (.copy none)
    (fullTemplatePreLookup d x y) hr hw hc hs ho hwork
    (fullTemplate_stable d x y)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

def diagonalFullRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (fullRowResult d (diagonalCore d x y) y) (writerExtra x y [])

def diagonalFullPreLookup (d : Input) (x y : ℕ) : Stack → List Bool :=
  Function.update (afterRowClear (diagonalFullRowBank d x y))
    (.inl 25) (List.replicate (fullLabel d y) true)

theorem diagonal_full_to_lookup (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (hrow : y < d.rowBoundary₁) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.copy none, none)
        (diagonalFullPreLookup d x y) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁⟩ := column_diagonal_run d x y [] hcolumn
  obtain ⟨t₂, -, h₂⟩ := diagonal_arithmetic_phase d x y []
  have hr := MatrixWeightedRowController.full_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃ hrow
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  obtain ⟨t₃, h₃⟩ := direct_row_to_lookup (diagonalCore d x y)
    (fullRowResult d (diagonalCore d x y) y) (writerExtra x y [])
    (.diagonal .idle) 0 (fullLabel d y) _ (by decide) hr
    (by rfl) (by rfl) (by rfl)
  have h₂' : run t₂
      (cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y [])) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y [])) := by
    have hu : Function.update (afterDiagonalColumn d x y [])
        (.inl 19)
        (List.replicate
          (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
            d.wordBase d.cy d.s d.binBase) true) =
        Sum.elim (diagonalCore d x y) (writerExtra x y []) := by
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    rw [hu] at h₂
    exact h₂
  have h₃' : run t₃
      (cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y []))) =
      cfg (some .lookupInit) (.copy none, none)
        (diagonalFullPreLookup d x y) := by
    simpa only [diagonalFullPreLookup,
      diagonalFullRowBank] using h₃
  refine ⟨t₀+(t₁+(t₂+t₃)), ?_⟩
  rw [run_add h₀, run_add h₁, run_add h₂']
  exact h₃'

theorem diagonalFull_lookup_frame (d : Input) (x y : ℕ) :
    let S := diagonalFullPreLookup d x y
    S (lookupSlots 0) = List.replicate (fullLabel d y) true ∧
    S (lookupSlots 1) = List.replicate d.rawWidth true ∧
    S (lookupSlots 2) =
      List.replicate
        (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
          d.wordBase d.cy d.s d.binBase) true ∧
    S (lookupSlots 6) = d.rawBits ∧
    S (lookupSlots 7) = [] ∧
    (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro k hk0 hk1 hk2 hk6 hk7
  fin_cases k <;> simp_all [lookupSlots] <;> rfl

theorem diagonalFull_stable (d : Input) (x y : ℕ)
    (k : Stack) (hk : ∀ i : Fin 41, workSlot i ≠ k) :
    diagonalFullPreLookup d x y k = cellBank d x y [] k := by
  have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
    rintro ⟨i, hi⟩
    exact hk i hi
  cases k with
  | inl k =>
      fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
  | inr k => fin_cases k <;> rfl

theorem diagonal_full_run (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (hrow : y < d.rowBoundary₁) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[fullLabel d y*d.rawWidth+
            MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
              d.wordBase d.cy d.s d.binBase]?.getD false]) := by
  obtain ⟨tp, hp⟩ := diagonal_full_to_lookup d x y hcolumn hrow
  obtain ⟨hr, hw, hc, hs, ho, hwork⟩ :=
    diagonalFull_lookup_frame d x y
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y (fullLabel d y)
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) (.copy none)
    (diagonalFullPreLookup d x y) hr hw hc hs ho hwork
    (diagonalFull_stable d x y)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

def diagonalTemplateRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (templateRowResult d (diagonalCore d x y) y) (writerExtra x y [])

def diagonalTemplatePreLookup (d : Input) (x y : ℕ) : Stack → List Bool :=
  Function.update (afterRowClear (diagonalTemplateRowBank d x y))
    (.inl 25) (List.replicate (templateLabel d y) true)

theorem diagonal_template_to_lookup (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y - d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.copy none, none)
        (diagonalTemplatePreLookup d x y) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁'⟩ := column_diagonal_run d x y [] hcolumn
  obtain ⟨t₂, -, h₂⟩ := diagonal_arithmetic_phase d x y []
  have hr := MatrixWeightedRowController.template_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ htemplate
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  obtain ⟨t₃, h₃⟩ := direct_row_to_lookup (diagonalCore d x y)
    (templateRowResult d (diagonalCore d x y) y) (writerExtra x y [])
    (.diagonal .idle) 1 (templateLabel d y) _ (by decide) hr
    (by rfl) (by rfl) (by rfl)
  have h₂' : run t₂
      (cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y [])) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y [])) := by
    have hu : Function.update (afterDiagonalColumn d x y [])
        (.inl 19)
        (List.replicate
          (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
            d.wordBase d.cy d.s d.binBase) true) =
        Sum.elim (diagonalCore d x y) (writerExtra x y []) := by
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    rw [hu] at h₂
    exact h₂
  have h₃' : run t₃
      (cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y []))) =
      cfg (some .lookupInit) (.copy none, none)
        (diagonalTemplatePreLookup d x y) := by
    simpa only [diagonalTemplatePreLookup,
      diagonalTemplateRowBank] using h₃
  refine ⟨t₀+(t₁+(t₂+t₃)), ?_⟩
  rw [run_add h₀, run_add h₁', run_add h₂']
  exact h₃'

theorem diagonalTemplate_lookup_frame (d : Input) (x y : ℕ) :
    let S := diagonalTemplatePreLookup d x y
    S (lookupSlots 0) = List.replicate (templateLabel d y) true ∧
    S (lookupSlots 1) = List.replicate d.rawWidth true ∧
    S (lookupSlots 2) =
      List.replicate
        (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
          d.wordBase d.cy d.s d.binBase) true ∧
    S (lookupSlots 6) = d.rawBits ∧
    S (lookupSlots 7) = [] ∧
    (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro k hk0 hk1 hk2 hk6 hk7
  fin_cases k <;> simp_all [lookupSlots] <;> rfl

theorem diagonalTemplate_stable (d : Input) (x y : ℕ)
    (k : Stack) (hk : ∀ i : Fin 41, workSlot i ≠ k) :
    diagonalTemplatePreLookup d x y k = cellBank d x y [] k := by
  have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
    rintro ⟨i, hi⟩
    exact hk i hi
  cases k with
  | inl k =>
      fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
  | inr k => fin_cases k <;> rfl

theorem diagonal_template_run (d : Input) (x y : ℕ)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (htemplate : y - d.rowBoundary₁ < d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[templateLabel d y*d.rawWidth+
            MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
              d.wordBase d.cy d.s d.binBase]?.getD false]) := by
  obtain ⟨tp, hp⟩ := diagonal_template_to_lookup d x y
    hcolumn h₁ htemplate
  obtain ⟨hr, hw, hc, hs, ho, hwork⟩ :=
    diagonalTemplate_lookup_frame d x y
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y (templateLabel d y)
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) (.copy none)
    (diagonalTemplatePreLookup d x y) hr hw hc hs ho hwork
    (diagonalTemplate_stable d x y)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

def fullVertexRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (vertexRowResult d (fullCore d x y) y) (writerExtra x y [])

noncomputable def fullVertexPreLookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : Stack → List Bool :=
  BitMachineStackEmbedding.bank orderSlots
    (afterRowClear (fullVertexRowBank d x y))
    (MatrixWeightedRowOrderMachineRun.terminalBank
      (vertexLabel d y) d.rx d.nv d.stagePrefixRows
      (MatrixWeightedRowOrderLookup.orderWord order) []
      false j.val (order j).val)

theorem full_vertex_to_lookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.order (.address false), none)
        (fullVertexPreLookup d x y order j) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁'⟩ := column_full_run d x y [] hcolumn
  have hdispatch : run 1
      (cfg (some .afterColumn) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y []) := rfl
  have hr := MatrixWeightedRowController.vertex_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ hvertex
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  have hinput := vertex_order_frame_full d order horder x y
  obtain ⟨t₂, h₂'⟩ := ordered_row_to_lookup order j
    (fullCore d x y) (vertexRowResult d (fullCore d x y) y)
    (writerExtra x y []) (.column (.terminal false)) 2 false
    (vertexLabel d y) d.rx d.stagePrefixRows _
    (by decide) (by rfl) hwidth (by simpa using hj) hr hinput
  have h₂'' : run t₂
      (cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .lookupInit) (.order (.address false), none)
        (fullVertexPreLookup d x y order j) := by
    simpa only [afterFullColumn, fullCore,
      fullVertexPreLookup, fullVertexRowBank] using h₂'
  refine ⟨t₀+(t₁+(1+t₂)), ?_⟩
  rw [run_add h₀, run_add h₁', run_add hdispatch]
  exact h₂''

theorem fullVertex_lookup_frame (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) :
    let S := fullVertexPreLookup d x y order j
    S (lookupSlots 0) =
      List.replicate
        (d.stagePrefixRows + (order j).val*d.rx +
          vertexLabel d y % d.rx) true ∧
    S (lookupSlots 1) = List.replicate d.rawWidth true ∧
    S (lookupSlots 2) =
      List.replicate ((x/d.uniform)/d.fullDivisor) true ∧
    S (lookupSlots 6) = d.rawBits ∧
    S (lookupSlots 7) = [] ∧
    (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change BitMachineStackEmbedding.bank orderSlots
      (afterRowClear (fullVertexRowBank d x y))
      (MatrixWeightedRowOrderMachineRun.terminalBank
        (vertexLabel d y) d.rx d.nv d.stagePrefixRows
        (MatrixWeightedRowOrderLookup.orderWord order) []
        false j.val (order j).val) (orderSlots 5) = _
    rw [bank_at]
    simp [MatrixWeightedRowOrderMachineRun.terminalBank]
  · unfold fullVertexPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 1) (by decide)]
    rfl
  · unfold fullVertexPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 2) (by decide)]
    rfl
  · unfold fullVertexPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 6) (by decide)]
    rfl
  · unfold fullVertexPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 7) (by decide)]
    rfl
  · intro k hk0 hk1 hk2 hk6 hk7
    unfold fullVertexPreLookup
    fin_cases k <;> simp_all [lookupSlots]
    all_goals rw [bank_outside orderSlots _ _ _ (by decide)]
    all_goals rfl

theorem fullVertex_stable (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (k : Stack) (hk : ∀ i : Fin 41, workSlot i ≠ k) :
    fullVertexPreLookup d x y order j k = cellBank d x y [] k := by
  have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
    rintro ⟨i, hi⟩
    exact hk i hi
  by_cases h : ∃ i : MatrixWeightedRowOrderMachine.Stack,
      orderSlots i = k
  · obtain ⟨i, rfl⟩ := h
    unfold fullVertexPreLookup
    fin_cases i <;> first
      | (exfalso; exact hnot (by decide))
      | (rw [bank_at]; rfl)
      | (rw [bank_at, ← horder]; rfl)
  · unfold fullVertexPreLookup
    rw [bank_outside orderSlots _ _ k h]
    cases k with
    | inl k =>
        fin_cases k <;> first
          | rfl
          | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl

theorem full_vertex_run (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
            vertexLabel d y%d.rx)*d.rawWidth+
            ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  obtain ⟨tp, hp⟩ := full_vertex_to_lookup d x y order j horder
    hwidth hj hcolumn h₁ h₂ hvertex
  obtain ⟨hr, hw, hc, hs, ho, hwork⟩ :=
    fullVertex_lookup_frame d x y order j
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y
    (d.stagePrefixRows + (order j).val*d.rx + vertexLabel d y%d.rx)
    ((x/d.uniform)/d.fullDivisor) (.order (.address false))
    (fullVertexPreLookup d x y order j) hr hw hc hs ho hwork
    (fullVertex_stable d x y order j horder)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

noncomputable def orderPreLookup (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) (label : ℕ) (aux : Bool)
    (B : Stack → List Bool) : Stack → List Bool :=
  BitMachineStackEmbedding.bank orderSlots B
    (MatrixWeightedRowOrderMachineRun.terminalBank label d.rx
      d.nv d.stagePrefixRows
      (MatrixWeightedRowOrderLookup.orderWord order) []
      aux j.val (order j).val)

theorem orderPreLookup_frame (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) (label : ℕ) (aux : Bool)
    (B : Stack → List Bool) (col : ℕ)
    (hwidth : B (lookupSlots 1) = List.replicate d.rawWidth true)
    (hcol : B (lookupSlots 2) = List.replicate col true)
    (hsource : B (lookupSlots 6) = d.rawBits)
    (hout : B (lookupSlots 7) = [])
    (hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = []) :
    let S := orderPreLookup d order j label aux B
    S (lookupSlots 0) =
      List.replicate
        (d.stagePrefixRows + (order j).val*d.rx + label % d.rx) true ∧
    S (lookupSlots 1) = List.replicate d.rawWidth true ∧
    S (lookupSlots 2) = List.replicate col true ∧
    S (lookupSlots 6) = d.rawBits ∧
    S (lookupSlots 7) = [] ∧
    (∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → S (lookupSlots k) = []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change BitMachineStackEmbedding.bank orderSlots B
      (MatrixWeightedRowOrderMachineRun.terminalBank label d.rx
        d.nv d.stagePrefixRows
        (MatrixWeightedRowOrderLookup.orderWord order) []
        aux j.val (order j).val) (orderSlots 5) = _
    rw [bank_at]
    simp [MatrixWeightedRowOrderMachineRun.terminalBank]
  · unfold orderPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 1) (by decide)]
    exact hwidth
  · unfold orderPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 2) (by decide)]
    exact hcol
  · unfold orderPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 6) (by decide)]
    exact hsource
  · unfold orderPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots 7) (by decide)]
    exact hout
  · intro k hk0 hk1 hk2 hk6 hk7
    unfold orderPreLookup
    rw [bank_outside orderSlots _ _ (lookupSlots k) (by
      fin_cases k <;> simp_all [lookupSlots] <;> decide)]
    exact hwork k hk0 hk1 hk2 hk6 hk7

theorem orderPreLookup_stable (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) (label : ℕ) (aux : Bool)
    (B : Stack → List Bool)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k)
    (k : Stack) (hk : ∀ i : Fin 41, workSlot i ≠ k) :
    orderPreLookup d order j label aux B k = cellBank d x y [] k := by
  have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
    rintro ⟨i, hi⟩
    exact hk i hi
  by_cases h : ∃ i : MatrixWeightedRowOrderMachine.Stack,
      orderSlots i = k
  · obtain ⟨i, rfl⟩ := h
    unfold orderPreLookup
    fin_cases i <;> first
      | (exfalso; exact hnot (by decide))
      | (rw [bank_at]; rfl)
      | (rw [bank_at, ← horder]; rfl)
  · unfold orderPreLookup
    rw [bank_outside orderSlots _ _ k h]
    exact hB k hk

def fullAuxiliaryRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (auxiliaryRowResult d (fullCore d x y) y) (writerExtra x y [])

noncomputable def fullAuxiliaryPreLookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : Stack → List Bool :=
  orderPreLookup d order j (auxiliaryLabel d y) true
    (afterRowClear (fullAuxiliaryRowBank d x y))

theorem full_auxiliary_to_lookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.order (.address false), none)
        (fullAuxiliaryPreLookup d x y order j) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁'⟩ := column_full_run d x y [] hcolumn
  have hdispatch : run 1
      (cfg (some .afterColumn) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y []) := rfl
  have hr := MatrixWeightedRowController.auxiliary_controller_run
    (fullCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ haux
  simp only [fullCore] at hr
  rw [full_row_seed_frame d x y []] at hr
  have hinput := auxiliary_order_frame_full d order horder x y
  obtain ⟨t₂, h₂'⟩ := ordered_row_to_lookup order j
    (fullCore d x y) (auxiliaryRowResult d (fullCore d x y) y)
    (writerExtra x y []) (.column (.terminal false)) 3 true
    (auxiliaryLabel d y) d.rx d.stagePrefixRows _
    (by decide) (by rfl) hwidth (by simpa using hj) hr hinput
  have h₂'' : run t₂
      (cfg (some .rowInit) (.column (.terminal false), none)
        (afterFullColumn d x y [])) =
      cfg (some .lookupInit) (.order (.address false), none)
        (fullAuxiliaryPreLookup d x y order j) := by
    simpa only [afterFullColumn, fullCore,
      fullAuxiliaryPreLookup, fullAuxiliaryRowBank,
      orderPreLookup] using h₂'
  refine ⟨t₀+(t₁+(1+t₂)), ?_⟩
  rw [run_add h₀, run_add h₁', run_add hdispatch]
  exact h₂''

theorem full_auxiliary_run (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
            auxiliaryLabel d y%d.rx)*d.rawWidth+
            ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  obtain ⟨tp, hp⟩ := full_auxiliary_to_lookup d x y order j horder
    hwidth hj hcolumn h₁ h₂ haux
  let B := afterRowClear (fullAuxiliaryRowBank d x y)
  have hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [] := by
    intro k hk0 hk1 hk2 hk6 hk7
    fin_cases k <;> simp_all [lookupSlots] <;> rfl
  obtain ⟨hr, hw, hc, hs, ho, hwork'⟩ := orderPreLookup_frame
    d order j (auxiliaryLabel d y) true B
    ((x/d.uniform)/d.fullDivisor)
    (by rfl) (by rfl) (by rfl) (by rfl) hwork
  have hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k := by
    intro k hk
    have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
      rintro ⟨i, hi⟩
      exact hk i hi
    cases k with
    | inl k =>
        fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y
    (d.stagePrefixRows + (order j).val*d.rx + auxiliaryLabel d y%d.rx)
    ((x/d.uniform)/d.fullDivisor) (.order (.address false))
    (fullAuxiliaryPreLookup d x y order j)
    hr hw hc hs ho hwork'
    (by intro k hk
        exact orderPreLookup_stable d x y order j
          (auxiliaryLabel d y) true B horder hB k hk)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

def diagonalVertexRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (vertexRowResult d (diagonalCore d x y) y) (writerExtra x y [])

noncomputable def diagonalVertexPreLookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : Stack → List Bool :=
  orderPreLookup d order j (vertexLabel d y) false
    (afterRowClear (diagonalVertexRowBank d x y))

theorem diagonal_vertex_to_lookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.order (.address false), none)
        (diagonalVertexPreLookup d x y order j) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁'⟩ := column_diagonal_run d x y [] hcolumn
  obtain ⟨t₂, -, h₂'⟩ := diagonal_arithmetic_phase d x y []
  have hr := MatrixWeightedRowController.vertex_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ hvertex
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  have hinput := vertex_order_frame_diagonal d order horder x y
  obtain ⟨t₃, h₃⟩ := ordered_row_to_lookup order j
    (diagonalCore d x y) (vertexRowResult d (diagonalCore d x y) y)
    (writerExtra x y []) (.diagonal .idle) 2 false
    (vertexLabel d y) d.rx d.stagePrefixRows _
    (by decide) (by rfl) hwidth (by simpa using hj) hr hinput
  have h₂'' : run t₂
      (cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y [])) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y [])) := by
    have hu : Function.update (afterDiagonalColumn d x y [])
        (.inl 19)
        (List.replicate
          (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
            d.wordBase d.cy d.s d.binBase) true) =
        Sum.elim (diagonalCore d x y) (writerExtra x y []) := by
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    rw [hu] at h₂'
    exact h₂'
  have h₃' : run t₃
      (cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y []))) =
      cfg (some .lookupInit) (.order (.address false), none)
        (diagonalVertexPreLookup d x y order j) := by
    simpa only [diagonalVertexPreLookup,
      diagonalVertexRowBank, orderPreLookup] using h₃
  refine ⟨t₀+(t₁+(t₂+t₃)), ?_⟩
  rw [run_add h₀, run_add h₁', run_add h₂'']
  exact h₃'

theorem diagonal_vertex_run (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = vertexLabel d y / d.rx)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (hvertex : y-d.rowBoundary₁-d.rowBoundary₂ < d.rowBoundary₃) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
            vertexLabel d y%d.rx)*d.rawWidth+
            MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
              d.wordBase d.cy d.s d.binBase]?.getD false]) := by
  obtain ⟨tp, hp⟩ := diagonal_vertex_to_lookup d x y order j horder
    hwidth hj hcolumn h₁ h₂ hvertex
  let B := afterRowClear (diagonalVertexRowBank d x y)
  have hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [] := by
    intro k hk0 hk1 hk2 hk6 hk7
    fin_cases k <;> simp_all [lookupSlots] <;> rfl
  obtain ⟨hr, hw, hc, hs, ho, hwork'⟩ := orderPreLookup_frame
    d order j (vertexLabel d y) false B
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase)
    (by rfl) (by rfl) (by rfl) (by rfl) hwork
  have hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k := by
    intro k hk
    have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
      rintro ⟨i, hi⟩
      exact hk i hi
    cases k with
    | inl k =>
        fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y
    (d.stagePrefixRows + (order j).val*d.rx + vertexLabel d y%d.rx)
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) (.order (.address false))
    (diagonalVertexPreLookup d x y order j)
    hr hw hc hs ho hwork'
    (by intro k hk
        exact orderPreLookup_stable d x y order j
          (vertexLabel d y) false B horder hB k hk)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

def diagonalAuxiliaryRowBank (d : Input) (x y : ℕ) : Stack → List Bool :=
  Sum.elim (auxiliaryRowResult d (diagonalCore d x y) y) (writerExtra x y [])

noncomputable def diagonalAuxiliaryPreLookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) : Stack → List Bool :=
  orderPreLookup d order j (auxiliaryLabel d y) true
    (afterRowClear (diagonalAuxiliaryRowBank d x y))

theorem diagonal_auxiliary_to_lookup (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg (some .lookupInit) (.order (.address false), none)
        (diagonalAuxiliaryPreLookup d x y order j) := by
  obtain ⟨t₀, -, h₀⟩ := copy_coordinates_run d x y []
  obtain ⟨t₁, -, h₁'⟩ := column_diagonal_run d x y [] hcolumn
  obtain ⟨t₂, -, h₂'⟩ := diagonal_arithmetic_phase d x y []
  have hr := MatrixWeightedRowController.auxiliary_controller_run
    (diagonalCore d x y) y d.rowBoundary₁ d.rowBoundary₂ d.rowBoundary₃
    d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂ d.rowDivisor₃
    h₁ h₂ haux
  simp only [diagonalCore] at hr
  rw [diagonal_row_seed_frame d x y
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) []] at hr
  have hinput := auxiliary_order_frame_diagonal d order horder x y
  obtain ⟨t₃, h₃⟩ := ordered_row_to_lookup order j
    (diagonalCore d x y) (auxiliaryRowResult d (diagonalCore d x y) y)
    (writerExtra x y []) (.diagonal .idle) 3 true
    (auxiliaryLabel d y) d.rx d.stagePrefixRows _
    (by decide) (by rfl) hwidth (by simpa using hj) hr hinput
  have h₂'' : run t₂
      (cfg (some .afterColumn) (.column (.terminal true), none)
        (afterDiagonalColumn d x y [])) =
      cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y [])) := by
    have hu : Function.update (afterDiagonalColumn d x y [])
        (.inl 19)
        (List.replicate
          (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
            d.wordBase d.cy d.s d.binBase) true) =
        Sum.elim (diagonalCore d x y) (writerExtra x y []) := by
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
    rw [hu] at h₂'
    exact h₂'
  have h₃' : run t₃
      (cfg (some .rowInit) (.diagonal .idle, none)
        (Sum.elim (diagonalCore d x y) (writerExtra x y []))) =
      cfg (some .lookupInit) (.order (.address false), none)
        (diagonalAuxiliaryPreLookup d x y order j) := by
    simpa only [diagonalAuxiliaryPreLookup,
      diagonalAuxiliaryRowBank, orderPreLookup] using h₃
  refine ⟨t₀+(t₁+(t₂+t₃)), ?_⟩
  rw [run_add h₀, run_add h₁', run_add h₂'']
  exact h₃'

theorem diagonal_auxiliary_run (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hwidth : 0 < d.rx)
    (hj : j.val = auxiliaryLabel d y / d.rx + d.nv)
    (hcolumn : d.fullBoundary ≤ x / d.uniform)
    (h₁ : d.rowBoundary₁ ≤ y)
    (h₂ : d.rowBoundary₂ ≤ y-d.rowBoundary₁)
    (haux : d.rowBoundary₃ ≤ y-d.rowBoundary₁-d.rowBoundary₂) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[(d.stagePrefixRows + (order j).val*d.rx +
            auxiliaryLabel d y%d.rx)*d.rawWidth+
            MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
              d.wordBase d.cy d.s d.binBase]?.getD false]) := by
  obtain ⟨tp, hp⟩ := diagonal_auxiliary_to_lookup d x y order j horder
    hwidth hj hcolumn h₁ h₂ haux
  let B := afterRowClear (diagonalAuxiliaryRowBank d x y)
  have hwork : ∀ k : Fin 10, k ≠ 0 → k ≠ 1 → k ≠ 2 →
      k ≠ 6 → k ≠ 7 → B (lookupSlots k) = [] := by
    intro k hk0 hk1 hk2 hk6 hk7
    fin_cases k <;> simp_all [lookupSlots] <;> rfl
  obtain ⟨hr, hw, hc, hs, ho, hwork'⟩ := orderPreLookup_frame
    d order j (auxiliaryLabel d y) true B
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase)
    (by rfl) (by rfl) (by rfl) (by rfl) hwork
  have hB : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      B k = cellBank d x y [] k := by
    intro k hk
    have hnot : ¬ ∃ i : Fin 41, workSlot i = k := by
      rintro ⟨i, hi⟩
      exact hk i hi
    cases k with
    | inl k =>
        fin_cases k <;> first | rfl | (exfalso; exact hnot (by decide))
    | inr k => fin_cases k <;> rfl
  obtain ⟨ts, hs'⟩ := lookup_and_clear d x y
    (d.stagePrefixRows + (order j).val*d.rx + auxiliaryLabel d y%d.rx)
    (MatrixWeightedDiagonalMachine.rawValue (diagonalCode d x)
      d.wordBase d.cy d.s d.binBase) (.order (.address false))
    (diagonalAuxiliaryPreLookup d x y order j)
    hr hw hc hs ho hwork'
    (by intro k hk
        exact orderPreLookup_stable d x y order j
          (auxiliaryLabel d y) true B horder hB k hk)
  exact ⟨tp+ts, (run_add hp ts).trans hs'⟩

/-- One complete branch of the literal entry callback, including the actual
raw-bit read and clearing of all temporary banks. -/
theorem full_full_run (d : Input) (x y : ℕ)
    (hcolumn : x / d.uniform < d.fullBoundary)
    (hrow : y < d.rowBoundary₁) :
    ∃ t, run t (cfg (some start) initial (cellBank d x y [])) =
      cfg none initial
        (cellBank d x y
          [d.rawBits[fullLabel d y*d.rawWidth+
            ((x/d.uniform)/d.fullDivisor)]?.getD false]) := by
  obtain ⟨t₀, h₀⟩ := full_full_to_lookup d x y hcolumn hrow
  obtain ⟨hrow', hwidth, hcol, hsource, hout, hwork⟩ :=
    fullFull_lookup_frame d x y
  obtain ⟨t₁, -, h₁⟩ := lookup_phase (.copy none)
    (fullFullPreLookup d x y) (fullLabel d y) d.rawWidth
    ((x/d.uniform)/d.fullDivisor) d.rawBits []
    hrow' hwidth hcol hsource hout hwork
  let bit := d.rawBits[fullLabel d y*d.rawWidth+
    ((x/d.uniform)/d.fullDivisor)]?.getD false
  let S := Function.update (fullFullPreLookup d x y) (.inr 2) [bit]
  have hclear := clear_run (.lookup MatrixTableLookup.initial) S
  have hstable : ∀ k, (∀ i : Fin 41, workSlot i ≠ k) →
      S k = cellBank d x y [bit] k := by
    intro k hk
    by_cases heq : k = .inr 2
    · subst k
      rfl
    · simp only [S, Function.update_of_ne heq]
      rw [fullFull_stable d x y k hk]
      cases k with
      | inl k => rfl
      | inr k => fin_cases k <;> simp_all [cellBank]
  have hfinal : BitMachineClearBank.cleared workSlot S =
      cellBank d x y [bit] :=
    cleared_to_cellBank d x y [bit] S hstable
  refine ⟨t₀+t₁+((∑ i, (S (workSlot i)).length)+43), ?_⟩
  rw [show t₀+t₁+((∑ i, (S (workSlot i)).length)+43) =
      t₀+(t₁+((∑ i, (S (workSlot i)).length)+43)) by omega]
  rw [run_add h₀, run_add h₁, hclear, hfinal]

end EthInapproximability.CurrentPaper.MatrixWeightedEntryController
