import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# A literal row-major truth-table writer

Source: locked v8 `B-effectivity-details.tex`, `thm:paper-materialization`.
The entry subroutine is an actual Boolean-stack program. This controller
supplies every row/column index, charges the physical counter operations,
and reverses the accumulated bits into natural row-major order. Its explicit
local-run hypothesis must be instantiated with the concrete entry evaluator;
the theorem is not itself the complete materialisation runtime endpoint.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableWriter

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

abbrev CellStack (K : ℕ) := Fin K ⊕ Fin 3

inductive Extra where
  | rows | cols | rowsLeft | colsLeft | temp | buffer | output
  deriving DecidableEq, Fintype

inductive Source where
  | rows | cols
  deriving DecidableEq, Fintype

inductive Admin where
  | copy (s : Source) | restore (s : Source) | rows | cols
  | afterCell | clearColumn | clearRow | reverse
  deriving DecidableEq, Fintype

abbrev Stack (K : ℕ) := CellStack K ⊕ Extra
abbrev Label (L : Type*) := L ⊕ Admin
abbrev Control (V : Type*) := V × Option Bool
abbrev Statement (K : ℕ) (L V : Type*) := TM2.Stmt (fun _ : Stack K => Bool) (Label L) (Control V)
abbrev Config (K : ℕ) (L V : Type*) := TM2.Cfg (fun _ : Stack K => Bool) (Label L) (Control V)

def Source.source {K : ℕ} : Source → Stack K
  | .rows => .inr .rows
  | .cols => .inr .cols

def Source.target {K : ℕ} : Source → Stack K
  | .rows => .inr .rowsLeft
  | .cols => .inr .colsLeft

def Source.next : Source → Admin
  | .rows => .rows
  | .cols => .cols

def go {K : ℕ} {L V : Type*} (l : Admin) : Statement K L V := goto (fun _ => .inr l)
def setPop {V : Type*} (v : Control V) (b : Option Bool) : Control V := (v.1, b)

variable {K : ℕ} {L V : Type*}
variable (P : L → TM2.Stmt (fun _ : CellStack K => Bool) L V) (start : L) (initial : V)

def program : Label L → Statement K L V
  | .inl l => liftStmt (some Admin.afterCell) (P l)
  | .inr (.copy s) => pop s.source setPop
      (branch (fun v => v.2.isSome)
        (push (.inr .temp) (fun v => v.2.getD false) (go (.copy s))) (go (.restore s)))
  | .inr (.restore s) => pop (.inr .temp) setPop
      (branch (fun v => v.2.isSome)
        (push s.source (fun v => v.2.getD false)
          (push s.target (fun v => v.2.getD false) (go (.restore s)))) (go s.next))
  | .inr .rows => pop (.inr .rowsLeft) setPop
      (branch (fun v => v.2.isSome) (go (.copy .cols)) (go .clearRow))
  | .inr .cols => pop (.inr .colsLeft) setPop
      (branch (fun v => v.2.isSome)
        (load (fun _ => (initial, none)) (goto (fun _ => .inl start)))
        (push (.inl (.inr 0)) (fun _ => true) (go .clearColumn)))
  | .inr .afterCell => pop (.inl (.inr 2)) setPop
      (push (.inr .buffer) (fun v => v.2.getD false)
        (push (.inl (.inr 1)) (fun _ => true) (go .cols)))
  | .inr .clearColumn => pop (.inl (.inr 1)) setPop
      (branch (fun v => v.2.isSome) (go .clearColumn) (go .rows))
  | .inr .clearRow => pop (.inl (.inr 0)) setPop
      (branch (fun v => v.2.isSome) (go .clearRow) (go .reverse))
  | .inr .reverse => pop (.inr .buffer) setPop
      (branch (fun v => v.2.isSome)
        (push (.inr .output) (fun v => v.2.getD false) (go .reverse)) halt)

structure Data (K : ℕ) where
  bank : Fin K → List Bool
  rowIndex : List Bool
  colIndex : List Bool
  answer : List Bool := []
  rows : List Bool
  cols : List Bool
  rowsLeft : List Bool
  colsLeft : List Bool
  temp : List Bool := []
  buffer : List Bool := []
  output : List Bool := []

def Data.cell (d : Data K) : CellStack K → List Bool :=
  Sum.elim d.bank (![d.rowIndex, d.colIndex, d.answer] : Fin 3 → List Bool)

def Data.foreign (d : Data K) : Extra → List Bool
  | .rows => d.rows
  | .cols => d.cols
  | .rowsLeft => d.rowsLeft
  | .colsLeft => d.colsLeft
  | .temp => d.temp
  | .buffer => d.buffer
  | .output => d.output

def Data.contents (d : Data K) : Stack K → List Bool := Sum.elim d.cell d.foreign

def cfg (l : Option (Label L)) (v : Control V) (d : Data K) : Config K L V :=
  ⟨l, v, d.contents⟩

def run (t : ℕ) (c : Config K L V) := ((advance (program P start initial))^[t]) c

theorem run_succ (t : ℕ) (c : Config K L V) :
    run P start initial (t + 1) c = run P start initial t (advance (program P start initial) c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config K L V) :
    run P start initial (t + u) c = run P start initial u (run P start initial t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance (program P start initial)) u t c

def Data.getSource (d : Data K) : Source → List Bool
  | .rows => d.rows
  | .cols => d.cols

def Data.setSource (d : Data K) (s : Source) (bits : List Bool) : Data K :=
  match s with
  | .rows => { d with rows := bits }
  | .cols => { d with cols := bits }

def Data.addTarget (d : Data K) (s : Source) (bits : List Bool) : Data K :=
  match s with
  | .rows => { d with rowsLeft := bits ++ d.rowsLeft }
  | .cols => { d with colsLeft := bits ++ d.colsLeft }

theorem copy_cons (s : Source) (v : Control V) (b : Bool) (bits : List Bool)
    (d : Data K) (he : d.getSource s = b :: bits) :
    advance (program P start initial) (cfg (some (.inr (.copy s))) v d) =
      cfg (some (.inr (.copy s))) (setPop v (some b))
        { d.setSource s bits with temp := b :: d.temp } := by
  cases s <;> simp only [Data.getSource] at he
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, Source.source, cfg,
      Data.contents, Sum.elim_inr, Data.foreign, Data.setSource,
      he, go, setPop, List.head?_cons, List.tail_cons,
      Option.isSome_some, cond_true, Option.getD_some]
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · fin_cases k <;> rfl
    · cases k <;> rfl

theorem copy_nil (s : Source) (v : Control V) (d : Data K) (he : d.getSource s = []) :
    advance (program P start initial) (cfg (some (.inr (.copy s))) v d) =
      cfg (some (.inr (.restore s))) (setPop v none) d := by
  cases s <;> simp only [Data.getSource] at he
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, Source.source, cfg,
      Data.contents, Sum.elim_inr, Data.foreign, he, go, setPop,
      List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · fin_cases k <;> rfl
    · cases k <;> simp [he, Data.foreign]

theorem restore_cons (s : Source) (v : Control V) (b : Bool) (bits : List Bool)
    (d : Data K) (he : d.temp = b :: bits) :
    advance (program P start initial) (cfg (some (.inr (.restore s))) v d) =
      cfg (some (.inr (.restore s))) (setPop v (some b))
        (({ d with temp := bits }.setSource s (b :: d.getSource s)).addTarget s [b]) := by
  cases s
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, Source.source, Source.target, cfg,
      Data.contents, Sum.elim_inr, Data.foreign, Data.getSource, Data.setSource,
      Data.addTarget, he, go, setPop, List.head?_cons, List.tail_cons,
      Option.isSome_some, cond_true, Option.getD_some]
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · fin_cases k <;> rfl
    · cases k <;> rfl

theorem restore_nil (s : Source) (v : Control V) (d : Data K) (he : d.temp = []) :
    advance (program P start initial) (cfg (some (.inr (.restore s))) v d) =
      cfg (some (.inr s.next)) (setPop v none) d := by
  cases s
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, Source.source, Source.target, cfg,
      Data.contents, Sum.elim_inr, Data.foreign, he, go, setPop,
      List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · fin_cases k <;> rfl
    · cases k <;> simp [he, Data.foreign]

theorem copy_run (s : Source) (v : Control V) (d : Data K) :
    run P start initial ((d.getSource s).length + 1) (cfg (some (.inr (.copy s))) v d) =
      cfg (some (.inr (.restore s))) (setPop v none)
        { d.setSource s [] with temp := (d.getSource s).reverse ++ d.temp } := by
  generalize he : d.getSource s = bits
  induction bits generalizing v d with
  | nil =>
      rw [show [].length + 1 = 0 + 1 from rfl, run_succ, copy_nil P start initial s v d he]
      simp only [run, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append]
      congr 1
      cases s <;> cases d <;> simp_all [Data.getSource, Data.setSource]
  | cons b bits ih =>
      rw [List.length_cons, run_succ, copy_cons P start initial s v b bits d he,
        ih _ _ (by cases s <;> rfl)]
      cases s <;> simp [Data.setSource, List.reverse_cons, List.append_assoc, setPop]

theorem restore_run (s : Source) (v : Control V) (d : Data K) :
    run P start initial (d.temp.length + 1) (cfg (some (.inr (.restore s))) v d) =
      cfg (some (.inr s.next)) (setPop v none)
        (({ d with temp := [] }.setSource s (d.temp.reverse ++ d.getSource s)).addTarget
          s d.temp.reverse) := by
  generalize he : d.temp = bits
  induction bits generalizing v d with
  | nil =>
      rw [show [].length + 1 = 0 + 1 from rfl, run_succ, restore_nil P start initial s v d he]
      simp only [run, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append]
      cases s <;> cases d <;> simp_all [Data.getSource, Data.setSource, Data.addTarget]
  | cons b bits ih =>
      rw [List.length_cons, run_succ, restore_cons P start initial s v b bits d he,
        ih _ _ (by cases s <;> rfl)]
      cases s <;> simp [Data.setSource, Data.getSource, Data.addTarget,
        List.reverse_cons, List.append_assoc, setPop]

theorem copy_correct (s : Source) (v : Control V) (d : Data K) (ht : d.temp = []) :
    run P start initial (2 * (d.getSource s).length + 2) (cfg (some (.inr (.copy s))) v d) =
      cfg (some (.inr s.next)) (setPop v none) (d.addTarget s (d.getSource s)) := by
  rw [show 2 * (d.getSource s).length + 2 =
      ((d.getSource s).length + 1) + ((d.getSource s).length + 1) by omega,
    run_add, copy_run]
  have hr := restore_run P start initial s (setPop v none)
    { d.setSource s [] with temp := (d.getSource s).reverse ++ d.temp }
  simp only [ht, List.append_nil, List.length_reverse] at hr
  simp only [ht, List.append_nil]
  rw [hr]
  cases s <;> cases d <;> simp_all [Data.setSource, Data.getSource, Data.addTarget, setPop]

def clearLabel (row : Bool) : Admin := if row then .clearRow else .clearColumn
def clearNext (row : Bool) : Admin := if row then .reverse else .rows
def Data.index (d : Data K) (row : Bool) := if row then d.rowIndex else d.colIndex
def Data.setIndex (d : Data K) (row : Bool) (bits : List Bool) :=
  if row then { d with rowIndex := bits } else { d with colIndex := bits }

theorem clear_cons (row : Bool) (v : Control V) (b : Bool) (bits : List Bool)
    (d : Data K) (he : d.index row = b :: bits) :
    advance (program P start initial) (cfg (some (.inr (clearLabel row))) v d) =
      cfg (some (.inr (clearLabel row))) (setPop v (some b)) (d.setIndex row bits) := by
  cases row <;> simp only [Data.index, Bool.false_eq_true, ↓reduceIte] at he
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, clearLabel, Data.setIndex,
      Bool.false_eq_true, ↓reduceIte, cfg, Data.contents, Data.cell, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, he, go, setPop,
      List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · fin_cases k <;> rfl
    · cases k <;> rfl

theorem clear_nil (row : Bool) (v : Control V) (d : Data K) (he : d.index row = []) :
    advance (program P start initial) (cfg (some (.inr (clearLabel row))) v d) =
      cfg (some (.inr (clearNext row))) (setPop v none) d := by
  cases row <;> simp only [Data.index, Bool.false_eq_true, ↓reduceIte] at he
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, clearLabel, clearNext,
      Bool.false_eq_true, ↓reduceIte, cfg, Data.contents, Data.cell, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, he, go, setPop,
      List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · fin_cases k <;> simp [he]
    · cases k <;> rfl

theorem clear_run (row : Bool) (v : Control V) (d : Data K) :
    run P start initial ((d.index row).length + 1) (cfg (some (.inr (clearLabel row))) v d) =
      cfg (some (.inr (clearNext row))) (setPop v none) (d.setIndex row []) := by
  generalize he : d.index row = bits
  induction bits generalizing v d with
  | nil =>
      rw [show [].length + 1 = 0 + 1 from rfl, run_succ, clear_nil P start initial row v d he]
      simp only [run, Function.iterate_zero, id_eq]
      congr 1
      cases row <;> cases d <;> simp_all [Data.index, Data.setIndex]
  | cons b bits ih =>
      rw [List.length_cons, run_succ, clear_cons P start initial row v b bits d he,
        ih _ _ (by cases row <;> rfl)]
      cases row <;> rfl

theorem reverse_cons (v : Control V) (b : Bool) (bits : List Bool)
    (d : Data K) (he : d.buffer = b :: bits) :
    advance (program P start initial) (cfg (some (.inr .reverse)) v d) =
      cfg (some (.inr .reverse)) (setPop v (some b))
        { d with buffer := bits, output := b :: d.output } := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Sum.elim_inr,
    Data.foreign, he, go, setPop, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl

theorem reverse_nil (v : Control V) (d : Data K) (he : d.buffer = []) :
    advance (program P start initial) (cfg (some (.inr .reverse)) v d) =
      cfg none (setPop v none) d := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Sum.elim_inr,
    Data.foreign, he, go, setPop, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> simp [Data.foreign, he]

theorem reverse_run (v : Control V) (d : Data K) :
    run P start initial (d.buffer.length + 1) (cfg (some (.inr .reverse)) v d) =
      cfg none (setPop v none) { d with buffer := [], output := d.buffer.reverse ++ d.output } := by
  generalize he : d.buffer = bits
  induction bits generalizing v d with
  | nil =>
      rw [show [].length + 1 = 0 + 1 from rfl, run_succ, reverse_nil P start initial v d he]
      simp only [run, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append]
      congr 1
      cases d
      simp_all
  | cons b bits ih =>
      rw [List.length_cons, run_succ, reverse_cons P start initial v b bits d he, ih _ _ rfl]
      simp [List.reverse_cons, List.append_assoc, setPop]

theorem rows_nil (v : Control V) (d : Data K) (he : d.rowsLeft = []) :
    advance (program P start initial) (cfg (some (.inr .rows)) v d) =
      cfg (some (.inr .clearRow)) (setPop v none) d := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Sum.elim_inr,
    Data.foreign, he, go, setPop, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> simp [Data.foreign, he]

theorem rows_cons (v : Control V) (b : Bool) (bits : List Bool)
    (d : Data K) (he : d.rowsLeft = b :: bits) :
    advance (program P start initial) (cfg (some (.inr .rows)) v d) =
      cfg (some (.inr (.copy .cols))) (setPop v (some b)) { d with rowsLeft := bits } := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Sum.elim_inr,
    Data.foreign, he, go, setPop, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl

theorem cols_nil (v : Control V) (d : Data K) (he : d.colsLeft = []) :
    advance (program P start initial) (cfg (some (.inr .cols)) v d) =
      cfg (some (.inr .clearColumn)) (setPop v none)
        { d with rowIndex := true :: d.rowIndex } := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Sum.elim_inr,
    Data.foreign, he, go, setPop, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl

theorem cols_cons (v : Control V) (b : Bool) (bits : List Bool)
    (d : Data K) (he : d.colsLeft = b :: bits) :
    advance (program P start initial) (cfg (some (.inr .cols)) v d) =
      cfg (some (.inl start)) (initial, none) { d with colsLeft := bits } := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Sum.elim_inr,
    Data.foreign, he, go, setPop, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl

theorem afterCell (v : Control V) (b : Bool) (d : Data K) (he : d.answer = [b]) :
    advance (program P start initial) (cfg (some (.inr .afterCell)) v d) =
      cfg (some (.inr .cols)) (setPop v (some b))
        { d with answer := [], colIndex := true :: d.colIndex, buffer := b :: d.buffer } := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Data.contents, Data.cell,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_two, he, setPop, go, Option.getD_some]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl

def ready (bank : Fin K → List Bool) (r c x y nr nc : ℕ) (buffer output : List Bool) : Data K where
  bank := bank
  rowIndex := List.replicate x true
  colIndex := List.replicate y true
  rows := List.replicate r true
  cols := List.replicate c true
  rowsLeft := List.replicate nr true
  colsLeft := List.replicate nc true
  buffer := buffer
  output := output

def cellCfg (l : Option L) (v : V) (bank : Fin K → List Bool)
    (x y : ℕ) (answer : List Bool) : TM2.Cfg (fun _ : CellStack K => Bool) L V :=
  ⟨l, v, Sum.elim bank (![List.replicate x true, List.replicate y true, answer] : Fin 3 → List Bool)⟩

/-- Local contract consumed by the writer. It quantifies actual executions
of the supplied fixed entry program; it is not a table-output oracle. -/
def EntryRuns (bank : Fin K → List Bool) (r c T : ℕ) (entry : ℕ → ℕ → Bool) : Prop :=
  ∀ x < r, ∀ y < c, ∃ t ≤ T, ∃ v,
    ((advance P)^[t]) (cellCfg (some start) initial bank x y []) =
      cellCfg none v bank x y [entry x y]

theorem lift_cell_cfg (l : Option L) (v : V) (other : Option Bool) (d : Data K) :
    liftCfg (some Admin.afterCell) other d.foreign
      (⟨l, v, d.cell⟩ : TM2.Cfg (fun _ : CellStack K => Bool) L V) =
      cfg (match l with | none => some (.inr .afterCell) | some q => some (.inl q))
        (v, other) d := by
  cases l <;> rfl

theorem cell_run (bank : Fin K → List Bool) (r c T : ℕ) (entry : ℕ → ℕ → Bool)
    (hcell : EntryRuns P start initial bank r c T entry)
    (x y nr nc : ℕ) (hx : x < r) (hy : y < c) (buffer output : List Bool) :
    ∃ t ≤ T, ∃ v,
      run P start initial t (cfg (some (.inl start)) (initial, none)
        (ready bank r c x y nr nc buffer output)) =
      cfg (some (.inr .afterCell)) (v, none)
        { ready bank r c x y nr nc buffer output with answer := [entry x y] } := by
  obtain ⟨n, hn, v, he⟩ := hcell x hx y hy
  have hh : (((advance P)^[n]) (cellCfg (some start) initial bank x y [])).l = none := by
    rw [he]; rfl
  obtain ⟨t, ht, hr⟩ := lift_outputs P (program P start initial) (some Admin.afterCell)
    (fun _ => rfl) none (Data.foreign (ready bank r c x y nr nc buffer output))
    (cellCfg (some start) initial bank x y []) n hh
  rw [he] at hr
  refine ⟨t, ht.trans hn, v, ?_⟩
  exact hr

def rowWord (entry : ℕ → ℕ → Bool) (x : ℕ) : ℕ → ℕ → List Bool
  | _, 0 => []
  | y, nc + 1 => entry x y :: rowWord entry x (y + 1) nc

def tableWord (entry : ℕ → ℕ → Bool) (c : ℕ) : ℕ → ℕ → List Bool
  | _, 0 => []
  | x, nr + 1 => rowWord entry x 0 c ++ tableWord entry c (x + 1) nr

@[simp] theorem rowWord_length (entry : ℕ → ℕ → Bool) (x y nc : ℕ) :
    (rowWord entry x y nc).length = nc := by
  induction nc generalizing y with
  | zero => rfl
  | succ nc ih => simp [rowWord, ih]

@[simp] theorem tableWord_length (entry : ℕ → ℕ → Bool) (c x nr : ℕ) :
    (tableWord entry c x nr).length = nr * c := by
  induction nr generalizing x with
  | zero => simp [tableWord]
  | succ nr ih => simp [tableWord, ih, Nat.add_mul, Nat.add_comm]

theorem columns_run (bank : Fin K → List Bool) (r c T : ℕ) (entry : ℕ → ℕ → Bool)
    (hcell : EntryRuns P start initial bank r c T entry)
    (x y nr nc : ℕ) (hx : x < r) (hy : y + nc ≤ c)
    (buffer output : List Bool) (v : Control V) :
    ∃ t ≤ nc * (T + 2) + 1, ∃ v',
      run P start initial t (cfg (some (.inr .cols)) v
        (ready bank r c x y nr nc buffer output)) =
      cfg (some (.inr .clearColumn)) v'
        (ready bank r c (x + 1) (y + nc) nr 0
          ((rowWord entry x y nc).reverse ++ buffer) output) := by
  induction nc generalizing y buffer v with
  | zero =>
      refine ⟨1, by simp, setPop v none, ?_⟩
      change run P start initial (0 + 1) _ = _
      rw [run_succ, cols_nil P start initial v (ready bank r c x y nr 0 buffer output) rfl]
      simp [run, ready, rowWord, List.replicate_succ]
  | succ nc ih =>
      have hstart : run P start initial 1
          (cfg (some (.inr .cols)) v (ready bank r c x y nr (nc + 1) buffer output)) =
          cfg (some (.inl start)) (initial, none)
            (ready bank r c x y nr nc buffer output) := by
        change run P start initial (0 + 1) _ = _
        rw [run_succ, cols_cons P start initial v true (List.replicate nc true)
          (ready bank r c x y nr (nc + 1) buffer output) (by simp [ready, List.replicate_succ])]
        rfl
      obtain ⟨te, hte, ve, he⟩ := cell_run P start initial bank r c T entry hcell
        x y nr nc hx (by omega) buffer output
      let final := { ready bank r c x y nr nc buffer output with answer := [entry x y] }
      have hpre : run P start initial (1 + te)
          (cfg (some (.inr .cols)) v (ready bank r c x y nr (nc + 1) buffer output)) =
          cfg (some (.inr .afterCell)) (ve, none) final := by
        rw [run_add, hstart, he]
      have hstep : run P start initial 1 (cfg (some (.inr .afterCell)) (ve, none) final) =
          cfg (some (.inr .cols)) (ve, some (entry x y))
            (ready bank r c x (y + 1) nr nc (entry x y :: buffer) output) := by
        change run P start initial (0 + 1) _ = _
        rw [run_succ, afterCell P start initial (ve, none) (entry x y) final rfl]
        simp only [run, Function.iterate_zero, id_eq, final, ready, List.replicate_succ, setPop]
      obtain ⟨ti, hti, vi, hi⟩ := ih (y + 1) (by omega)
        (entry x y :: buffer) (ve, some (entry x y))
      refine ⟨1 + te + 1 + ti, by nlinarith, vi, ?_⟩
      rw [run_add, run_add, hpre, hstep, hi]
      simp only [rowWord, List.reverse_cons, List.append_assoc, List.singleton_append,
        Nat.add_assoc, Nat.add_comm 1 nc]

def rowBound (c T : ℕ) : ℕ := c * (T + 2) + 3 * c + 5

theorem rows_run (bank : Fin K → List Bool) (r c T : ℕ) (entry : ℕ → ℕ → Bool)
    (hcell : EntryRuns P start initial bank r c T entry)
    (x nr : ℕ) (hx : x + nr ≤ r) (buffer output : List Bool) (v : Control V) :
    ∃ t ≤ nr * rowBound c T + 1, ∃ v',
      run P start initial t (cfg (some (.inr .rows)) v
        (ready bank r c x 0 nr 0 buffer output)) =
      cfg (some (.inr .clearRow)) v'
        (ready bank r c (x + nr) 0 0 0 ((tableWord entry c x nr).reverse ++ buffer) output) := by
  induction nr generalizing x buffer v with
  | zero =>
      refine ⟨1, by simp, setPop v none, ?_⟩
      change run P start initial (0 + 1) _ = _
      rw [run_succ, rows_nil P start initial v (ready bank r c x 0 0 0 buffer output) rfl]
      simp [run, tableWord]
  | succ nr ih =>
      have hstart : run P start initial 1
          (cfg (some (.inr .rows)) v (ready bank r c x 0 (nr + 1) 0 buffer output)) =
          cfg (some (.inr (.copy .cols))) (setPop v (some true))
            (ready bank r c x 0 nr 0 buffer output) := by
        change run P start initial (0 + 1) _ = _
        rw [run_succ, rows_cons P start initial v true (List.replicate nr true)
          (ready bank r c x 0 (nr + 1) 0 buffer output) (by simp [ready, List.replicate_succ])]
        rfl
      have hcopy : run P start initial (2 * c + 2)
          (cfg (some (.inr (.copy .cols))) (setPop v (some true))
            (ready bank r c x 0 nr 0 buffer output)) =
          cfg (some (.inr .cols)) (setPop v none)
            (ready bank r c x 0 nr c buffer output) := by
        have he := copy_correct P start initial .cols (setPop v (some true))
          (ready bank r c x 0 nr 0 buffer output) rfl
        simpa only [Data.getSource, Data.addTarget, ready, List.length_replicate,
          List.replicate_zero, List.append_nil, Source.next, setPop] using he
      obtain ⟨tc, htc, vc, hc⟩ := columns_run P start initial bank r c T entry hcell
        x 0 nr c (by omega) (by omega) buffer output (setPop v none)
      simp only [Nat.zero_add] at hc
      have hclear : run P start initial (c + 1)
          (cfg (some (.inr .clearColumn)) vc
            (ready bank r c (x + 1) c nr 0 ((rowWord entry x 0 c).reverse ++ buffer) output)) =
          cfg (some (.inr .rows)) (setPop vc none)
            (ready bank r c (x + 1) 0 nr 0 ((rowWord entry x 0 c).reverse ++ buffer) output) := by
        have he := clear_run P start initial false vc
          (ready bank r c (x + 1) c nr 0 ((rowWord entry x 0 c).reverse ++ buffer) output)
        simpa only [Data.index, Data.setIndex, clearLabel, clearNext, Bool.false_eq_true,
          ↓reduceIte, ready, List.length_replicate, List.replicate_zero] using he
      obtain ⟨ti, hti, vi, hi⟩ := ih (x + 1) (by omega)
        ((rowWord entry x 0 c).reverse ++ buffer) (setPop vc none)
      refine ⟨1 + (2 * c + 2) + tc + (c + 1) + ti, ?_, vi, ?_⟩
      · dsimp [rowBound] at hti ⊢
        nlinarith
      · rw [run_add (u := ti), run_add (u := c + 1), run_add (u := tc),
          run_add (u := 2 * c + 2), hstart, hcopy, hc, hclear, hi]
        simp only [tableWord, List.reverse_append, List.append_assoc,
          Nat.add_assoc, Nat.add_comm 1 nr]

def writerBound (r c T : ℕ) : ℕ := r * (c * (T + 2) + 4 * c + 8) + 5

/-- All loop, counter setup, cleanup, and output-writing costs are charged.
The local entry contract is the sole remaining implementation input. The
writer restores dimensions, data, and empty row/column indices, and preserves
an arbitrary old output suffix. It handles zero dimensions without a promise. -/
theorem write_table (bank : Fin K → List Bool) (r c T : ℕ) (entry : ℕ → ℕ → Bool)
    (hcell : EntryRuns P start initial bank r c T entry) (output : List Bool) :
    ∃ t ≤ writerBound r c T, ∃ v,
      run P start initial t (cfg (some (.inr (.copy .rows))) (initial, none)
        (ready bank r c 0 0 0 0 [] output)) =
      cfg none v (ready bank r c 0 0 0 0 [] (tableWord entry c 0 r ++ output)) := by
  have hcopy : run P start initial (2 * r + 2)
      (cfg (some (.inr (.copy .rows))) (initial, none) (ready bank r c 0 0 0 0 [] output)) =
      cfg (some (.inr .rows)) (initial, none) (ready bank r c 0 0 r 0 [] output) := by
    have he := copy_correct P start initial .rows ((initial, none) : Control V)
      (ready bank r c 0 0 0 0 [] output) rfl
    simpa only [Data.getSource, Data.addTarget, ready, List.length_replicate,
      List.replicate_zero, List.append_nil, Source.next, setPop] using he
  obtain ⟨tb, htb, vb, hb⟩ := rows_run P start initial bank r c T entry hcell
    0 r (by omega) [] output (initial, none)
  simp only [Nat.zero_add, List.append_nil] at hb
  have hclear : run P start initial (r + 1)
      (cfg (some (.inr .clearRow)) vb (ready bank r c r 0 0 0 (tableWord entry c 0 r).reverse output)) =
      cfg (some (.inr .reverse)) (setPop vb none)
        (ready bank r c 0 0 0 0 (tableWord entry c 0 r).reverse output) := by
    have he := clear_run P start initial true vb
      (ready bank r c r 0 0 0 (tableWord entry c 0 r).reverse output)
    simpa only [Data.index, Data.setIndex, clearLabel, clearNext, ↓reduceIte,
      ready, List.length_replicate, List.replicate_zero] using he
  have hreverse : run P start initial (r * c + 1)
      (cfg (some (.inr .reverse)) (setPop vb none)
        (ready bank r c 0 0 0 0 (tableWord entry c 0 r).reverse output)) =
      cfg none (setPop vb none)
        (ready bank r c 0 0 0 0 [] (tableWord entry c 0 r ++ output)) := by
    have he := reverse_run P start initial (setPop vb none)
      (ready bank r c 0 0 0 0 (tableWord entry c 0 r).reverse output)
    simpa only [ready, List.length_reverse, tableWord_length, List.reverse_reverse, setPop] using he
  refine ⟨2 * r + 2 + tb + (r + 1) + (r * c + 1), ?_, setPop vb none, ?_⟩
  · dsimp [rowBound, writerBound] at htb ⊢
    nlinarith
  · rw [run_add (u := r * c + 1), run_add (u := r + 1), run_add (u := tb),
      hcopy, hb, hclear, hreverse]

theorem rowWord_lookup (entry : ℕ → ℕ → Bool) (x y nc j : ℕ) (hj : j < nc) :
    (rowWord entry x y nc)[j]? = some (entry x (y + j)) := by
  induction nc generalizing y j with
  | zero => omega
  | succ nc ih =>
      cases j with
      | zero => simp [rowWord]
      | succ j =>
          simpa [rowWord, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (y + 1) j (by omega)

theorem tableWord_lookup (entry : ℕ → ℕ → Bool) (c x nr i j : ℕ)
    (hi : i < nr) (hj : j < c) :
    (tableWord entry c x nr)[i * c + j]? = some (entry (x + i) j) := by
  induction nr generalizing x i with
  | zero => omega
  | succ nr ih =>
      cases i with
      | zero =>
          simpa [tableWord, List.getElem?_append, hj] using rowWord_lookup entry x 0 c j hj
      | succ i =>
          have hindex : (i + 1) * c + j = c + (i * c + j) := by ring
          have hge : ¬c + (i * c + j) < c := by omega
          simpa [tableWord, hindex, List.getElem?_append, hge,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (x + 1) i (by omega)

/-- The output order agrees with the existing finite matrix materializer,
including its zero-dimensional cases. -/
theorem tableWord_eq_rowMajor (r c : ℕ) (entry : ℕ → ℕ → Bool)
    (f : Fin r → Fin c → Bool) (he : ∀ x y, entry x.val y.val = f x y) :
    tableWord entry c 0 r = MatrixMaterialization.rowMajor f := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < r * c := by simpa using hleft
    let xy : Fin r × Fin c := finProdFinEquiv.symm ⟨i, hi⟩
    have hindex : xy.1.val * c + xy.2.val = i := by
      have hpair : finProdFinEquiv xy = ⟨i, hi⟩ := Equiv.apply_symm_apply _ _
      have hh := congrArg Fin.val hpair
      simpa only [finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm] using hh
    have hl := tableWord_lookup entry c 0 r xy.1.val xy.2.val xy.1.isLt xy.2.isLt
    have hr := MatrixMaterialization.rowMajor_entry f xy.1 xy.2
    rw [hindex] at hl hr
    simp only [Nat.zero_add, he, List.getElem?_eq_getElem hleft,
      List.getElem?_eq_getElem hright, Option.some.injEq] at hl hr
    exact hl.trans hr.symm

theorem write_rowMajor (bank : Fin K → List Bool) (r c T : ℕ) (entry : ℕ → ℕ → Bool)
    (f : Fin r → Fin c → Bool) (he : ∀ x y, entry x.val y.val = f x y)
    (hcell : EntryRuns P start initial bank r c T entry) (output : List Bool) :
    ∃ t ≤ writerBound r c T, ∃ v,
      run P start initial t (cfg (some (.inr (.copy .rows))) (initial, none)
        (ready bank r c 0 0 0 0 [] output)) =
      cfg none v (ready bank r c 0 0 0 0 [] (MatrixMaterialization.rowMajor f ++ output)) := by
  simpa only [tableWord_eq_rowMajor r c entry f he] using
    write_table P start initial bank r c T entry hcell output

theorem writerBound_polynomial (r c T : ℕ) :
    writerBound r c T ≤ 20 * (r + c + T + 1) ^ 3 := by
  let n := r + c + T + 1
  have hr : r ≤ n := by dsimp [n]; omega
  have hc : c ≤ n := by dsimp [n]; omega
  have hT : T ≤ n := by dsimp [n]; omega
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hinside : c * (T + 2) + 4 * c + 8 ≤ 15 * n ^ 2 := by
    have hm := Nat.mul_le_mul hc (Nat.add_le_add_right hT 2)
    nlinarith [Nat.mul_le_mul hn hn]
  have hm := Nat.mul_le_mul hr hinside
  change r * (c * (T + 2) + 4 * c + 8) + 5 ≤ 20 * n ^ 3
  nlinarith [Nat.mul_le_mul hn (Nat.mul_le_mul hn hn)]

end EthInapproximability.CurrentPaper.MatrixTableWriter
