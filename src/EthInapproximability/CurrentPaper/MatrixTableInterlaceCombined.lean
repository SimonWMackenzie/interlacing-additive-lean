import EthInapproximability.CurrentPaper.MatrixTableInterlaceSize
import EthInapproximability.CurrentPaper.MatrixTableInterlace
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# One physical Boolean-stack classical interlace materializer

Frozen v8 `def:paper-interlace`, `thm:paper-materialization`.  The size
initializer, two unary transfers, and literal row-major writer share one
fixed sum of Boolean-stack banks and one finite instruction table.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceCombined

set_option maxRecDepth 2048

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutine BitMachineSubroutineRenaming

abbrev WStack := MatrixTableWriter.Stack 20
abbrev WLabel := MatrixTableWriter.Label MatrixTableInterlaceEntry.Label
abbrev WControl := MatrixTableWriter.Control MatrixTableInterlaceEntry.Control
abbrev Stack := MatrixTableInterlaceSize.Stack ⊕ WStack

inductive Bridge where
  | moveRows | moveCols
  deriving DecidableEq, Fintype

abbrev Label := MatrixTableInterlaceSize.Label ⊕ (Bridge ⊕ WLabel)
abbrev Control := MatrixTableInterlaceSize.Control × WControl
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def start : Label := .inl MatrixTableInterlaceSize.start
def writerStart : Label := .inr (.inr (.inr (.copy .rows)))
def initial : Control := (MatrixTableInterlaceSize.initial,
  (MatrixTableInterlaceEntry.initial, none))

def writerLabels : WLabel ⊕ (MatrixTableInterlaceSize.Label ⊕ Bridge) ≃ Label where
  toFun
    | .inl l => .inr (.inr l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inl l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr l)
    | .inr (.inr l) => .inl l
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inl Bridge.moveRows)) (MatrixTableInterlaceSize.program l)
  | .inr (.inl .moveRows) =>
      pop (.inl 3) (fun v b => (v.1,(v.2.1,b)))
        (branch (fun v => v.2.2.isSome)
          (push (.inr (.inr .rows)) (fun _ => true)
            (load (fun _ => initial) (goto (fun _ => .inr (.inl .moveRows)))))
          (load (fun _ => initial) (goto (fun _ => .inr (.inl .moveCols)))))
  | .inr (.inl .moveCols) =>
      pop (.inl 4) (fun v b => (v.1,(v.2.1,b)))
        (branch (fun v => v.2.2.isSome)
          (push (.inr (.inr .cols)) (fun _ => true)
            (load (fun _ => initial) (goto (fun _ => .inr (.inl .moveCols)))))
          (load (fun _ => initial) (goto (fun _ => writerStart))))
  | .inr (.inr l) =>
      renameStmt (Equiv.sumComm WStack MatrixTableInterlaceSize.Stack) writerLabels
        (Equiv.prodComm WControl MatrixTableInterlaceSize.Control)
        (liftStmt none
          (MatrixTableWriter.program MatrixTableInterlace.entryProgram
            MatrixTableInterlaceEntry.start MatrixTableInterlaceEntry.initial l))

def cfg (l : Option Label) (v : Control)
    (size : MatrixTableInterlaceSize.Stack → List Bool)
    (writer : WStack → List Bool) : Config :=
  ⟨l,v,Sum.elim size writer⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def sizeFrame (v : WControl) (writer : WStack → List Bool)
    (c : MatrixTableInterlaceSize.Config) : Config :=
  liftCfg (some (.inl Bridge.moveRows)) v writer c

def writerFrame (v : MatrixTableInterlaceSize.Control)
    (size : MatrixTableInterlaceSize.Stack → List Bool)
    (c : MatrixTableWriter.Config 20 MatrixTableInterlaceEntry.Label
      MatrixTableInterlaceEntry.Control) : Config :=
  renameCfg (Equiv.sumComm WStack MatrixTableInterlaceSize.Stack) writerLabels
    (Equiv.prodComm WControl MatrixTableInterlaceSize.Control)
    (liftCfg none v size c)

theorem size_phase (blocks rows cols : ℕ) (v : WControl)
    (writer : WStack → List Bool) :
    ∃ t ≤ MatrixTableInterlaceSize.sizeBound blocks rows cols,
      run t (sizeFrame v writer
        (MatrixTableInterlaceSize.cfg (some MatrixTableInterlaceSize.start)
          MatrixTableInterlaceSize.initial (List.replicate blocks true)
          (List.replicate rows true) (List.replicate cols true) [] [] [] [] [])) =
      sizeFrame v writer
        (MatrixTableInterlaceSize.cfg none MatrixTableInterlaceSize.initial
          (List.replicate blocks true) (List.replicate rows true)
          (List.replicate cols true) (List.replicate (blocks*rows) true)
          (List.replicate (cols^blocks) true) [] [] []) := by
  obtain ⟨t,ht,he⟩ := MatrixTableInterlaceSize.size_run blocks rows cols
  obtain ⟨u,hu,hr⟩ := lift_outputs MatrixTableInterlaceSize.program program
    (some (.inl Bridge.moveRows)) (fun _ => rfl) v writer
    (MatrixTableInterlaceSize.cfg (some MatrixTableInterlaceSize.start)
      MatrixTableInterlaceSize.initial (List.replicate blocks true)
      (List.replicate rows true) (List.replicate cols true) [] [] [] [] [])
    t (by change (MatrixTableInterlaceSize.run t _).l = none; rw [he]; rfl)
  change run u (sizeFrame v writer _) = sizeFrame v writer
    (MatrixTableInterlaceSize.run t _) at hr
  rw [he] at hr
  exact ⟨u,hu.trans ht,hr⟩

def sizeBank (blocks rows cols : ℕ) (rowCount colCount : List Bool) :
    MatrixTableInterlaceSize.Stack → List Bool :=
  (MatrixTableInterlaceSize.cfg none MatrixTableInterlaceSize.initial
    (List.replicate blocks true) (List.replicate rows true)
    (List.replicate cols true) rowCount colCount [] [] []).stk

def writerData (rows cols : ℕ) (source output rowCount colCount : List Bool) :
    MatrixTableWriter.Data 20 where
  bank := MatrixTableInterlace.persistentBank rows cols source
  rowIndex := []
  colIndex := []
  rows := rowCount
  cols := colCount
  rowsLeft := []
  colsLeft := []
  output := output

def bridgeCfg (l : Label) (blocks rows cols : ℕ)
    (source output rowIn colIn rowOut colOut : List Bool) : Config :=
  cfg (some l) initial (sizeBank blocks rows cols rowIn colIn)
    (writerData rows cols source output rowOut colOut).contents

theorem move_rows_cons (blocks rows cols : ℕ)
    (source output rowIn colIn rowOut colOut : List Bool) :
    run 1 (bridgeCfg (.inr (.inl .moveRows)) blocks rows cols
      source output (true::rowIn) colIn rowOut colOut) =
    bridgeCfg (.inr (.inl .moveRows)) blocks rows cols
      source output rowIn colIn (true::rowOut) colOut := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some, bridgeCfg, cfg]
  have hin : Sum.elim (sizeBank blocks rows cols (true::rowIn) colIn)
      (writerData rows cols source output rowOut colOut).contents (.inl 3) =
      true::rowIn := rfl
  rw [hin]
  simp only [List.head?_cons, Option.isSome_some, cond_true,
    List.tail_cons]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
      cases k with
      | inl k =>
          cases k with
          | inl k => fin_cases k <;> rfl
          | inr k => fin_cases k <;> rfl
      | inr k => cases k <;> rfl

theorem move_rows_nil (blocks rows cols : ℕ)
    (source output colIn rowOut colOut : List Bool) :
    run 1 (bridgeCfg (.inr (.inl .moveRows)) blocks rows cols
      source output [] colIn rowOut colOut) =
    bridgeCfg (.inr (.inl .moveCols)) blocks rows cols
      source output [] colIn rowOut colOut := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some, bridgeCfg, cfg]
  have hin : Sum.elim (sizeBank blocks rows cols [] colIn)
      (writerData rows cols source output rowOut colOut).contents (.inl 3) =
      [] := rfl
  rw [hin]
  simp only [List.head?_nil, Option.isSome_none, cond_false, List.tail_nil]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => rfl

theorem move_cols_cons (blocks rows cols : ℕ)
    (source output rowIn colIn rowOut colOut : List Bool) :
    run 1 (bridgeCfg (.inr (.inl .moveCols)) blocks rows cols
      source output rowIn (true::colIn) rowOut colOut) =
    bridgeCfg (.inr (.inl .moveCols)) blocks rows cols
      source output rowIn colIn rowOut (true::colOut) := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some, bridgeCfg, cfg]
  have hin : Sum.elim (sizeBank blocks rows cols rowIn (true::colIn))
      (writerData rows cols source output rowOut colOut).contents (.inl 4) =
      true::colIn := rfl
  rw [hin]
  simp only [List.head?_cons, Option.isSome_some, cond_true,
    List.tail_cons]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
      cases k with
      | inl k =>
          cases k with
          | inl k => fin_cases k <;> rfl
          | inr k => fin_cases k <;> rfl
      | inr k => cases k <;> rfl

theorem move_cols_nil (blocks rows cols : ℕ)
    (source output rowIn rowOut colOut : List Bool) :
    run 1 (bridgeCfg (.inr (.inl .moveCols)) blocks rows cols
      source output rowIn [] rowOut colOut) =
    cfg (some writerStart) initial
      (sizeBank blocks rows cols rowIn [])
      (writerData rows cols source output rowOut colOut).contents := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some, bridgeCfg, cfg]
  have hin : Sum.elim (sizeBank blocks rows cols rowIn [])
      (writerData rows cols source output rowOut colOut).contents (.inl 4) =
      [] := rfl
  rw [hin]
  simp only [List.head?_nil, Option.isSome_none, cond_false, List.tail_nil]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => rfl

theorem move_rows_run (blocks rows cols n : ℕ)
    (source output colIn rowOut colOut : List Bool) :
    run (n+1) (bridgeCfg (.inr (.inl .moveRows)) blocks rows cols
      source output (List.replicate n true) colIn rowOut colOut) =
    bridgeCfg (.inr (.inl .moveCols)) blocks rows cols
      source output [] colIn (List.replicate n true ++ rowOut) colOut := by
  induction n generalizing rowOut with
  | zero => simpa using move_rows_nil blocks rows cols source output colIn rowOut colOut
  | succ n ih =>
      have h := run_add (move_rows_cons blocks rows cols source output
        (List.replicate n true) colIn rowOut colOut) (n+1)
      have hlist : List.replicate n true ++ true :: rowOut =
          List.replicate (n+1) true ++ rowOut := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      have hz := h.trans (ih (true::rowOut))
      rw [hlist] at hz
      simpa only [List.replicate_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz

theorem move_cols_run (blocks rows cols n : ℕ)
    (source output rowIn rowOut colOut : List Bool) :
    run (n+1) (bridgeCfg (.inr (.inl .moveCols)) blocks rows cols
      source output rowIn (List.replicate n true) rowOut colOut) =
    cfg (some writerStart) initial (sizeBank blocks rows cols rowIn [])
      (writerData rows cols source output rowOut
        (List.replicate n true ++ colOut)).contents := by
  induction n generalizing colOut with
  | zero => simpa using move_cols_nil blocks rows cols source output rowIn rowOut colOut
  | succ n ih =>
      have h := run_add (move_cols_cons blocks rows cols source output
        rowIn (List.replicate n true) rowOut colOut) (n+1)
      have hlist : List.replicate n true ++ true :: colOut =
          List.replicate (n+1) true ++ colOut := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      have hz := h.trans (ih (true::colOut))
      rw [hlist] at hz
      simpa only [List.replicate_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz

theorem bridge_run (blocks rows cols : ℕ) (source output : List Bool) :
    run ((blocks*rows+1)+(cols^blocks+1))
      (bridgeCfg (.inr (.inl .moveRows)) blocks rows cols source output
        (List.replicate (blocks*rows) true)
        (List.replicate (cols^blocks) true) [] []) =
    cfg (some writerStart) initial (sizeBank blocks rows cols [] [])
      (writerData rows cols source output
        (List.replicate (blocks*rows) true)
        (List.replicate (cols^blocks) true)).contents := by
  have h := run_add (move_rows_run blocks rows cols (blocks*rows) source output
    (List.replicate (cols^blocks) true) [] []) (cols^blocks+1)
  simp only [List.append_nil] at h
  simpa only [List.append_nil] using
    h.trans (move_cols_run blocks rows cols (cols^blocks)
      source output [] (List.replicate (blocks*rows) true) [])

theorem writer_phase (blocks rows cols : ℕ) (source output : List Bool)
    (size : MatrixTableInterlaceSize.Stack → List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
      (MatrixTableInterlace.uniformBound blocks rows cols source.length),
      ∃ v,
        run t (writerFrame MatrixTableInterlaceSize.initial size
          (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
            (MatrixTableInterlaceEntry.initial,none)
            (MatrixTableWriter.ready
              (MatrixTableInterlace.persistentBank rows cols source)
              (blocks*rows) (cols^blocks) 0 0 0 0 [] output))) =
        writerFrame MatrixTableInterlaceSize.initial size
          (MatrixTableWriter.cfg none v
            (MatrixTableWriter.ready
              (MatrixTableInterlace.persistentBank rows cols source)
              (blocks*rows) (cols^blocks) 0 0 0 0 []
              (MatrixTableWriter.tableWord
                (MatrixTableInterlaceCodes.entry rows cols source)
                (cols^blocks) 0 (blocks*rows) ++ output))) := by
  obtain ⟨t,ht,v,he⟩ :=
    MatrixTableInterlace.interlace_table blocks rows cols source output
  obtain ⟨u,hu,hr⟩ := lift_outputs_renamed
    (Equiv.sumComm WStack MatrixTableInterlaceSize.Stack) writerLabels
    (Equiv.prodComm WControl MatrixTableInterlaceSize.Control)
    (MatrixTableWriter.program MatrixTableInterlace.entryProgram
      MatrixTableInterlaceEntry.start MatrixTableInterlaceEntry.initial)
    program none (fun _ => rfl) MatrixTableInterlaceSize.initial size
    (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
      (MatrixTableInterlaceEntry.initial,none)
      (MatrixTableWriter.ready
        (MatrixTableInterlace.persistentBank rows cols source)
        (blocks*rows) (cols^blocks) 0 0 0 0 [] output))
    t (by change (MatrixTableWriter.run MatrixTableInterlace.entryProgram
      MatrixTableInterlaceEntry.start MatrixTableInterlaceEntry.initial t _).l = none
          rw [he]; rfl)
  change run u (writerFrame MatrixTableInterlaceSize.initial size _) =
    writerFrame MatrixTableInterlaceSize.initial size
      (MatrixTableWriter.run MatrixTableInterlace.entryProgram
        MatrixTableInterlaceEntry.start MatrixTableInterlaceEntry.initial t _) at hr
  rw [he] at hr
  exact ⟨u,hu.trans ht,v,hr⟩

theorem size_input_frame (blocks rows cols : ℕ) (source output : List Bool) :
    sizeFrame (MatrixTableInterlaceEntry.initial,none)
      (writerData rows cols source output [] []).contents
      (MatrixTableInterlaceSize.cfg (some MatrixTableInterlaceSize.start)
        MatrixTableInterlaceSize.initial (List.replicate blocks true)
        (List.replicate rows true) (List.replicate cols true) [] [] [] [] []) =
    bridgeCfg start blocks rows cols source output [] [] [] [] := by
  rfl

theorem size_output_frame (blocks rows cols : ℕ) (source output : List Bool) :
    sizeFrame (MatrixTableInterlaceEntry.initial,none)
      (writerData rows cols source output [] []).contents
      (MatrixTableInterlaceSize.cfg none MatrixTableInterlaceSize.initial
        (List.replicate blocks true) (List.replicate rows true)
        (List.replicate cols true) (List.replicate (blocks*rows) true)
        (List.replicate (cols^blocks) true) [] [] []) =
    bridgeCfg (.inr (.inl .moveRows)) blocks rows cols source output
      (List.replicate (blocks*rows) true)
      (List.replicate (cols^blocks) true) [] [] := by
  rfl

theorem writer_input_frame (blocks rows cols : ℕ) (source output : List Bool) :
    writerFrame MatrixTableInterlaceSize.initial
      (sizeBank blocks rows cols [] [])
      (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
        (MatrixTableInterlaceEntry.initial,none)
        (MatrixTableWriter.ready
          (MatrixTableInterlace.persistentBank rows cols source)
          (blocks*rows) (cols^blocks) 0 0 0 0 [] output)) =
    cfg (some writerStart) initial (sizeBank blocks rows cols [] [])
      (writerData rows cols source output
        (List.replicate (blocks*rows) true)
        (List.replicate (cols^blocks) true)).contents := by
  unfold writerFrame renameCfg liftCfg cfg writerStart initial writerData
    MatrixTableWriter.ready MatrixTableWriter.Data.contents
  congr 1
  funext k
  cases k with
  | inl k => rfl
  | inr k =>
      cases k with
      | inl k =>
          cases k with
          | inl k => fin_cases k <;> rfl
          | inr k => fin_cases k <;> rfl
      | inr k => cases k <;> rfl

def totalBound (blocks rows cols sourceLength : ℕ) : ℕ :=
  MatrixTableInterlaceSize.sizeBound blocks rows cols +
    ((blocks*rows+1)+(cols^blocks+1)) +
    MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
      (MatrixTableInterlace.uniformBound blocks rows cols sourceLength)

/-- One fixed transition table starts with the three unary counts in its
size bank and the literal old table in its writer bank; it physically
prepares both output dimensions, transfers them, and writes every interlace
cell. No entry or size oracle is used. -/
theorem combined_table (blocks rows cols : ℕ) (source output : List Bool) :
    ∃ t ≤ totalBound blocks rows cols source.length, ∃ v,
      run t (bridgeCfg start blocks rows cols source output [] [] [] []) =
      writerFrame MatrixTableInterlaceSize.initial
        (sizeBank blocks rows cols [] [])
        (MatrixTableWriter.cfg none v
          (MatrixTableWriter.ready
            (MatrixTableInterlace.persistentBank rows cols source)
            (blocks*rows) (cols^blocks) 0 0 0 0 []
            (MatrixTableWriter.tableWord
              (MatrixTableInterlaceCodes.entry rows cols source)
              (cols^blocks) 0 (blocks*rows) ++ output))) := by
  obtain ⟨t₁,ht₁,he₁⟩ := size_phase blocks rows cols
    (MatrixTableInterlaceEntry.initial,none)
    (writerData rows cols source output [] []).contents
  rw [size_input_frame, size_output_frame] at he₁
  have h₁ := run_add he₁ ((blocks*rows+1)+(cols^blocks+1))
  rw [bridge_run] at h₁
  obtain ⟨t₂,ht₂,v,he₂⟩ := writer_phase blocks rows cols source output
    (sizeBank blocks rows cols [] [])
  rw [writer_input_frame] at he₂
  have h₂ := run_add h₁ t₂
  rw [he₂] at h₂
  refine ⟨(t₁+((blocks*rows+1)+(cols^blocks+1)))+t₂, ?_, v, h₂⟩
  unfold totalBound
  omega

set_option maxHeartbeats 1000000 in
-- The final arithmetic estimate expands two previously proved cost bounds.
theorem totalBound_polynomial (blocks rows cols sourceLength : ℕ) :
    totalBound blocks rows cols sourceLength ≤
      1024*(blocks+rows+cols+sourceLength+blocks*rows+cols^blocks+1)^4 := by
  let s := blocks+rows+cols+sourceLength+blocks*rows+cols^blocks+1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hr : blocks*rows ≤ s := by dsimp [s]; omega
  have hc : cols^blocks ≤ s := by dsimp [s]; omega
  have hsmall : blocks+rows+cols+blocks*rows+cols^blocks+1 ≤ s := by
    dsimp [s]; omega
  have hsize := (MatrixTableInterlaceSize.sizeBound_polynomial
    blocks rows cols).trans
    (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hsmall 2))
  have hwriter := MatrixTableInterlace.interlace_bound_polynomial
    blocks rows cols sourceLength
  change MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
    (MatrixTableInterlace.uniformBound blocks rows cols sourceLength) ≤
      512*s^4 at hwriter
  have hs2 : 1 ≤ s^2 := by nlinarith
  have hs4 : 1 ≤ s^4 := by nlinarith
  have hs_to4 : s ≤ s^4 := by
    have h : s ≤ s^2 := by nlinarith [Nat.mul_le_mul (le_refl s) hs]
    nlinarith [Nat.mul_le_mul (le_refl (s^2)) hs2]
  have hs2_to4 : s^2 ≤ s^4 := by
    nlinarith [Nat.mul_le_mul (le_refl (s^2)) hs2]
  change MatrixTableInterlaceSize.sizeBound blocks rows cols +
    ((blocks*rows+1)+(cols^blocks+1)) +
    MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
      (MatrixTableInterlace.uniformBound blocks rows cols sourceLength) ≤
    1024*s^4
  omega

/-- Under the explicit row and mixed-radix column codings, the literal
output of the single combined controller is the mathematical classical
interlace of the supplied Boolean matrix. -/
theorem combined_rowMajor (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) (output : List Bool) :
    ∃ t ≤ totalBound blocks rows cols (MatrixMaterialization.rowMajor f).length,
      ∃ v,
        run t (bridgeCfg start blocks rows cols
          (MatrixMaterialization.rowMajor f) output [] [] [] []) =
        writerFrame MatrixTableInterlaceSize.initial
          (sizeBank blocks rows cols [] [])
          (MatrixTableWriter.cfg none v
            (MatrixTableWriter.ready
              (MatrixTableInterlace.persistentBank rows cols
                (MatrixMaterialization.rowMajor f))
              (blocks*rows) (cols^blocks) 0 0 0 0 []
              (MatrixMaterialization.rowMajor
                (MatrixTableInterlace.interlaced (blocks := blocks) f) ++ output))) := by
  obtain ⟨t,ht,v,he⟩ := combined_table blocks rows cols
    (MatrixMaterialization.rowMajor f) output
  refine ⟨t,ht,v,?_⟩
  simpa only [MatrixTableWriter.tableWord_eq_rowMajor
    (blocks*rows) (cols^blocks)
    (MatrixTableInterlaceCodes.entry rows cols (MatrixMaterialization.rowMajor f))
    (MatrixTableInterlace.interlaced (blocks := blocks) f)
    (MatrixTableInterlace.entry_rowMajor blocks rows cols f)] using he

end EthInapproximability.CurrentPaper.MatrixTableInterlaceCombined
