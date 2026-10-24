import EthInapproximability.CurrentPaper.MatrixSourceColumnMachine
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Physical source-row setup and evaluation

Source: frozen v8 Appendix B, `thm:paper-materialization`, source-vector
entry evaluation. Copy and restore the literal row number, add one to the
prefix counter, and invoke the actual column gather/count controller.
Column decoding supplies the header separately; no rank or answer is input.
-/

namespace EthInapproximability.CurrentPaper.MatrixSourceEntry

set_option maxHeartbeats 0

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine
open MatrixMaterializationMachine
open MatrixSourceColumnMachine

abbrev Stack := Fin 11 ⊕ Fin 2
abbrev Label := Gather.Label ⊕ Bool
abbrev Control := Gather.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def start : Label := .inr false
def initialControl (s : MatrixSourceColumnMachine.Control) : Control :=
  (((MatrixStrideGather.baseControl,false),s),none)
def finalControl : Control := initialControl {}

def setPop (v : Control) (b : Option Bool) : Control := (v.1,b)
def go (b : Bool) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  goto (fun _ => .inr b)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt none (Gather.program l)
  | .inr false => pop (.inr 0) setPop
      (branch (fun v => v.2.isSome)
        (push (.inr 1) (fun v => v.2.getD false)
          (push (.inl 7) (fun _ => true) (go false))) (go true))
  | .inr true => pop (.inr 1) setPop
      (branch (fun v => v.2.isSome)
        (push (.inr 0) (fun v => v.2.getD false) (go true))
        (push (.inl 7) (fun _ => true)
          (goto (fun _ => .inl (.inl (.inr .test))))))

def cfg (l : Option Label) (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (idx src buffer count stride out row temp : List Bool) : Config :=
  ⟨l, (((MatrixStrideGather.baseControl,false),s),flag),
    Sum.elim (Gather.cfg none s idx src buffer count stride out).stk (![row,temp])⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) := Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) : run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

theorem scan_cons (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (b : Bool) (row idx src buffer count stride out temp : List Bool) :
    advance program (cfg (some (.inr false)) s flag idx src buffer count stride out (b::row) temp) =
      cfg (some (.inr false)) s (some b) idx src buffer (true::count) stride out row (b::temp) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Gather.cfg,
    Sum.elim_inr, Matrix.cons_val_zero, go, setPop, List.head?_cons,
    List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;>
    norm_num only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
  all_goals split_ifs <;> simp_all

theorem scan_nil (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (idx src buffer count stride out temp : List Bool) :
    advance program (cfg (some (.inr false)) s flag idx src buffer count stride out [] temp) =
      cfg (some (.inr true)) s none idx src buffer count stride out [] temp := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Gather.cfg,
    Sum.elim_inr, Matrix.cons_val_zero, go, setPop, List.head?_nil,
    List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;>
    norm_num only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
  all_goals split_ifs <;> simp_all

theorem restore_cons (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (b : Bool) (row idx src buffer count stride out temp : List Bool) :
    advance program (cfg (some (.inr true)) s flag idx src buffer count stride out row (b::temp)) =
      cfg (some (.inr true)) s (some b) idx src buffer count stride out (b::row) temp := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Gather.cfg,
    Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, go, setPop, List.head?_cons,
    List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;>
    norm_num only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
  all_goals split_ifs <;> simp_all

theorem restore_nil (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (row idx src buffer count stride out : List Bool) :
    advance program (cfg (some (.inr true)) s flag idx src buffer count stride out row []) =
      cfg (some (.inl (.inl (.inr .test)))) s none idx src buffer (true::count) stride out row [] := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, Gather.cfg,
    Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, go, setPop, List.head?_nil,
    List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;>
    norm_num only [Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_succ, reduceCtorEq]
  all_goals split_ifs <;> simp_all

theorem scan_run (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (row idx src buffer count stride out temp : List Bool) :
    run (row.length+1)
      (cfg (some (.inr false)) s flag idx src buffer count stride out row temp) =
      cfg (some (.inr true)) s none idx src buffer
        (List.replicate row.length true ++ count) stride out [] (row.reverse ++ temp) := by
  induction row generalizing flag count temp with
  | nil =>
      rw [show [].length+1 = 0+1 from rfl, run_succ, scan_nil]
      rfl
  | cons b row ih =>
      rw [List.length_cons, run_succ, scan_cons, ih]
      have hr : List.replicate row.length true ++ true::count =
          true :: (List.replicate row.length true ++ count) := by
        induction row.length with
        | zero => rfl
        | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]
      simp only [List.replicate_succ, List.reverse_cons, List.append_assoc,
        hr, List.cons_append, List.nil_append]

theorem restore_run (s : MatrixSourceColumnMachine.Control) (flag : Option Bool)
    (row idx src buffer count stride out temp : List Bool) :
    run (temp.length+1)
      (cfg (some (.inr true)) s flag idx src buffer count stride out row temp) =
      cfg (some (.inl (.inl (.inr .test)))) s none idx src buffer
        (true::count) stride out (temp.reverse ++ row) [] := by
  induction temp generalizing flag row with
  | nil =>
      rw [show [].length+1 = 0+1 from rfl, run_succ, restore_nil]
      rfl
  | cons b temp ih =>
      rw [List.length_cons, run_succ, restore_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem prepare_run (s : MatrixSourceColumnMachine.Control)
    (row idx src stride out : List Bool) :
    run (2*row.length+2) (cfg (some (.inr false)) s none idx src [] [] stride out row []) =
      cfg (some (.inl (.inl (.inr .test)))) s none idx src []
        (List.replicate (row.length+1) true) stride out row [] := by
  rw [show 2*row.length+2 = (row.length+1)+(row.length+1) by omega, run_add, scan_run]
  simp only [List.append_nil]
  have h := restore_run s none [] idx src [] (List.replicate row.length true) stride out row.reverse
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil,
    List.replicate_succ] using h

theorem gather_cfg (l : Option Gather.Label) (s : MatrixSourceColumnMachine.Control)
    (idx src buffer count stride out row : List Bool) :
    liftCfg (none : Option Bool) (none : Option Bool) (![row,[]] : Fin 2 → List Bool)
      (Gather.cfg l s idx src buffer count stride out) =
      cfg (l.map Sum.inl) s none idx src buffer count stride out row [] := by
  cases l <;> rfl

/-- No prefix length is preloaded: the controller constructs it from the
preserved row input. The supplied header is the column decoder's output. -/
theorem source_run {n d N₁ : ℕ}
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    ∃ t ≤ (i.val+1) *
        (3*((c.2 0).1.val+(i.val+1)*d)+3*(n*d)+2*d+12)+3*i.val+5,
      run t (cfg (some (.inr false)) (header (decide (ExactConstruction.aligned c)) c.1)
        none (List.replicate (c.2 0).1.val true) (MatrixMaterialization.rowMajor v)
        [] [] (List.replicate d true) out (List.replicate i.val true) []) =
      cfg none {} none (List.replicate ((c.2 0).1.val+(i.val+1)*d) true)
        (MatrixMaterialization.rowMajor v) [] [] (List.replicate d true)
        (ExactConstruction.vectorEntry v cap i c :: out) (List.replicate i.val true) [] := by
  obtain ⟨tg, ht, hg⟩ := Gather.source_run v cap i c out
  have hh : (Gather.run tg (Gather.cfg (some (.inl (.inr .test)))
      (header (decide (ExactConstruction.aligned c)) c.1)
      (List.replicate (c.2 0).1.val true) (MatrixMaterialization.rowMajor v) []
      (List.replicate (i.val+1) true) (List.replicate d true) out)).l = none := by
    rw [hg]
    rfl
  obtain ⟨t, htg, he⟩ := lift_outputs Gather.program program none (fun _ => rfl)
    (none : Option Bool) (![List.replicate i.val true,[]] : Fin 2 → List Bool)
    (Gather.cfg (some (.inl (.inr .test))) (header (decide (ExactConstruction.aligned c)) c.1)
      (List.replicate (c.2 0).1.val true) (MatrixMaterialization.rowMajor v) []
      (List.replicate (i.val+1) true) (List.replicate d true) out) tg hh
  change ((advance program)^[t]) _ = liftCfg _ _ _ (Gather.run tg _) at he
  rw [hg, gather_cfg, gather_cfg] at he
  refine ⟨2*i.val+2+t, by omega, ?_⟩
  rw [show 2*i.val+2+t = (2*(List.replicate i.val true).length+2)+t by simp,
    run_add, prepare_run]
  simpa only [List.length_replicate] using he

end EthInapproximability.CurrentPaper.MatrixSourceEntry
