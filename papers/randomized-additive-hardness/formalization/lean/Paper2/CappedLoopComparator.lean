import Paper2.CappedBlockTransfer
import Paper2.CappedTicketMachine
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
Physical fixed-control capped rejection loop for Paper 2 v12 Appendix D.
The source rejection semantics are in `Paper2.CappedSampler`. This realizes
one elementary draw, not adaptive multi-draw generation or input preparation.
-/

namespace Paper2.CappedLoop.Comparator

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineSubroutine
abbrev BLabel := EthInapproximability.CurrentPaper.ProtocolBoundedUnary.Label
abbrev BControl := EthInapproximability.CurrentPaper.ProtocolBoundedUnary.Control

inductive Label where
  | start | read | restoreWidth | restoreBits
  | copyCap | restoreCap | compare (l : BLabel)
  | decision | clearTicket | clearCap | clearOut
  deriving DecidableEq, Fintype

abbrev Control := BControl

def cmpIdx : Fin 4 → Fin 10
  | 0 => 4
  | 1 => 7
  | 2 => 8
  | _ => 9

def liftCmpStmt : TM2.Stmt (fun _ : Fin 4 => Bool) BLabel Control →
    TM2.Stmt (fun _ : Fin 10 => Bool) Label Control
  | .push k f next => .push (cmpIdx k) f (liftCmpStmt next)
  | .peek k f next => .peek (cmpIdx k) f (liftCmpStmt next)
  | .pop k f next => .pop (cmpIdx k) f (liftCmpStmt next)
  | .load f next => .load f (liftCmpStmt next)
  | .branch f yes no => .branch f (liftCmpStmt yes) (liftCmpStmt no)
  | .goto f => .goto (fun v => .compare (f v))
  | .halt => .goto (fun _ => .decision)

def program : Label → TM2.Stmt (fun _ : Fin 10 => Bool) Label Control
  | .start =>
      pop 5 (fun s attempt => (attempt, s.2))
        (branch (fun s => s.1.isSome)
          (load (fun s => (none, s.2)) (goto (fun _ => .read)))
          halt)
  | .read =>
      pop 1 (fun s width => (width, s.2))
        (branch (fun s => s.1.isSome)
          (pop 0 (fun s bit => (bit, s.2))
            (branch (fun s => s.1.isSome)
              (push 2 (fun _ => true)
                (push 3 (fun s => s.1.getD false) (goto (fun _ => .read))))
              halt))
          (goto (fun _ => .restoreWidth)))
  | .restoreWidth =>
      pop 2 (fun s width => (width, s.2))
        (branch (fun s => s.1.isSome)
          (push 1 (fun _ => true) (goto (fun _ => .restoreWidth)))
          (goto (fun _ => .restoreBits)))
  | .restoreBits =>
      pop 3 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (push 4 (fun s => s.1.getD false) (goto (fun _ => .restoreBits)))
          (load (fun _ => (none, false)) (goto (fun _ => .copyCap))))
  | .copyCap =>
      pop 6 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (push 7 (fun _ => true)
            (push 8 (fun _ => true) (goto (fun _ => .copyCap))))
          (goto (fun _ => .restoreCap)))
  | .restoreCap =>
      pop 8 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (push 6 (fun _ => true) (goto (fun _ => .restoreCap)))
          (goto (fun _ => .compare .zeroScan)))
  | .compare l => liftCmpStmt
      (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.program l)
  | .decision =>
      peek 9 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.getD false)
          halt
          (goto (fun _ => .clearTicket)))
  | .clearTicket =>
      pop 4 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (goto (fun _ => .clearTicket))
          (goto (fun _ => .clearCap)))
  | .clearCap =>
      pop 7 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (goto (fun _ => .clearCap))
          (goto (fun _ => .clearOut)))
  | .clearOut =>
      pop 9 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (goto (fun _ => .clearOut))
          (load (fun _ => (none, false)) (goto (fun _ => .start))))

def bank (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    Fin 10 → List Bool :=
  fun k => if k = 0 then tape else if k = 1 then width else
    if k = 2 then widthWork else if k = 3 then bitsWork else
      if k = 4 then ticket else if k = 5 then attempts else
        if k = 6 then savedCap else if k = 7 then cap else
          if k = 8 then cmpWork else out

def cfg (l : Option Label) (v : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.Cfg (fun _ : Fin 10 => Bool) Label Control :=
  ⟨l, v, bank tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem copy_cons (s : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .copyCap) s tape width widthWork bitsWork ticket attempts
        (true :: savedCap) cap cmpWork out) =
    some (cfg (some .copyCap) (some true, s.2) tape width widthWork bitsWork ticket
      attempts savedCap (true :: cap) (true :: cmpWork) out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem copy_nil (s : Control)
    (tape width widthWork bitsWork ticket attempts cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .copyCap) s tape width widthWork bitsWork ticket attempts
        [] cap cmpWork out) =
    some (cfg (some .restoreCap) (none, s.2) tape width widthWork bitsWork ticket
      attempts [] cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem restore_cons (s : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .restoreCap) s tape width widthWork bitsWork ticket attempts
        savedCap cap (true :: cmpWork) out) =
    some (cfg (some .restoreCap) (some true, s.2) tape width widthWork bitsWork ticket
      attempts (true :: savedCap) cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (s : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap out : List Bool) :
    TM2.step program
      (cfg (some .restoreCap) s tape width widthWork bitsWork ticket attempts
        savedCap cap [] out) =
    some (cfg (some (.compare .zeroScan)) (none, s.2)
      tape width widthWork bitsWork ticket attempts
      savedCap cap [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem unary_comm (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem start_cons (s : Control)
    (tape width savedCap cap cmpWork out attempts : List Bool) :
    TM2.step program (cfg (some .start) s tape width [] [] []
      (true :: attempts) savedCap cap cmpWork out) =
      some (cfg (some .read) (none, s.2) tape width [] [] []
        attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem read_cons (s : Control) (bit : Bool)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .read) s (bit :: tape) (true :: width) widthWork bitsWork
        ticket attempts savedCap cap cmpWork out) =
      some (cfg (some .read) (some bit, s.2) tape width
        (true :: widthWork) (bit :: bitsWork) ticket attempts
        savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem read_nil (s : Control)
    (tape widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .read) s tape [] widthWork bitsWork ticket attempts
        savedCap cap cmpWork out) =
      some (cfg (some .restoreWidth) (none, s.2) tape [] widthWork bitsWork
        ticket attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem width_cons (s : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .restoreWidth) s tape width (true :: widthWork) bitsWork
        ticket attempts savedCap cap cmpWork out) =
      some (cfg (some .restoreWidth) (some true, s.2) tape (true :: width)
        widthWork bitsWork ticket attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem width_nil (s : Control)
    (tape width bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .restoreWidth) s tape width [] bitsWork ticket attempts
        savedCap cap cmpWork out) =
      some (cfg (some .restoreBits) (none, s.2) tape width [] bitsWork ticket
        attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem bits_cons (s : Control) (bit : Bool)
    (tape width bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .restoreBits) s tape width [] (bit :: bitsWork) ticket
        attempts savedCap cap cmpWork out) =
      some (cfg (some .restoreBits) (some bit, s.2) tape width [] bitsWork
        (bit :: ticket) attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem bits_nil (s : Control)
    (tape width ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .restoreBits) s tape width [] [] ticket attempts
        savedCap cap cmpWork out) =
      some (cfg (some .copyCap) (none, false) tape width [] [] ticket attempts
        savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem read_phase (s : Control)
    (block tape widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    run (block.length + 1)
      (cfg (some .read) s (block ++ tape) (List.replicate block.length true)
        widthWork bitsWork ticket attempts savedCap cap cmpWork out) =
    cfg (some .restoreWidth) (none, s.2) tape []
      (List.replicate block.length true ++ widthWork)
      (block.reverse ++ bitsWork) ticket attempts savedCap cap cmpWork out := by
  induction block generalizing s widthWork bitsWork with
  | nil => simpa using (run_succ
      (read_nil s tape widthWork bitsWork ticket attempts savedCap cap cmpWork out) 0)
  | cons bit block ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [run_succ (read_cons s bit (block ++ tape) (List.replicate block.length true)
        widthWork bitsWork ticket attempts savedCap cap cmpWork out),
        ih (some bit, s.2)]
      simp only [List.reverse_cons, List.append_assoc]
      rw [unary_comm]
      simp

theorem width_phase (s : Control) (n : ℕ)
    (tape width bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    run (n + 1)
      (cfg (some .restoreWidth) s tape width (List.replicate n true)
        bitsWork ticket attempts savedCap cap cmpWork out) =
    cfg (some .restoreBits) (none, s.2) tape
      (List.replicate n true ++ width) [] bitsWork ticket attempts
      savedCap cap cmpWork out := by
  induction n generalizing s width with
  | zero => simpa using (run_succ
      (width_nil s tape width bitsWork ticket attempts savedCap cap cmpWork out) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [run_succ (width_cons s tape width (List.replicate n true) bitsWork
        ticket attempts savedCap cap cmpWork out), ih (some true, s.2)]
      rw [unary_comm]
      simp

theorem bits_phase (s : Control)
    (bitsWork tape width ticket attempts savedCap cap cmpWork out : List Bool) :
    run (bitsWork.length + 1)
      (cfg (some .restoreBits) s tape width [] bitsWork ticket attempts
        savedCap cap cmpWork out) =
    cfg (some .copyCap) (none, false) tape width [] []
      (bitsWork.reverse ++ ticket) attempts savedCap cap cmpWork out := by
  induction bitsWork generalizing s ticket with
  | nil => simpa using (run_succ
      (bits_nil s tape width ticket attempts savedCap cap cmpWork out) 0)
  | cons bit bitsWork ih =>
      rw [show (bit :: bitsWork).length + 1 = (bitsWork.length + 1) + 1 by simp,
        run_succ (bits_cons s bit tape width bitsWork ticket attempts
          savedCap cap cmpWork out), ih (some bit, s.2)]
      simp [List.reverse_cons, List.append_assoc]

theorem transfer_to_copyCap (block tape attempts savedCap : List Bool) :
    run (3 * block.length + 4)
      (cfg (some .start) (none, false) (block ++ tape)
        (List.replicate block.length true) [] [] []
        (true :: attempts) savedCap [] [] []) =
    cfg (some .copyCap) (none, false) tape
      (List.replicate block.length true) [] [] block attempts savedCap [] [] [] := by
  have hstart := run_succ
    (start_cons (none, false) (block ++ tape) (List.replicate block.length true)
      savedCap [] [] [] attempts) 0
  have hread := read_phase (none, false) block tape [] [] [] attempts savedCap [] [] []
  simp only [List.append_nil] at hread
  have hw := width_phase (none, false) block.length tape [] block.reverse [] attempts
    savedCap [] [] []
  simp only [List.append_nil] at hw
  have hb := bits_phase (none, false) block.reverse tape
    (List.replicate block.length true) [] attempts savedCap [] [] []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hb
  have h1 := (run_add hstart (block.length + 1)).trans hread
  have h2 := (run_add h1 (block.length + 1)).trans hw
  have h3 := (run_add h2 (block.length + 1)).trans hb
  simpa only [show 1 + (block.length + 1) + (block.length + 1) +
      (block.length + 1) = 3 * block.length + 4 by omega] using h3

theorem copy_phase (s : Control) (n : ℕ)
    (tape width widthWork bitsWork ticket attempts cap cmpWork out : List Bool) :
    run (n + 1)
      (cfg (some .copyCap) s tape width widthWork bitsWork ticket attempts
        (List.replicate n true) cap cmpWork out) =
    cfg (some .restoreCap) (none, s.2) tape width widthWork bitsWork ticket
      attempts [] (List.replicate n true ++ cap)
        (List.replicate n true ++ cmpWork) out := by
  induction n generalizing s cap cmpWork with
  | zero => simpa using (run_succ
      (copy_nil s tape width widthWork bitsWork ticket attempts cap cmpWork out) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [run_succ (copy_cons s tape width widthWork bitsWork ticket attempts
        (List.replicate n true) cap cmpWork out), ih (some true, s.2)]
      rw [unary_comm, unary_comm]
      simp

theorem restore_phase (s : Control) (n : ℕ)
    (tape width widthWork bitsWork ticket attempts savedCap cap out : List Bool) :
    run (n + 1)
      (cfg (some .restoreCap) s tape width widthWork bitsWork ticket attempts
        savedCap cap (List.replicate n true) out) =
    cfg (some (.compare .zeroScan)) (none, s.2)
      tape width widthWork bitsWork ticket attempts
      (List.replicate n true ++ savedCap) cap [] out := by
  induction n generalizing s savedCap with
  | zero => simpa using (run_succ
      (restore_nil s tape width widthWork bitsWork ticket attempts savedCap cap out) 0)
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [run_succ (restore_cons s tape width widthWork bitsWork ticket attempts
        savedCap cap (List.replicate n true) out), ih (some true, s.2)]
      rw [unary_comm]
      simp

theorem copy_saved_cap (n : ℕ)
    (tape width widthWork bitsWork ticket attempts out : List Bool) :
    run (2 * n + 2)
      (cfg (some .copyCap) (none, false) tape width widthWork bitsWork ticket attempts
        (List.replicate n true) [] [] out) =
    cfg (some (.compare .zeroScan)) (none, false)
      tape width widthWork bitsWork ticket attempts
      (List.replicate n true) (List.replicate n true) [] out := by
  have hc := copy_phase (none, false) n tape width widthWork bitsWork ticket attempts [] [] out
  simp only [List.append_nil] at hc
  have hr := restore_phase (none, false) n tape width widthWork bitsWork ticket attempts []
    (List.replicate n true) out
  simp only [List.append_nil] at hr
  have h := (run_add hc (n + 1)).trans hr
  simpa only [show (n + 1) + (n + 1) = 2 * n + 2 by omega] using h

def cmpReplace (base : Fin 10 → List Bool) (part : Fin 4 → List Bool) :
    Fin 10 → List Bool :=
  fun k => if k = 4 then part 0 else if k = 7 then part 1 else
    if k = 8 then part 2 else if k = 9 then part 3 else base k

theorem cmpReplace_read (base : Fin 10 → List Bool) (part : Fin 4 → List Bool)
    (k : Fin 4) : cmpReplace base part (cmpIdx k) = part k := by
  fin_cases k <;> rfl

theorem cmpReplace_update (base : Fin 10 → List Bool) (part : Fin 4 → List Bool)
    (k : Fin 4) (value : List Bool) :
    Function.update (cmpReplace base part) (cmpIdx k) value =
      cmpReplace base (Function.update part k value) := by
  funext j
  fin_cases k <;> fin_cases j <;>
    simp [cmpReplace, cmpIdx, Function.update]

def injectCmp (base : Fin 10 → List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) BLabel Control) :
    TM2.Cfg (fun _ : Fin 10 => Bool) Label Control :=
  ⟨some (c.l.elim .decision .compare), c.var, cmpReplace base c.stk⟩

theorem liftCmpStmt_stepAux (s : TM2.Stmt (fun _ : Fin 4 => Bool) BLabel Control)
    (v : Control) (part : Fin 4 → List Bool) (base : Fin 10 → List Bool) :
    TM2.stepAux (liftCmpStmt s) v (cmpReplace base part) =
      injectCmp base (TM2.stepAux s v part) := by
  induction s generalizing v part with
  | push k f next ih =>
      simp only [liftCmpStmt, TM2.stepAux, cmpReplace_read]
      rw [cmpReplace_update]
      exact ih _ _
  | peek k f next ih =>
      simp only [liftCmpStmt, TM2.stepAux, cmpReplace_read]
      exact ih _ _
  | pop k f next ih =>
      simp only [liftCmpStmt, TM2.stepAux, cmpReplace_read]
      rw [cmpReplace_update]
      exact ih _ _
  | load f next ih =>
      simpa only [liftCmpStmt, TM2.stepAux] using ih (f v) part
  | branch f yes no ihy ihn =>
      by_cases h : f v = true
      · simpa [liftCmpStmt, TM2.stepAux, h] using ihy v part
      · simpa [liftCmpStmt, TM2.stepAux, h] using ihn v part
  | goto f => rfl
  | halt => rfl

theorem cmp_advance (base : Fin 10 → List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) BLabel Control) (hc : c.l ≠ none) :
    advance program (injectCmp base c) =
      injectCmp base (advance
        EthInapproximability.CurrentPaper.ProtocolBoundedUnary.program c) := by
  cases c with
  | mk l v part =>
      cases l with
      | none => exact (hc rfl).elim
      | some l =>
          simpa only [advance, injectCmp, Option.map_some, TM2.step,
            Option.getD_some, program] using
            liftCmpStmt_stepAux
              (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.program l)
              v part base

theorem cmp_run_until (base : Fin 10 → List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) BLabel Control) (n : ℕ)
    (h : ∀ k < n,
      (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.run k c).l ≠ none) :
    run n (injectCmp base c) =
      injectCmp base (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.run n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run, EthInapproximability.CurrentPaper.ProtocolBoundedUnary.run] at ih ⊢
      have hn : (((advance
          EthInapproximability.CurrentPaper.ProtocolBoundedUnary.program)^[n]) c).l ≠
          none := h n (by omega)
      rw [Function.iterate_succ_apply', ih (fun k hk => h k (by omega))]
      rw [cmp_advance base _ hn, Function.iterate_succ_apply']

theorem cmp_outputs (base : Fin 10 → List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) BLabel Control) (bound : ℕ)
    (hhalt : (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.run bound c).l = none) :
    ∃ n ≤ bound,
      run n (injectCmp base c) =
        injectCmp base (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.run bound c) := by
  obtain ⟨n, hn, _, heq, hfirst⟩ := first_halt_cfg
    EthInapproximability.CurrentPaper.ProtocolBoundedUnary.program c bound hhalt
  exact ⟨n, hn,
    (cmp_run_until base c n hfirst).trans (congrArg (injectCmp base) heq)⟩

theorem cmp_foreign_read (base : Fin 10 → List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) BLabel Control)
    (j : Fin 10) (hj : j ≠ 4 ∧ j ≠ 7 ∧ j ≠ 8 ∧ j ≠ 9) :
    (injectCmp base c).stk j = base j := by
  simp [injectCmp, cmpReplace, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]

/-- The complete bounded comparator runs on the shared ten-stack bank.
Its foreign stacks (flat tape, width, transfer scratch, attempts and saved
cap) are exactly those in `base` throughout the lifted run. -/
theorem comparator_bounded_framed (base : Fin 10 → List Bool)
    (q cap out : List Bool) :
    ∃ t c,
      t ≤ (cap.length + 1) * (4 * q.length + 5) ∧
      run t (injectCmp base
        (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.cfg
          (some .zeroScan) (none, false) q cap [] out)) =
        injectCmp base c ∧
      c.l = none ∧
      c.stk 3 = EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result
        q cap out ∧
      (c.stk 0).length = q.length ∧ c.stk 2 = [] ∧
      (c.stk 1).length ≤ cap.length := by
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    EthInapproximability.CurrentPaper.ProtocolBoundedUnary.bounded_run_framed q cap out
  obtain ⟨n, hn, hrun⟩ := cmp_outputs base _ t (by rw [hr]; exact hhalt)
  exact ⟨n, c, hn.trans ht, hrun.trans (congrArg (injectCmp base) hr),
    hhalt, hout, hlen, hwork, hcaplen⟩

theorem comparator_begin (tape width widthWork bitsWork ticket attempts savedCap cap :
    List Bool) :
    cfg (some (.compare .zeroScan)) (none, false)
      tape width widthWork bitsWork ticket attempts savedCap cap [] [] =
    injectCmp (bank tape width widthWork bitsWork ticket attempts savedCap cap [] [])
      (EthInapproximability.CurrentPaper.ProtocolBoundedUnary.cfg
        (some .zeroScan) (none, false) ticket cap [] []) := by
  apply congrArg
    (fun cells : Fin 10 → List Bool =>
      (⟨some (.compare .zeroScan), (none, false), cells⟩ :
        TM2.Cfg (fun _ : Fin 10 => Bool) Label Control))
  funext k
  fin_cases k <;> rfl

/-- The saved unary alphabet cap is copied by literal push/pop steps and
restored before the lifted comparator begins. The printed comparison output
and worst-case step count come from the original B machine on the same banks.
Foreign readbacks are fixed by `injectCmp` and `cmp_foreign_read`. -/
theorem copy_cap_then_compare (n : ℕ)
    (tape width widthWork bitsWork ticket attempts : List Bool) :
    ∃ t c,
      t ≤ 2 * n + 2 + (n + 1) * (4 * ticket.length + 5) ∧
      run t (cfg (some .copyCap) (none, false)
        tape width widthWork bitsWork ticket attempts
        (List.replicate n true) [] [] []) =
      injectCmp
        (bank tape width widthWork bitsWork ticket attempts
          (List.replicate n true) (List.replicate n true) [] []) c ∧
      c.l = none ∧
      c.stk 3 = EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result
        ticket (List.replicate n true) [] ∧
      (c.stk 0).length = ticket.length ∧ c.stk 2 = [] ∧
      (c.stk 1).length ≤ n := by
  let base := bank tape width widthWork bitsWork ticket attempts
    (List.replicate n true) (List.replicate n true) [] []
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    comparator_bounded_framed base ticket (List.replicate n true) []
  refine ⟨2 * n + 2 + t, c, ?_, ?_, hhalt, hout, hlen, hwork, ?_⟩
  · simpa using Nat.add_le_add_left ht (2 * n + 2)
  · have hc := copy_saved_cap n tape width widthWork bitsWork ticket attempts []
    rw [run_add hc t, comparator_begin]
    exact hr
  · simpa using hcaplen

/-- One entire physical attempt on the literal nested fair-bit tape:
counter decrement, `b` bit transfers, cap copying/restoration, and the
bounded binary-versus-unary comparator. The endpoint is on one shared
ten-stack TM2 program. Rejection cleanup and repeat are separate. -/
theorem one_complete_comparison (b R n : ℕ)
    (tape : Paper2.CappedSampler.BitTape b (R + 1)) :
    ∃ t c,
      t ≤ 3 * b + 4 + (2 * n + 2 +
        (n + 1) * (4 * b + 5)) ∧
      run t
        (cfg (some .start) (none, false)
          (BlockTransfer.flatBitTape b (R + 1) tape)
          (List.replicate b true) [] [] []
          (List.replicate (R + 1) true)
          (List.replicate n true) [] [] []) =
      injectCmp
        (bank (BlockTransfer.flatBitTape b R tape.2)
          (List.replicate b true) [] [] (List.ofFn tape.1)
          (List.replicate R true)
          (List.replicate n true) (List.replicate n true) [] []) c ∧
      c.l = none ∧
      c.stk 3 = EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result
        (List.ofFn tape.1) (List.replicate n true) [] ∧
      (c.stk 0).length = b ∧ c.stk 2 = [] ∧
      (c.stk 1).length ≤ n := by
  let block := List.ofFn tape.1
  let rest := BlockTransfer.flatBitTape b R tape.2
  have htransfer : run (3 * b + 4)
      (cfg (some .start) (none, false)
        (BlockTransfer.flatBitTape b (R + 1) tape)
        (List.replicate b true) [] [] []
        (List.replicate (R + 1) true)
        (List.replicate n true) [] [] []) =
      cfg (some .copyCap) (none, false) rest
        (List.replicate b true) [] [] block
        (List.replicate R true) (List.replicate n true) [] [] [] := by
    simpa [BlockTransfer.flatBitTape, block, rest] using
      transfer_to_copyCap block rest (List.replicate R true)
        (List.replicate n true)
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    copy_cap_then_compare n rest (List.replicate b true) [] [] block
      (List.replicate R true)
  refine ⟨3 * b + 4 + t, c, ?_, ?_, hhalt, hout, ?_, hwork, hcaplen⟩
  · simpa [block, List.length_ofFn] using Nat.add_le_add_left ht (3 * b + 4)
  · exact (run_add htransfer t).trans hr
  · simpa [block] using hlen

private theorem decision_false (s : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .decision) s tape width widthWork bitsWork ticket attempts
        savedCap cap cmpWork (false :: out)) =
    some (cfg (some .clearTicket) (some false, s.2)
      tape width widthWork bitsWork ticket attempts savedCap cap cmpWork
      (false :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem decision_true (s : Control)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .decision) s tape width widthWork bitsWork ticket attempts
        savedCap cap cmpWork (true :: out)) =
    some (cfg none (some true, s.2)
      tape width widthWork bitsWork ticket attempts savedCap cap cmpWork
      (true :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem clear_ticket_cons (s : Control) (bit : Bool)
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .clearTicket) s tape width widthWork bitsWork (bit :: ticket)
        attempts savedCap cap cmpWork out) =
    some (cfg (some .clearTicket) (some bit, s.2)
      tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem clear_ticket_nil (s : Control)
    (tape width widthWork bitsWork attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .clearTicket) s tape width widthWork bitsWork []
        attempts savedCap cap cmpWork out) =
    some (cfg (some .clearCap) (none, s.2)
      tape width widthWork bitsWork [] attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem clear_cap_cons (s : Control) (bit : Bool)
    (tape width widthWork bitsWork attempts savedCap cap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .clearCap) s tape width widthWork bitsWork []
        attempts savedCap (bit :: cap) cmpWork out) =
    some (cfg (some .clearCap) (some bit, s.2)
      tape width widthWork bitsWork [] attempts savedCap cap cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem clear_cap_nil (s : Control)
    (tape width widthWork bitsWork attempts savedCap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .clearCap) s tape width widthWork bitsWork []
        attempts savedCap [] cmpWork out) =
    some (cfg (some .clearOut) (none, s.2)
      tape width widthWork bitsWork [] attempts savedCap [] cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem clear_out_cons (s : Control) (bit : Bool)
    (tape width widthWork bitsWork attempts savedCap cmpWork out : List Bool) :
    TM2.step program
      (cfg (some .clearOut) s tape width widthWork bitsWork []
        attempts savedCap [] cmpWork (bit :: out)) =
    some (cfg (some .clearOut) (some bit, s.2)
      tape width widthWork bitsWork [] attempts savedCap [] cmpWork out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem clear_out_nil (s : Control)
    (tape width widthWork bitsWork attempts savedCap cmpWork : List Bool) :
    TM2.step program
      (cfg (some .clearOut) s tape width widthWork bitsWork []
        attempts savedCap [] cmpWork []) =
    some (cfg (some .start) (none, false)
      tape width widthWork bitsWork [] attempts savedCap [] cmpWork []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem clear_ticket_phase (s : Control)
    (ticket tape width widthWork bitsWork attempts savedCap cap cmpWork out : List Bool) :
    run (ticket.length + 1)
      (cfg (some .clearTicket) s tape width widthWork bitsWork ticket attempts
        savedCap cap cmpWork out) =
    cfg (some .clearCap) (none, s.2)
      tape width widthWork bitsWork [] attempts savedCap cap cmpWork out := by
  induction ticket generalizing s with
  | nil => simpa using (run_succ
      (clear_ticket_nil s tape width widthWork bitsWork attempts savedCap cap cmpWork out) 0)
  | cons bit ticket ih =>
      rw [show (bit :: ticket).length + 1 = (ticket.length + 1) + 1 by simp,
        run_succ (clear_ticket_cons s bit tape width widthWork bitsWork ticket
          attempts savedCap cap cmpWork out), ih (some bit, s.2)]

theorem clear_cap_phase (s : Control)
    (cap tape width widthWork bitsWork attempts savedCap cmpWork out : List Bool) :
    run (cap.length + 1)
      (cfg (some .clearCap) s tape width widthWork bitsWork [] attempts
        savedCap cap cmpWork out) =
    cfg (some .clearOut) (none, s.2)
      tape width widthWork bitsWork [] attempts savedCap [] cmpWork out := by
  induction cap generalizing s with
  | nil => simpa using (run_succ
      (clear_cap_nil s tape width widthWork bitsWork attempts savedCap cmpWork out) 0)
  | cons bit cap ih =>
      rw [show (bit :: cap).length + 1 = (cap.length + 1) + 1 by simp,
        run_succ (clear_cap_cons s bit tape width widthWork bitsWork attempts
          savedCap cap cmpWork out), ih (some bit, s.2)]

theorem clear_out_phase (s : Control)
    (out tape width widthWork bitsWork attempts savedCap cmpWork : List Bool) :
    run (out.length + 1)
      (cfg (some .clearOut) s tape width widthWork bitsWork [] attempts
        savedCap [] cmpWork out) =
    cfg (some .start) (none, false)
      tape width widthWork bitsWork [] attempts savedCap [] cmpWork [] := by
  induction out generalizing s with
  | nil => simpa using (run_succ
      (clear_out_nil s tape width widthWork bitsWork attempts savedCap cmpWork) 0)
  | cons bit out ih =>
      rw [show (bit :: out).length + 1 = (out.length + 1) + 1 by simp,
        run_succ (clear_out_cons s bit tape width widthWork bitsWork attempts
          savedCap cmpWork out), ih (some bit, s.2)]

theorem rejected_cleanup (s : Control)
    (ticket cap out tape width widthWork bitsWork attempts savedCap : List Bool) :
    run (ticket.length + cap.length + out.length + 5)
      (cfg (some .decision) s tape width widthWork bitsWork ticket attempts
        savedCap cap [] (false :: out)) =
    cfg (some .start) (none, false)
      tape width widthWork bitsWork [] attempts savedCap [] [] [] := by
  have hd := run_succ
    (decision_false s tape width widthWork bitsWork ticket attempts
      savedCap cap [] out) 0
  have ht := clear_ticket_phase (some false, s.2) ticket tape width widthWork
    bitsWork attempts savedCap cap [] (false :: out)
  have hc := clear_cap_phase (none, s.2) cap tape width widthWork bitsWork
    attempts savedCap [] (false :: out)
  have ho := clear_out_phase (none, s.2) (false :: out) tape width widthWork
    bitsWork attempts savedCap []
  have h1 := (run_add hd (ticket.length + 1)).trans ht
  have h2 := (run_add h1 (cap.length + 1)).trans hc
  have h3 := (run_add h2 ((false :: out).length + 1)).trans ho
  simpa only [List.length_cons, show 1 + (ticket.length + 1) +
      (cap.length + 1) + (out.length + 1 + 1) =
      ticket.length + cap.length + out.length + 5 by omega] using h3

theorem cmp_endpoint_cfg
    (tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out :
      List Bool)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) BLabel Control)
    (hhalt : c.l = none) (hwork : c.stk 2 = []) :
    injectCmp
      (bank tape width widthWork bitsWork ticket attempts savedCap cap cmpWork out) c =
    cfg (some .decision) c.var tape width widthWork bitsWork (c.stk 0)
      attempts savedCap (c.stk 1) [] (c.stk 3) := by
  rcases c with ⟨l, v, part⟩
  cases l with
  | none =>
      dsimp [injectCmp, cfg]
      congr 1
      funext k
      fin_cases k <;> simp [cmpReplace, bank]
      simpa using hwork
  | some l => exact (Option.some_ne_none l hhalt).elim

/-- If the first bit-tape block is out of range, one actual shared-bank
attempt (including comparator and physical cleanup) reaches exactly the
initial loop shape for `R` remaining blocks. This is a pointwise statement:
the failure predicate concerns the decoded ticket, not the source promise. -/
theorem one_rejected_retry (b R n : ℕ)
    (tape : Paper2.CappedSampler.BitTape b (R + 1))
    (hfail : n <
      EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
        (List.ofFn tape.1)) :
    ∃ t,
      t ≤ 3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) +
        (b + 2 * n + 5) ∧
      run t
        (cfg (some .start) (none, false)
          (BlockTransfer.flatBitTape b (R + 1) tape)
          (List.replicate b true) [] [] []
          (List.replicate (R + 1) true)
          (List.replicate n true) [] [] []) =
      cfg (some .start) (none, false)
        (BlockTransfer.flatBitTape b R tape.2)
        (List.replicate b true) [] [] []
        (List.replicate R true)
        (List.replicate n true) [] [] [] := by
  obtain ⟨t, c, ht, hr, hhalt, hout, hlen, hwork, hcaplen⟩ :=
    one_complete_comparison b R n tape
  let rest := BlockTransfer.flatBitTape b R tape.2
  let cap := List.replicate n true
  let base := bank rest (List.replicate b true) [] [] (List.ofFn tape.1)
    (List.replicate R true) cap cap [] []
  have hout' : c.stk 3 = false :: List.replicate n true := by
    rw [hout]
    have hle : n ≤
        EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
          (List.ofFn tape.1) := by omega
    simp [EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result,
      Nat.not_le.mpr hfail, min_eq_right hle]
  have hcfg : injectCmp base c =
      cfg (some .decision) c.var rest (List.replicate b true) [] [] (c.stk 0)
        (List.replicate R true) cap (c.stk 1) [] (false :: List.replicate n true) := by
    rw [cmp_endpoint_cfg rest (List.replicate b true) [] []
      (List.ofFn tape.1) (List.replicate R true) cap cap [] [] c hhalt hwork,
      hout']
  have hcleanup := rejected_cleanup c.var (c.stk 0) (c.stk 1)
    (List.replicate n true) rest (List.replicate b true) [] []
    (List.replicate R true) cap
  let u := (c.stk 0).length + (c.stk 1).length + n + 5
  refine ⟨t + u, ?_, ?_⟩
  · dsimp [u]
    omega
  · rw [run_add hr u, hcfg]
    simpa [u, rest, cap] using hcleanup

/-- A successful first attempt halts at the decision label after one more
literal step. The output is a unary encoding of the exact accepted ticket,
not just an acceptance probability. -/
theorem one_accepted_halts (b R n : ℕ)
    (tape : Paper2.CappedSampler.BitTape b (R + 1))
    (hsuccess :
      EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
        (List.ofFn tape.1) ≤ n) :
    ∃ t c,
      t ≤ 3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) + 1 ∧
      run t
        (cfg (some .start) (none, false)
          (BlockTransfer.flatBitTape b (R + 1) tape)
          (List.replicate b true) [] [] []
          (List.replicate (R + 1) true)
          (List.replicate n true) [] [] []) = c ∧
      c.l = none ∧
      c.stk 0 = BlockTransfer.flatBitTape b R tape.2 ∧
      c.stk 1 = List.replicate b true ∧
      c.stk 5 = List.replicate R true ∧
      c.stk 6 = List.replicate n true ∧
      c.stk 9 = true :: List.replicate
        (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
          (List.ofFn tape.1)) true := by
  obtain ⟨t, c, ht, hr, hhalt, hout, _hlen, hwork, _hcaplen⟩ :=
    one_complete_comparison b R n tape
  let rest := BlockTransfer.flatBitTape b R tape.2
  let cap := List.replicate n true
  let base := bank rest (List.replicate b true) [] [] (List.ofFn tape.1)
    (List.replicate R true) cap cap [] []
  have hout' : c.stk 3 = true :: List.replicate
      (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
        (List.ofFn tape.1)) true := by
    rw [hout]
    simp [EthInapproximability.CurrentPaper.ProtocolBoundedUnary.result,
      hsuccess]
  have hcfg : injectCmp base c =
      cfg (some .decision) c.var rest (List.replicate b true) [] [] (c.stk 0)
        (List.replicate R true) cap (c.stk 1) [] (true :: List.replicate
          (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
            (List.ofFn tape.1)) true) := by
    rw [cmp_endpoint_cfg rest (List.replicate b true) [] []
      (List.ofFn tape.1) (List.replicate R true) cap cap [] [] c hhalt hwork,
      hout']
  let finalCfg := cfg none (some true, c.var.2) rest (List.replicate b true) [] []
    (c.stk 0) (List.replicate R true) cap (c.stk 1) []
    (true :: List.replicate
      (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
        (List.ofFn tape.1)) true)
  refine ⟨t + 1, finalCfg, by omega, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [run_add hr 1, hcfg]
  simpa [finalCfg] using (run_succ
    (decision_true c.var rest (List.replicate b true) [] [] (c.stk 0)
      (List.replicate R true) cap (c.stk 1) []
      (List.replicate
        (EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
          (List.ofFn tape.1)) true)) 0)

def attemptBound (D : ℕ) : ℕ :=
  let b := Nat.clog 2 D
  let n := D - 1
  3 * b + 4 + (2 * n + 2 + (n + 1) * (4 * b + 5)) +
    (b + 2 * n + 5)

def machineOutput (c : TM2.Cfg (fun _ : Fin 10 => Bool) Label Control) :
    Option ℕ :=
  if (c.stk 9).head? = some true then some (c.stk 9).tail.length else none

theorem runBits_succ (D R : ℕ)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) (R + 1)) :
    Paper2.CappedSampler.runBits D (R + 1) tape =
      if h : (Paper2.CappedSampler.bitsTicketEquiv (Nat.clog 2 D) tape.1).val < D
      then some ⟨_, h⟩ else Paper2.CappedSampler.runBits D R tape.2 := rfl

theorem empty_attempts_halt (tape width savedCap : List Bool) :
    run 1 (cfg (some .start) (none, false) tape width [] [] [] []
      savedCap [] [] []) =
      cfg none (none, false) tape width [] [] [] [] savedCap [] [] [] := by
  simpa using (run_succ (show TM2.step program
      (cfg (some .start) (none, false) tape width [] [] [] [] savedCap [] [] []) =
      some (cfg none (none, false) tape width [] [] [] [] savedCap [] [] []) by
        simp [TM2.step, TM2.stepAux, program, cfg, bank]) 0)

/-- Total pointwise capped rejection loop on an actual finite Boolean-stack
machine. The only public parameters in the theorem are represented in its
input stacks: flat fair-bit tape, unary width, unary attempt counter, and
saved unary alphabet cap. The fixed control has no `Fin b`, `Fin R`, or
`Fin D` state. `attemptBound` is polynomial in the physical unary alphabet
size, not asserted polynomial in a binary encoding of `D`. -/
theorem capped_loop_correct (D R : ℕ) (hD : 0 < D)
    (tape : Paper2.CappedSampler.BitTape (Nat.clog 2 D) R) :
    ∃ t c,
      t ≤ R * attemptBound D + 1 ∧
      run t (cfg (some .start) (none, false)
        (BlockTransfer.flatBitTape (Nat.clog 2 D) R tape)
        (List.replicate (Nat.clog 2 D) true) [] [] []
        (List.replicate R true) (List.replicate (D - 1) true) [] [] []) = c ∧
      c.l = none ∧
      machineOutput c =
        (Paper2.CappedSampler.runBits D R tape).map Fin.val := by
  induction R with
  | zero =>
      let c := cfg none (none, false) [] (List.replicate (Nat.clog 2 D) true)
        [] [] [] [] (List.replicate (D - 1) true) [] [] []
      refine ⟨1, c, by simp, ?_, rfl, ?_⟩
      · simpa [BlockTransfer.flatBitTape, c] using
          empty_attempts_halt []
            (List.replicate (Nat.clog 2 D) true)
            (List.replicate (D - 1) true)
      · simp [machineOutput, c, Paper2.CappedSampler.runBits,
          Paper2.CappedSampler.run, cfg, bank]
  | succ R ih =>
      let b := Nat.clog 2 D
      let n := D - 1
      let q := EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
        (List.ofFn tape.1)
      have hv : q = (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val := by
        simpa [q, b, Paper2.CappedTicketMachine.ticketWord] using
          Paper2.CappedTicketMachine.bitsValue_ofFn tape.1
      by_cases hs : q ≤ n
      · obtain ⟨t, c, ht, hr, hhalt, _htape, _hwidth, _hattempts, _hsaved,
          hout⟩ := one_accepted_halts b R n tape hs
        refine ⟨t, c, ?_, hr, hhalt, ?_⟩
        · dsimp [attemptBound, b, n] at *
          nlinarith
        · have hlt : (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [runBits_succ, dif_pos hlt]
          simp [machineOutput, hout]
          simpa [q, b] using hv
      · have hf : n < q := by omega
        obtain ⟨t₁, ht₁, hr₁⟩ := one_rejected_retry b R n tape hf
        obtain ⟨t₂, c, ht₂, hr₂, hhalt, hout⟩ := ih tape.2
        refine ⟨t₁ + t₂, c, ?_, ?_, hhalt, ?_⟩
        · dsimp [attemptBound, b, n] at *
          nlinarith
        · exact (run_add hr₁ t₂).trans hr₂
        · have hnot : ¬ (Paper2.CappedSampler.bitsTicketEquiv b tape.1).val < D := by
            omega
          rw [runBits_succ, dif_neg hnot]
          exact hout



end Paper2.CappedLoop.Comparator
