import Paper2.CappedSampler
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary

/-!
Locked Paper 2 v12 Appendix D. This is a fixed finite-control
TM2 subroutine for physically transferring one b-bit block from a flat tape
to a ticket stack. Its width is a unary input stack, not machine control.
It preserves a separate physical unary attempt-counter stack for a later loop.
-/

namespace Paper2.CappedLoop.BlockTransfer

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | start | read | restoreWidth | restoreBits
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control
  | .start =>
      pop 5 (fun _ attempt => attempt)
        (branch (fun attempt => attempt.isSome)
          (load (fun _ => none) (goto (fun _ => .read)))
          halt)
  | .read =>
      pop 1 (fun _ w => w)
        (branch (fun w => w.isSome)
          (pop 0 (fun _ bit => bit)
            (branch (fun bit => bit.isSome)
              (push 2 (fun _ => true)
                (push 3 (fun bit => bit.getD false) (goto (fun _ => .read))))
              halt))
          (goto (fun _ => .restoreWidth)))
  | .restoreWidth =>
      pop 2 (fun _ w => w)
        (branch (fun w => w.isSome)
          (push 1 (fun _ => true) (goto (fun _ => .restoreWidth)))
          (goto (fun _ => .restoreBits)))
  | .restoreBits =>
      pop 3 (fun _ bit => bit)
        (branch (fun bit => bit.isSome)
          (push 4 (fun bit => bit.getD false) (goto (fun _ => .restoreBits)))
          halt)

def stackContents (tape width widthWork bitsWork ticket attempts : List Bool) :
    Fin 6 → List Bool :=
  fun k => if k = 0 then tape else if k = 1 then width else
    if k = 2 then widthWork else if k = 3 then bitsWork else
      if k = 4 then ticket else attempts

@[simp] private theorem stack_zero (a b c d e f : List Bool) :
    stackContents a b c d e f 0 = a := rfl
@[simp] private theorem stack_one (a b c d e f : List Bool) :
    stackContents a b c d e f 1 = b := rfl
@[simp] private theorem stack_two (a b c d e f : List Bool) :
    stackContents a b c d e f 2 = c := rfl
@[simp] private theorem stack_three (a b c d e f : List Bool) :
    stackContents a b c d e f 3 = d := rfl
@[simp] private theorem stack_four (a b c d e f : List Bool) :
    stackContents a b c d e f 4 = e := rfl
@[simp] private theorem stack_five (a b c d e f : List Bool) :
    stackContents a b c d e f 5 = f := rfl

def cfg (l : Option Label) (v : Control)
    (tape width widthWork bitsWork ticket attempts : List Bool) :
    TM2.Cfg (fun _ : Fin 6 => Bool) Label Control :=
  ⟨l, v, stackContents tape width widthWork bitsWork ticket attempts⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem read_cons (v : Control) (bit : Bool) (tape width widthWork bitsWork ticket attempts : List Bool) :
    TM2.step program
      (cfg (some .read) v (bit :: tape) (true :: width) widthWork bitsWork ticket attempts) =
    some (cfg (some .read) (some bit) tape width (true :: widthWork)
      (bit :: bitsWork) ticket attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem read_done (v : Control) (tape widthWork bitsWork ticket attempts : List Bool) :
    TM2.step program (cfg (some .read) v tape [] widthWork bitsWork ticket attempts) =
      some (cfg (some .restoreWidth) none tape [] widthWork bitsWork ticket attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem width_cons (v : Control) (tape width widthWork bitsWork ticket attempts : List Bool) :
    TM2.step program
      (cfg (some .restoreWidth) v tape width (true :: widthWork) bitsWork ticket attempts) =
      some (cfg (some .restoreWidth) (some true) tape (true :: width) widthWork
        bitsWork ticket attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem width_done (v : Control) (tape width bitsWork ticket attempts : List Bool) :
    TM2.step program (cfg (some .restoreWidth) v tape width [] bitsWork ticket attempts) =
      some (cfg (some .restoreBits) none tape width [] bitsWork ticket attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem bits_cons (v : Control) (bit : Bool) (tape width bitsWork ticket attempts : List Bool) :
    TM2.step program
      (cfg (some .restoreBits) v tape width [] (bit :: bitsWork) ticket attempts) =
      some (cfg (some .restoreBits) (some bit) tape width [] bitsWork
        (bit :: ticket) attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem bits_done (v : Control) (tape width ticket attempts : List Bool) :
    TM2.step program (cfg (some .restoreBits) v tape width [] [] ticket attempts) =
      some (cfg none none tape width [] [] ticket attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem start_cons (tape width attempts : List Bool) :
    TM2.step program (cfg (some .start) none tape width [] [] [] (true :: attempts)) =
      some (cfg (some .read) none tape width [] [] [] attempts) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

theorem start_empty_aborts (tape width : List Bool) :
    run 1 (cfg (some .start) none tape width [] [] [] []) =
      cfg none none tape width [] [] [] [] := by
  simpa using run_succ (show TM2.step program
      (cfg (some .start) none tape width [] [] [] []) =
      some (cfg none none tape width [] [] [] []) by
        simp [TM2.step, TM2.stepAux, program, cfg]) 0

private theorem unary_comm (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem read_prefix (v : Control) (block tape widthWork bitsWork ticket attempts : List Bool) :
    run (block.length + 1)
      (cfg (some .read) v (block ++ tape) (List.replicate block.length true)
        widthWork bitsWork ticket attempts) =
      cfg (some .restoreWidth) none tape []
        (List.replicate block.length true ++ widthWork)
        (block.reverse ++ bitsWork) ticket attempts := by
  induction block generalizing v widthWork bitsWork with
  | nil => simpa using run_succ (read_done v tape widthWork bitsWork ticket attempts) 0
  | cons bit block ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [run_succ (read_cons v bit (block ++ tape) (List.replicate block.length true)
          widthWork bitsWork ticket attempts), ih (some bit)]
      simp only [List.reverse_cons, List.append_assoc]
      rw [unary_comm]
      simp

theorem restore_width (v : Control) (n : ℕ) (tape width bitsWork ticket attempts : List Bool) :
    run (n + 1)
      (cfg (some .restoreWidth) v tape width (List.replicate n true)
        bitsWork ticket attempts) =
      cfg (some .restoreBits) none tape (List.replicate n true ++ width) []
        bitsWork ticket attempts := by
  induction n generalizing v width with
  | zero => simpa using run_succ (width_done v tape width bitsWork ticket attempts) 0
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        run_succ (width_cons v tape width (List.replicate n true) bitsWork ticket attempts),
        ih (some true)]
      rw [unary_comm]
      simp

theorem restore_bits (v : Control) (bitsWork tape width ticket attempts : List Bool) :
    run (bitsWork.length + 1)
      (cfg (some .restoreBits) v tape width [] bitsWork ticket attempts) =
      cfg none none tape width [] [] (bitsWork.reverse ++ ticket) attempts := by
  induction bitsWork generalizing v ticket with
  | nil => simpa using run_succ (bits_done v tape width ticket attempts) 0
  | cons bit bitsWork ih =>
      rw [show (bit :: bitsWork).length + 1 = (bitsWork.length + 1) + 1 by simp,
        run_succ (bits_cons v bit tape width bitsWork ticket attempts), ih (some bit)]
      simp [List.reverse_cons, List.append_assoc]

/-- The literal first `block` is consumed, the remaining tape and unary
attempt counter are untouched, width is restored, all scratch stacks are
empty, and bit order is preserved. Every transfer and cleanup step is charged. -/
theorem transfer_block (block tape attempts : List Bool) :
    run (3 * block.length + 3)
      (cfg (some .read) none (block ++ tape)
        (List.replicate block.length true) [] [] [] attempts) =
      cfg none none tape (List.replicate block.length true) [] [] block attempts := by
  have hread := read_prefix none block tape [] [] [] attempts
  simp only [List.append_nil] at hread
  have hw := restore_width none block.length tape [] block.reverse [] attempts
  simp only [List.append_nil] at hw
  have hb := restore_bits none block.reverse tape (List.replicate block.length true) [] attempts
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hb
  have hpre := (run_add hread (block.length + 1)).trans hw
  have hall := (run_add hpre (block.length + 1)).trans hb
  simpa only [show (block.length + 1) + (block.length + 1) + (block.length + 1) =
      3 * block.length + 3 by omega] using hall

/-- The literal fair-bit tape uses consecutive little-endian attempt words.
No semantic random-access array stands between this list and the machine. -/
def flatBitTape (b : ℕ) : (R : ℕ) →
    Paper2.CappedSampler.BitTape b R → List Bool
  | 0, _ => []
  | R + 1, tape => List.ofFn tape.1 ++ flatBitTape b R tape.2

theorem flatBitTape_length (b R : ℕ)
    (tape : Paper2.CappedSampler.BitTape b R) :
    (flatBitTape b R tape).length = b * R := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp [flatBitTape, ih, Nat.mul_succ, Nat.add_comm]

theorem transfer_bitTape_head (b R : ℕ)
    (tape : Paper2.CappedSampler.BitTape b (R + 1))
    (attempts : List Bool) :
    run (3 * b + 3)
      (cfg (some .read) none (flatBitTape b (R + 1) tape)
        (List.replicate b true) [] [] [] attempts) =
      cfg none none (flatBitTape b R tape.2)
        (List.replicate b true) [] [] (List.ofFn tape.1) attempts := by
  simpa [flatBitTape] using
    transfer_block (List.ofFn tape.1) (flatBitTape b R tape.2) attempts

/-- A physical unary attempt symbol is removed before the next block is
transferred. This is the one-iteration front end, not yet a full repeating
controller or comparator. -/
theorem consume_attempt_and_transfer (b R : ℕ)
    (tape : Paper2.CappedSampler.BitTape b (R + 1))
    (attempts : List Bool) :
    run (3 * b + 4)
      (cfg (some .start) none (flatBitTape b (R + 1) tape)
        (List.replicate b true) [] [] [] (true :: attempts)) =
      cfg none none (flatBitTape b R tape.2)
        (List.replicate b true) [] [] (List.ofFn tape.1) attempts := by
  rw [show 3 * b + 4 = (3 * b + 3) + 1 by omega,
    run_succ (start_cons (flatBitTape b (R + 1) tape)
      (List.replicate b true) attempts)]
  simpa only using transfer_bitTape_head b R tape attempts





end Paper2.CappedLoop.BlockTransfer
