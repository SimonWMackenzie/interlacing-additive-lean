import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Physical framing and parsing of one binary base-p digit

A remainder is LSB first. The writer puts a false terminator below its
`true, bit` pairs, so a sequence of divisions prepends the new, more
significant coefficient to the stream. The reader consumes precisely one
such frame and returns its bits LSB first. Both routines use a fixed two-bank
Boolean machine and linear time, including the zero digit's terminator.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitFrame

open Turing Turing.TM2.Stmt BitMachineEncoding

def marked (bits : List Bool) : List Bool :=
  bits.flatMap (fun b => [true, b])

def frame (lsbBits tail : List Bool) : List Bool :=
  marked lsbBits.reverse ++ false :: tail

theorem marked_cons (b : Bool) (bs : List Bool) :
    marked (b :: bs) = true :: b :: marked bs := rfl

theorem frame_cons (b : Bool) (bs tail : List Bool) :
    frame (b :: bs) tail = marked bs.reverse ++ [true,b,false] ++ tail := by
  simp [frame, marked, List.flatMap_append, List.reverse_cons, List.append_assoc]

namespace Writer

inductive Label where
  | start | scan
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .start => push 1 (fun _ => false) (goto (fun _ => .scan))
  | .scan => pop 0 (fun _ b => b)
      (branch (fun b => b.isSome)
        (push 1 (fun b => b.getD false)
          (push 1 (fun _ => true) (goto (fun _ => .scan))))
        halt)

def bank (source stream : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then source else stream

def cfg (l : Option Label) (s : Control) (source stream : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Control := ⟨l,s,bank source stream⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_start (source stream : List Bool) :
    TM2.step program (cfg (some .start) none source stream) =
      some (cfg (some .scan) none source (false :: stream)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_cons (b : Bool) (bs stream : List Bool) :
    TM2.step program (cfg (some .scan) none (b :: bs) stream) =
      some (cfg (some .scan) (some b) bs (true :: b :: stream)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_nil (stream : List Bool) :
    TM2.step program (cfg (some .scan) none [] stream) =
      some (cfg none none [] stream) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem scan_correct (bits stream : List Bool) :
    run (bits.length + 1) (cfg (some .scan) none bits stream) =
      cfg none none [] (marked bits.reverse ++ stream) := by
  induction bits generalizing stream with
  | nil => simpa [marked] using run_step (step_nil stream) 0
  | cons b bs ih =>
      rw [List.length_cons, run_step (step_cons b bs stream)]
      simpa [marked, List.flatMap_append, List.reverse_cons, List.append_assoc]
        using ih (true :: b :: stream)

theorem run_correct (bits stream : List Bool) :
    run (bits.length + 2) (cfg (some .start) none bits stream) =
      cfg none none [] (frame bits stream) := by
  rw [show bits.length + 2 = (bits.length + 1) + 1 by omega]
  rw [run_step (step_start bits stream)]
  simpa [frame, List.append_assoc] using scan_correct bits (false :: stream)

end Writer

namespace Reader

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .scan => pop 0 (fun _ marker => marker)
      (branch (fun marker => marker.getD false)
        (pop 0 (fun _ bit => bit)
          (push 1 (fun bit => bit.getD false) (goto (fun _ => .scan))))
        halt)

def bank (stream digit : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then stream else digit

def cfg (l : Option Label) (s : Control) (stream digit : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Control := ⟨l,s,bank stream digit⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_cons (b : Bool) (rest digit : List Bool) :
    TM2.step program (cfg (some .scan) none (true :: b :: rest) digit) =
      some (cfg (some .scan) (some b) rest (b :: digit)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_nil (rest digit : List Bool) :
    TM2.step program (cfg (some .scan) none (false :: rest) digit) =
      some (cfg none (some false) rest digit) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

theorem marked_run (bits rest digit : List Bool) :
    run (bits.length + 1)
      (cfg (some .scan) none (marked bits ++ false :: rest) digit) =
      cfg none (some false) rest (bits.reverse ++ digit) := by
  induction bits generalizing digit with
  | nil => simpa [marked] using run_step (step_nil rest digit) 0
  | cons b bs ih =>
      rw [List.length_cons, marked_cons]
      change run (bs.length + 1 + 1)
        (cfg (some .scan) none
          (true :: b :: (marked bs ++ false :: rest)) digit) = _
      rw [run_step (step_cons b (marked bs ++ false :: rest) digit)]
      simpa [List.reverse_cons, List.append_assoc] using ih (b :: digit)

theorem frame_run (bits rest digit : List Bool) :
    run (bits.length + 1) (cfg (some .scan) none (frame bits rest) digit) =
      cfg none (some false) rest (bits ++ digit) := by
  simpa [frame] using marked_run bits.reverse rest digit

end Reader

theorem frame_length (bits tail : List Bool) :
    (frame bits tail).length = 2 * bits.length + 1 + tail.length := by
  induction bits with
  | nil => simp [frame, marked, Nat.add_comm]
  | cons b bs ih =>
      simp [frame, marked, List.reverse_cons, List.flatMap_append,
        List.length_append]
      omega

end EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitFrame
