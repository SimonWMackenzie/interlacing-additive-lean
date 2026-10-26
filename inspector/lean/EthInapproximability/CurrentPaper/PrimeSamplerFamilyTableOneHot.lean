import EthInapproximability.CurrentPaper.MatrixStage4FamilyData

/-!
# Physical unary-index to one-hot field writer

The fixed four-stack machine consumes unary `index` and `width`, writes the
literal forward-order one-hot word, and clears its temporary counter. It
uses no finite-control enumeration of the index or desired output word.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerFamilyTableOneHot

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | start | subtract | tail | middle | front
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .start =>
      pop 1 (fun _ b => b)
        (branch Option.isSome (goto (fun _ => .subtract)) halt)
  | .subtract =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (pop 1 (fun _ b => b)
            (branch Option.isSome
              (push 2 (fun _ => true) (goto (fun _ => .subtract))) halt))
          (goto (fun _ => .tail)))
  | .tail =>
      pop 1 (fun _ b => b)
        (branch Option.isSome
          (push 3 (fun _ => false) (goto (fun _ => .tail)))
          (goto (fun _ => .middle)))
  | .middle => push 3 (fun _ => true) (goto (fun _ => .front))
  | .front =>
      pop 2 (fun _ b => b)
        (branch Option.isSome
          (push 3 (fun _ => false) (goto (fun _ => .front))) halt)

def cfg (l : Option Label) (v : Control)
    (index width saved output : List Bool) : Config :=
  ⟨l, v, ![index, width, saved, output]⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem start_step (index width saved output : List Bool) (v : Control) :
    advance program
      (cfg (some .start) v index (true :: width) saved output) =
    cfg (some .subtract) (some true) index width saved output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem subtract_step (index width saved output : List Bool) (v : Control) :
    advance program
      (cfg (some .subtract) v (true :: index) (true :: width) saved output) =
    cfg (some .subtract) (some true) index width (true :: saved) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem subtract_done (width saved output : List Bool) (v : Control) :
    advance program (cfg (some .subtract) v [] width saved output) =
    cfg (some .tail) none [] width saved output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem tail_step (index saved output : List Bool) (v : Control) :
    advance program (cfg (some .tail) v index (true :: saved) [] output) =
    cfg (some .tail) (some true) index saved [] (false :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem tail_done (index output : List Bool) (v : Control) :
    advance program (cfg (some .tail) v index [] [] output) =
    cfg (some .middle) none index [] [] output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem middle_step (index output : List Bool) (v : Control) :
    advance program (cfg (some .middle) v index [] [] output) =
    cfg (some .front) v index [] [] (true :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem front_step (index saved output : List Bool) (v : Control) :
    advance program (cfg (some .front) v index [] (true :: saved) output) =
    cfg (some .front) (some true) index [] saved (false :: output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem front_done (index output : List Bool) (v : Control) :
    advance program (cfg (some .front) v index [] [] output) =
    cfg none none index [] [] output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem run_after (c : Config) (s t : Nat) :
    run (s + t) c = run t (run s c) := by
  simp [run, show s + t = t + s by omega,
    Function.iterate_add_apply]

private theorem replicate_push (i : Nat) (b : Bool)
    (suffix : List Bool) :
    List.replicate i b ++ b :: suffix =
      b :: (List.replicate i b ++ suffix) := by
  calc
    _ = (List.replicate i b ++ [b]) ++ suffix := by
      simp [List.append_assoc]
    _ = List.replicate (i + 1) b ++ suffix := by
      rw [List.replicate_succ']
    _ = b :: (List.replicate i b ++ suffix) := by
      rw [List.replicate_succ]
      rfl

theorem subtract_run (i tail : Nat) (saved output : List Bool)
    (v : Control) :
    run i (cfg (some .subtract) v (List.replicate i true)
      (List.replicate (i + tail) true) saved output) =
    cfg (some .subtract) (if i = 0 then v else some true)
      [] (List.replicate tail true)
      (List.replicate i true ++ saved) output := by
  induction i generalizing saved v with
  | zero => simp [run, cfg]
  | succ i ih =>
      simp only [run, Function.iterate_succ_apply,
        List.replicate_succ, Nat.succ_add]
      rw [subtract_step]
      change run i (cfg (some .subtract) (some true)
        (List.replicate i true) (List.replicate (i + tail) true)
        (true :: saved) output) = _
      rw [ih]
      simp only [ite_self, Nat.succ_ne_zero, if_false, replicate_push, List.cons_append]

theorem tail_run (tail : Nat) (index output : List Bool) (v : Control) :
    run tail (cfg (some .tail) v index
      (List.replicate tail true) [] output) =
    cfg (some .tail) (if tail = 0 then v else some true)
      index [] [] (List.replicate tail false ++ output) := by
  induction tail generalizing output v with
  | zero => simp [run, cfg]
  | succ tail ih =>
      simp only [run, Function.iterate_succ_apply,
        List.replicate_succ]
      rw [tail_step]
      change run tail (cfg (some .tail) (some true) index
        (List.replicate tail true) [] (false :: output)) = _
      rw [ih]
      simp only [ite_self, Nat.succ_ne_zero, if_false, replicate_push, List.cons_append]

theorem front_run (i : Nat) (index output : List Bool) (v : Control) :
    run i (cfg (some .front) v index []
      (List.replicate i true) output) =
    cfg (some .front) (if i = 0 then v else some true)
      index [] [] (List.replicate i false ++ output) := by
  induction i generalizing output v with
  | zero => simp [run, cfg]
  | succ i ih =>
      simp only [run, Function.iterate_succ_apply,
        List.replicate_succ]
      rw [front_step]
      change run i (cfg (some .front) (some true) index []
        (List.replicate i true) (false :: output)) = _
      rw [ih]
      simp only [ite_self, Nat.succ_ne_zero, if_false, replicate_push, List.cons_append]

end EthInapproximability.CurrentPaper.PrimeSamplerFamilyTableOneHot
