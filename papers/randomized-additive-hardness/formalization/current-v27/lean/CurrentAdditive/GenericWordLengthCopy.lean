import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A fixed three-stack machine copies the length of any Boolean word to
true-unary while restoring the original word. -/

namespace Paper2.GenericWordLengthCopy

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Option Bool)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun v => v.getD false)
          (push 1 (fun _ => true) (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun v => v.getD false) (goto (fun _ => .restore)))
        halt)

def cfg (l : Option Label) (v : Option Bool)
    (source dest scratch : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool) :=
  ⟨l, v, ![source, dest, scratch]⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :=
  ((advance program)^[t]) c

theorem run_add (t u : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :
    run (t + u) c = run u (run t c) := by
  simp only [run]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem scan_cons (v : Option Bool) (b : Bool)
    (source dest scratch : List Bool) :
    advance program (cfg (some .scan) v (b :: source) dest scratch) =
      cfg (some .scan) (some b) source (true :: dest) (b :: scratch) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_nil (v : Option Bool) (dest scratch : List Bool) :
    advance program (cfg (some .scan) v [] dest scratch) =
      cfg (some .restore) none [] dest scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem restore_cons (v : Option Bool) (b : Bool)
    (source dest scratch : List Bool) :
    advance program (cfg (some .restore) v source dest (b :: scratch)) =
      cfg (some .restore) (some b) (b :: source) dest scratch := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (v : Option Bool) (source dest : List Bool) :
    advance program (cfg (some .restore) v source dest []) =
      cfg none none source dest [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem replicate_shift (n : ℕ) (dest : List Bool) :
    List.replicate n true ++ true :: dest =
      true :: (List.replicate n true ++ dest) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (true :: ·) ih

theorem scan_run (source dest scratch : List Bool) (v : Option Bool) :
    run (source.length + 1) (cfg (some .scan) v source dest scratch) =
      cfg (some .restore) none []
        (List.replicate source.length true ++ dest)
        (source.reverse ++ scratch) := by
  induction source generalizing dest scratch v with
  | nil =>
    simpa only [List.length_nil, zero_add, List.replicate_zero,
      List.nil_append, List.reverse_nil, Function.iterate_one, run] using
      scan_nil v dest scratch
  | cons b source ih =>
    rw [List.length_cons, show source.length + 1 + 1 = 1 + (source.length + 1) by omega,
      run_add]
    change run (source.length + 1)
      (advance program (cfg (some .scan) v (b :: source) dest scratch)) = _
    rw [scan_cons]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc,
      List.replicate_succ, List.cons_append]
    congr 1
    exact replicate_shift source.length dest

theorem restore_run (scratch source dest : List Bool) (v : Option Bool) :
    run (scratch.length + 1) (cfg (some .restore) v source dest scratch) =
      cfg none none (scratch.reverse ++ source) dest [] := by
  induction scratch generalizing source v with
  | nil =>
    simpa only [List.length_nil, zero_add, List.reverse_nil,
      List.nil_append, Function.iterate_one, run] using
      restore_nil v source dest
  | cons b scratch ih =>
    rw [List.length_cons, show scratch.length + 1 + 1 = 1 + (scratch.length + 1) by omega,
      run_add]
    change run (scratch.length + 1)
      (advance program (cfg (some .restore) v source dest (b :: scratch))) = _
    rw [restore_cons]
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem length_copy (source : List Bool) :
    run (2 * source.length + 2) (cfg (some .scan) none source [] []) =
      cfg none none source (List.replicate source.length true) [] := by
  have h1 := scan_run source [] [] none
  simp only [List.append_nil] at h1
  have h2 := restore_run source.reverse []
    (List.replicate source.length true) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  have htime : 2 * source.length + 2 = (source.length + 1) + (source.length + 1) := by omega
  rw [htime, run_add, h1, h2]

#print axioms length_copy

end Paper2.GenericWordLengthCopy
