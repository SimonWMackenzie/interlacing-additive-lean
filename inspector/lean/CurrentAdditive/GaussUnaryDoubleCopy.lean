import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A literal finite controller copies one unary input into two empty
destinations while restoring the input. -/

namespace CurrentAdditive.GaussUnaryDoubleCopy

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 4
inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def bank (source first second temp : List Bool) : Stack → List Bool :=
  ![source, first, second, temp]

def cfg (l : Option Label) (v : Control)
    (source first second temp : List Bool) : Config :=
  ⟨l, v, bank source first second temp⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 3 (fun _ => true)
          (push 1 (fun _ => true)
            (push 2 (fun _ => true) (goto (fun _ => .scan)))))
        (goto (fun _ => .restore)))
  | .restore => pop 3 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true) (goto (fun _ => .restore)))
        halt)

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

theorem run_add (t u : Nat) (q : Config) :
    run (t+u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

theorem scan_cons (source first second temp : List Bool) (v : Control) :
    run 1 (cfg (some .scan) v (true :: source) first second temp) =
      cfg (some .scan) (some true) source (true :: first)
        (true :: second) (true :: temp) := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem scan_nil (first second temp : List Bool) (v : Control) :
    run 1 (cfg (some .scan) v [] first second temp) =
      cfg (some .restore) none [] first second temp := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, bank]

theorem restore_cons (source first second temp : List Bool) (v : Control) :
    run 1 (cfg (some .restore) v source first second (true :: temp)) =
      cfg (some .restore) (some true) (true :: source) first second temp := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem restore_nil (source first second : List Bool) (v : Control) :
    run 1 (cfg (some .restore) v source first second []) =
      cfg none none source first second [] := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg, bank]

private theorem replicate_append_cons (n : Nat) (xs : List Bool) :
    List.replicate n true ++ true :: xs =
      true :: (List.replicate n true ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem scan_all (n : Nat) (v : Control)
    (first second temp : List Bool) :
    run n (cfg (some .scan) v (List.replicate n true)
      first second temp) =
    cfg (some .scan) (if n = 0 then v else some true) []
      (List.replicate n true ++ first)
      (List.replicate n true ++ second)
      (List.replicate n true ++ temp) := by
  induction n generalizing v first second temp with
  | zero => simp [run, cfg, bank]
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n+1 = 1+n by omega, run_add,
        scan_cons (List.replicate n true) first second temp v]
      rw [ih]
      simp [replicate_append_cons]

theorem restore_all (n : Nat) (v : Control)
    (source first second : List Bool) :
    run n (cfg (some .restore) v source first second
      (List.replicate n true)) =
    cfg (some .restore) (if n = 0 then v else some true)
      (List.replicate n true ++ source) first second [] := by
  induction n generalizing v source with
  | zero => simp [run, cfg, bank]
  | succ n ih =>
      simp only [List.replicate_succ]
      rw [show n+1 = 1+n by omega, run_add,
        restore_cons source first second (List.replicate n true) v]
      rw [ih]
      simp [replicate_append_cons]

theorem run_unary (n : Nat) :
    run (2*n+2) (cfg (some .scan) none
      (List.replicate n true) [] [] []) =
      cfg none none (List.replicate n true)
        (List.replicate n true) (List.replicate n true) [] := by
  have htime : 2*n+2 = n+1+n+1 := by omega
  rw [htime, run_add (n+1+n) 1, run_add (n+1) n,
    run_add n 1, scan_all]
  simp only [List.append_nil]
  rw [scan_nil, restore_all]
  simp only [List.append_nil]
  exact restore_nil _ _ _ _

#print axioms run_unary

end CurrentAdditive.GaussUnaryDoubleCopy
