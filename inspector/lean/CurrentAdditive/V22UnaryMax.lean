import EthInapproximability.CurrentPaper.MatrixUnaryArithmetic

/-! A physical maximum of two canonical delimiter-free unary operands.
The source operands are separated by one false bit. No numerical operation
is performed in finite control. -/
namespace V22UnaryMax
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where | first | second | clear
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Bool
  | .first => .pop 0 (fun _ b => b.getD false)
      (.branch id
        (.push 1 (fun _ => true) (.push 2 (fun _ => true) (.goto fun _ => .first)))
        (.goto fun _ => .second))
  | .second => .pop 0 (fun _ b => b.isSome)
      (.branch id
        (.pop 1 (fun _ b => b.isSome)
          (.branch id (.goto fun _ => .second)
            (.push 2 (fun _ => true) (.goto fun _ => .second))))
        (.goto fun _ => .clear))
  | .clear => .pop 1 (fun _ b => b.isSome)
      (.branch id (.goto fun _ => .clear) (.load (fun _ => false) .halt))

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool
def cfg (l : Option Label) (v : Bool) (a c o : List Bool) : Config :=
  ⟨l,v,![a,c,o]⟩
def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add (t u : ℕ) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simp only [run, Nat.add_comm t u, Function.iterate_add_apply]

private theorem first_cons (q c o : List Bool) (v : Bool) :
    advance program (cfg (some .first) v (true::q) c o) =
      cfg (some .first) true q (true::c) (true::o) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext i; fin_cases i <;> rfl

private theorem first_stop (q c o : List Bool) (v : Bool) :
    advance program (cfg (some .first) v (false::q) c o) =
      cfg (some .second) false q c o := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext i; fin_cases i <;> rfl

private theorem first_run (n m c o : ℕ) (v : Bool) :
    run (n+1) (cfg (some .first) v
      (MatrixUnaryArithmetic.encodeInput n m)
      (List.replicate c true) (List.replicate o true)) =
    cfg (some .second) false (List.replicate m true)
      (List.replicate (n+c) true) (List.replicate (n+o) true) := by
  induction n generalizing c o v with
  | zero => simpa [run, MatrixUnaryArithmetic.encodeInput] using first_stop (List.replicate m true) (List.replicate c true) (List.replicate o true) v
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      change run (n+1) (advance program (cfg (some .first) v
        (true :: MatrixUnaryArithmetic.encodeInput n m) _ _)) = _
      rw [first_cons]
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (c+1) (o+1) true

private theorem second_cons_pos (q c o : List Bool) (v : Bool) :
    advance program (cfg (some .second) v (true::q) (true::c) o) =
      cfg (some .second) true q c o := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext i; fin_cases i <;> rfl

private theorem second_cons_zero (q o : List Bool) (v : Bool) :
    advance program (cfg (some .second) v (true::q) [] o) =
      cfg (some .second) false q [] (true::o) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext i; fin_cases i <;> rfl

private theorem second_nil (c o : List Bool) (v : Bool) :
    advance program (cfg (some .second) v [] c o) =
      cfg (some .clear) false [] c o := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem second_run (m c o : ℕ) (v : Bool) :
    run (m+1) (cfg (some .second) v (List.replicate m true)
      (List.replicate c true) (List.replicate o true)) =
      cfg (some .clear) false [] (List.replicate (c-m) true)
        (List.replicate (o+(m-c)) true) := by
  induction m generalizing c o v with
  | zero => simpa using second_nil (List.replicate c true) (List.replicate o true) v
  | succ m ih =>
      rw [run, Function.iterate_succ_apply]
      cases c with
      | zero =>
          simp only [List.replicate_succ, List.replicate_zero]
          rw [second_cons_zero]
          have h := ih 0 (o+1) false
          simpa [run, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using h
      | succ c =>
          simp only [List.replicate_succ]
          rw [second_cons_pos]
          simpa [run, Nat.succ_sub_succ_eq_sub] using ih c o true

private theorem clear_cons (c o : List Bool) (v : Bool) :
    advance program (cfg (some .clear) v [] (true::c) o) =
      cfg (some .clear) true [] c o := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext i; fin_cases i <;> rfl

private theorem clear_nil (o : List Bool) (v : Bool) :
    advance program (cfg (some .clear) v [] [] o) = cfg none false [] [] o := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem clear_run (c : ℕ) (o : List Bool) (v : Bool) :
    run (c+1) (cfg (some .clear) v [] (List.replicate c true) o) =
      cfg none false [] [] o := by
  induction c generalizing v with
  | zero => exact clear_nil o v
  | succ c ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [clear_cons]
      exact ih true

theorem run_correct (n m : ℕ) :
    run ((n+1)+(m+1)+(n-m+1))
      (cfg (some .first) false (MatrixUnaryArithmetic.encodeInput n m) [] []) =
      cfg none false [] [] (List.replicate (max n m) true) := by
  rw [run_add (n+1+(m+1)) (n-m+1), run_add (n+1) (m+1)]
  have h := first_run n m 0 0 false
  simp only [Nat.add_zero, List.replicate_zero] at h
  rw [h, second_run, clear_run]
  congr 2
  omega

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 Label.first false program

theorem outputs (n m : ℕ) :
    machine.OutputsWithin (MatrixUnaryArithmetic.encodeInput n m)
      (List.replicate (max n m) true) (2*n+m+3) := by
  have hi : rawInit (0 : Fin 3) Label.first false
      (MatrixUnaryArithmetic.encodeInput n m) =
      cfg (some .first) false (MatrixUnaryArithmetic.encodeInput n m) [] [] := by
    unfold rawInit cfg
    congr 1
    funext i; fin_cases i <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 Label.first false program _ _
    ((n+1)+(m+1)+(n-m+1)) (2*n+m+3) (by omega)
  · rw [hi, ← run, run_correct]; rfl
  · rw [hi, ← run, run_correct]; rfl

#print axioms outputs
end V22UnaryMax
