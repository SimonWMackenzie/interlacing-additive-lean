import EthInapproximability.CurrentPaper.SignedMidpointPacket

/-!
# Physical unary midpoint cap

Source: frozen v8 `06-eth.tex`, final comparison against `2Y+k`.
This fixed five-stack program consumes the supplied unary threshold `Y` and
unary separation `k`, writing exactly `2Y+k` cells on the cap stack. The
signed answer stack is preserved. No unit-cost arithmetic is used.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointCap

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | double | restore | addK
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def program : Label → Statement
  | .double =>
      pop 1 (fun _ b => b)
        (branch Option.isSome
          (push 3 (fun _ => true)
            (push 3 (fun _ => true) (goto (fun _ => .double))))
          (goto (fun _ => .restore)))
  | .restore =>
      pop 3 (fun _ b => b)
        (branch Option.isSome
          (push 1 (fun _ => true) (goto (fun _ => .restore)))
          (goto (fun _ => .addK)))
  | .addK =>
      pop 2 (fun _ b => b)
        (branch Option.isSome
          (push 1 (fun _ => true) (goto (fun _ => .addK)))
          halt)

def cfg (l : Option Label) (v : Control)
    (answer threshold separation scratch out : List Bool) : Config :=
  ⟨l, v, ![answer, threshold, separation, scratch, out]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t + 1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) :
    run (t + u) c = run u (run t c) := by
  simp only [run, Nat.add_comm t u, Function.iterate_add_apply]

theorem double_step (answer separation scratch out : List Bool) (v : Control) (n : ℕ) :
    advance program (cfg (some .double) v answer
      (true :: List.replicate n true) separation scratch out) =
      cfg (some .double) (some true) answer (List.replicate n true)
        separation (true :: true :: scratch) out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem double_done (answer separation scratch out : List Bool) (v : Control) :
    advance program (cfg (some .double) v answer [] separation scratch out) =
      cfg (some .restore) none answer [] separation scratch out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem double_run (answer separation scratch out : List Bool) (v : Control) (n : ℕ) :
    run (n + 1) (cfg (some .double) v answer
      (List.replicate n true) separation scratch out) =
      cfg (some .restore) none answer [] separation
        (List.replicate (2*n) true ++ scratch) out := by
  induction n generalizing scratch v with
  | zero => simpa [run_succ, run] using double_done answer separation scratch out v
  | succ n ih =>
      rw [List.replicate_succ, run_succ, double_step]
      simpa [show 2 * (n + 1) = 2 * n + 2 by omega,
        List.replicate_add, List.append_assoc]
        using ih (true :: true :: scratch) (some true)

private theorem unary_cons_comm (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append]; rw [ih]

theorem restore_step (answer threshold separation out : List Bool)
    (v : Control) (n : ℕ) :
    advance program (cfg (some .restore) v answer threshold separation
      (true :: List.replicate n true) out) =
      cfg (some .restore) (some true) answer (true :: threshold) separation
        (List.replicate n true) out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem restore_done (answer threshold separation out : List Bool) (v : Control) :
    advance program (cfg (some .restore) v answer threshold separation [] out) =
      cfg (some .addK) none answer threshold separation [] out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem restore_run (answer threshold separation out : List Bool)
    (v : Control) (n : ℕ) :
    run (n + 1) (cfg (some .restore) v answer threshold separation
      (List.replicate n true) out) =
      cfg (some .addK) none answer (List.replicate n true ++ threshold)
        separation [] out := by
  induction n generalizing threshold v with
  | zero => simpa [run_succ, run] using restore_done answer threshold separation out v
  | succ n ih =>
      rw [List.replicate_succ, run_succ, restore_step]
      simpa only [unary_cons_comm] using ih (true :: threshold) (some true)

theorem addK_step (answer threshold scratch out : List Bool)
    (v : Control) (n : ℕ) :
    advance program (cfg (some .addK) v answer threshold
      (true :: List.replicate n true) scratch out) =
      cfg (some .addK) (some true) answer (true :: threshold)
        (List.replicate n true) scratch out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem addK_done (answer threshold scratch out : List Bool) (v : Control) :
    advance program (cfg (some .addK) v answer threshold [] scratch out) =
      cfg none none answer threshold [] scratch out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem addK_run (answer threshold scratch out : List Bool)
    (v : Control) (n : ℕ) :
    run (n + 1) (cfg (some .addK) v answer threshold
      (List.replicate n true) scratch out) =
      cfg none none answer (List.replicate n true ++ threshold) [] scratch out := by
  induction n generalizing threshold v with
  | zero => simpa [run_succ, run] using addK_done answer threshold scratch out v
  | succ n ih =>
      rw [List.replicate_succ, run_succ, addK_step]
      simpa only [unary_cons_comm] using ih (true :: threshold) (some true)

theorem cap_run (answer : List Bool) (threshold separation : ℕ) :
    run (3 * threshold + separation + 3)
      (cfg (some .double) none answer (List.replicate threshold true)
        (List.replicate separation true) [] []) =
      cfg none none answer (List.replicate (2 * threshold + separation) true)
        [] [] [] := by
  have hdouble := double_run answer (List.replicate separation true) [] [] none threshold
  have hrestore := restore_run answer [] (List.replicate separation true) []
    none (2 * threshold)
  have hadd := addK_run answer (List.replicate (2 * threshold) true) [] [] none separation
  simp only [List.append_nil] at hdouble hrestore
  have htotal := (run_add (threshold+1) (2*threshold+1+(separation+1))
    (cfg (some .double) none answer (List.replicate threshold true)
      (List.replicate separation true) [] [])).trans (by rw [hdouble, run_add, hrestore, hadd])
  have ht : threshold + 1 + (2*threshold + 1 + (separation + 1)) =
      3 * threshold + separation + 3 := by omega
  rw [ht] at htotal
  have hr : List.replicate separation true ++ List.replicate (2*threshold) true =
      List.replicate (2*threshold+separation) true := by
    rw [← List.replicate_add, show separation + 2*threshold =
      2*threshold+separation by omega]
  rw [hr] at htotal
  exact htotal

end EthInapproximability.CurrentPaper.SignedMidpointCap
