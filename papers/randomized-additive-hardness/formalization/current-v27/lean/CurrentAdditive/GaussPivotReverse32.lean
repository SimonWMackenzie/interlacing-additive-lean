import CurrentAdditive.GaussPivotScanRun

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotReverse32

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 32

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scan =>
      pop 9 (fun _ b => b)
        (branch Option.isSome
          (push 15 (fun v => v.getD false)
            (load (fun _ => none) (goto (fun _ => .scan))))
          halt)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem step_cons (b : Bool) (bs out : List Bool)
    (S : Stack → List Bool) (h9 : S 9 = b :: bs)
    (h15 : S 15 = out) :
    advance program ⟨some .scan, none, S⟩ =
      ⟨some .scan, none, Function.update
        (Function.update S 9 bs) 15 (b :: out)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, h9, h15,
    Function.update_apply]

theorem step_nil (S : Stack → List Bool) (h9 : S 9 = []) :
    advance program ⟨some .scan, none, S⟩ =
      ⟨none, none, S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, h9]

theorem run_succ {c c' : Config} (h : advance program c = c')
    (t : Nat) : run (t+1) c = run t c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run t) h)

theorem run_with_output (bs out : List Bool)
    (S : Stack → List Bool) (h9 : S 9 = bs) (h15 : S 15 = out) :
    run (bs.length + 1) ⟨some .scan, none, S⟩ =
      ⟨none, none,
        Function.update (Function.update S 9 []) 15
          (bs.reverse ++ out)⟩ := by
  induction bs generalizing S out with
  | nil =>
      change run 1 ⟨some .scan, none, S⟩ =
        ⟨none, none, Function.update (Function.update S 9 []) 15 out⟩
      rw [run_succ (step_nil S h9) 0]
      simp only [run, Function.iterate_zero, id]
      congr 1
      funext x
      by_cases hx9 : x = 9
      · subst x
        simp [Function.update_apply, h9]
      · by_cases hx15 : x = 15
        · subst x
          simp [Function.update_apply, h15]
        · simp [Function.update_apply, hx9, hx15]
  | cons b bs ih =>
      have hs := step_cons b bs out S h9 h15
      rw [show (b :: bs).length + 1 = bs.length + 1 + 1 by simp, run_succ hs]
      have h9' : (Function.update (Function.update S 9 bs) 15
          (b :: out)) 9 = bs := by simp [Function.update_apply]
      have h15' : (Function.update (Function.update S 9 bs) 15
          (b :: out)) 15 = b :: out := by simp [Function.update_apply]
      rw [ih (b :: out) _ h9' h15']
      congr 1
      funext x
      by_cases hx9 : x = 9
      · subst x
        simp [Function.update_apply]
      · by_cases hx15 : x = 15
        · subst x
          simp [Function.update_apply, List.reverse_cons, List.append_assoc]
        · simp [Function.update_apply, hx9, hx15]

theorem reversed_bank (bs : List Bool) (S : Stack → List Bool)
    (h9 : S 9 = bs) (h15 : S 15 = []) :
    (run (bs.length + 1) ⟨some .scan, none, S⟩).stk 15 = bs.reverse := by
  rw [run_with_output bs [] S h9 h15]
  simp

#print axioms run_with_output

end CurrentAdditive.GaussPivotReverse32
