import EthInapproximability.CurrentPaper.ExactParameterMachinePower
import EthInapproximability.CurrentPaper.MatrixUnaryArithmetic

/-!
# Physical unary squaring for the exact sampler denominator

One fixed copier builds `true^n ++ false :: true^n` from a unary input.
The existing multiplication machine then computes `n*n`, charging all
copy, separator, multiplication, and intermediate-transfer transitions.
Three squarings give the manuscript's exact denominator `d^8`.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineSquare

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Bool
  | .scan => pop 0 (fun _ b => b.isSome)
      (branch id
        (push 1 (fun _ => true) (push 2 (fun _ => true) (goto (fun _ => .scan))))
        (push 1 (fun _ => false) (goto (fun _ => .restore))))
  | .restore => pop 2 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .restore))) halt)

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool

def cfg (l : Option Label) (flag : Bool)
    (input output scratch : List Bool) : Config :=
  ⟨l, flag, ![input, output, scratch]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem replicate_commute (k : ℕ) (scratch : List Bool) :
    List.replicate k true ++ true :: scratch =
      true :: (List.replicate k true ++ scratch) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, List.append_assoc] using ih

theorem run_add (m n : ℕ) (c : Config) : run (m+n) c = run n (run m c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) n m c

private theorem scan_cons (q out scratch : List Bool) (flag : Bool) :
    advance program (cfg (some .scan) flag (true :: q) out scratch) =
      cfg (some .scan) true q (true :: out) (true :: scratch) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem scan_nil (out scratch : List Bool) (flag : Bool) :
    advance program (cfg (some .scan) flag [] out scratch) =
      cfg (some .restore) false [] (false :: out) scratch := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem restore_cons (out scratch : List Bool) (flag : Bool) :
    advance program (cfg (some .restore) flag [] out (true :: scratch)) =
      cfg (some .restore) true [] (true :: out) scratch := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (out : List Bool) (flag : Bool) :
    advance program (cfg (some .restore) flag [] out []) =
      cfg none false [] out [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem scan_run (n : ℕ) (out scratch : List Bool) (flag : Bool) :
    run (n+1) (cfg (some .scan) flag (List.replicate n true) out scratch) =
      cfg (some .restore) false []
        (false :: List.replicate n true ++ out)
        (List.replicate n true ++ scratch) := by
  induction n generalizing flag out scratch with
  | zero => simpa [run] using scan_nil out scratch flag
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [scan_cons]
      have hh := ih (true :: out) (true :: scratch) true
      simp only [replicate_commute] at hh
      have he : false :: List.replicate n true ++ true :: out =
          false :: true :: List.replicate n true ++ out := by
        simp only [List.cons_append]
        rw [replicate_commute]
      rw [he] at hh
      simpa [run, List.replicate_succ, List.append_assoc] using hh

private theorem restore_run (n : ℕ) (out : List Bool) (flag : Bool) :
    run (n+1) (cfg (some .restore) flag [] out (List.replicate n true)) =
      cfg none false [] (List.replicate n true ++ out) [] := by
  induction n generalizing out flag with
  | zero => simpa [run] using restore_nil out flag
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [restore_cons]
      have hh := ih (true :: out) true
      rw [replicate_commute] at hh
      simpa [run, List.replicate_succ, List.append_assoc] using hh

theorem exact_run (n : ℕ) :
    run (2*n+2) (cfg (some .scan) false (List.replicate n true) [] []) =
      cfg none false [] (MatrixUnaryArithmetic.encodeInput n n) [] := by
  have hs := scan_run n [] [] false
  have hr := restore_run n (false :: List.replicate n true) false
  have htime : 2*n+2 = (n+1)+(n+1) := by omega
  rw [htime, run_add, hs]
  convert hr using 1
  simp [MatrixUnaryArithmetic.encodeInput, List.append_assoc]

noncomputable def duplicateMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) (1 : Fin 3) .scan false program

theorem duplicate_outputs (n : ℕ) :
    duplicateMachine.OutputsWithin (List.replicate n true)
      (MatrixUnaryArithmetic.encodeInput n n) (2*n+2) := by
  have hi : rawInit (0 : Fin 3) Label.scan false (List.replicate n true) =
      cfg (some .scan) false (List.replicate n true) [] [] := by
    simp [rawInit, cfg]
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 3) (1 : Fin 3) .scan false program
    (List.replicate n true) (MatrixUnaryArithmetic.encodeInput n n)
    (2*n+2) (2*n+2) (by omega)
  · rw [hi]; exact congrArg TM2.Cfg.l (exact_run n)
  · rw [hi]; exact congrArg (fun c => c.stk 1) (exact_run n)

noncomputable def squareMachine : BitMachine.Machine :=
  BitMachineComposition.composition duplicateMachine MatrixUnaryArithmetic.bitMachine

theorem square_outputs (n : ℕ) :
    squareMachine.OutputsWithin (List.replicate n true)
      (List.replicate (n^2) true)
      (2*n+2 + 2*(2*n+1)+2 + 2*(2*n+2)^2) := by
  have hmul := MatrixUnaryArithmetic.bitMachine_outputs n n
  have hc := BitMachineComposition.composition_outputsWithin
    duplicateMachine MatrixUnaryArithmetic.bitMachine (duplicate_outputs n) hmul
  have hlen : (MatrixUnaryArithmetic.encodeInput n n).length = 2*n+1 := by
    simp [MatrixUnaryArithmetic.encodeInput]
    omega
  rw [hlen] at hc
  have htime : 2*n+2 + 2*(2*n+1)+2+2*(2*n+2)^2 =
      2*n+2+2*(2*n+1)+2+2*((2*n+1+1)^2) := by ring
  rw [htime]
  simpa only [squareMachine, Nat.pow_two] using hc

noncomputable def eighthPowerMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition squareMachine squareMachine) squareMachine

theorem eighthPower_outputs (n : ℕ) :
    ∃ T, eighthPowerMachine.OutputsWithin (List.replicate n true)
      (List.replicate (n^8) true) T := by
  have h1 := square_outputs n
  have h2 := square_outputs (n^2)
  have h3 := square_outputs (n^4)
  have h12 := BitMachineComposition.composition_outputsWithin
    squareMachine squareMachine h1 h2
  have he12 : (n^2)^2 = n^4 := by ring
  rw [he12] at h12
  have h123 := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition squareMachine squareMachine) squareMachine
    h12 h3
  have he123 : (n^4)^2 = n^8 := by ring
  rw [he123] at h123
  exact ⟨_, h123⟩

noncomputable def denominatorMachine : BitMachine.Machine :=
  BitMachineComposition.composition ExactParameterMachinePower.dMachine eighthPowerMachine

theorem denominator_outputs (edges : ℕ) :
    ∃ T, denominatorMachine.OutputsWithin (List.replicate edges true)
      (List.replicate (SmallBiasSampler.exactDenominator
        (ExactSourcePadding.paddedDimension edges)) true) T := by
  obtain ⟨T, hd⟩ := ExactParameterMachinePower.d_outputs edges
  obtain ⟨U, he⟩ := eighthPower_outputs (ExactSourcePadding.paddedDimension edges)
  have hc := BitMachineComposition.composition_outputsWithin
    ExactParameterMachinePower.dMachine eighthPowerMachine hd he
  exact ⟨_, by simpa only [denominatorMachine, SmallBiasSampler.exactDenominator] using hc⟩

end EthInapproximability.CurrentPaper.ExactParameterMachineSquare
