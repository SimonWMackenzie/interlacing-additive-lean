import EthInapproximability.CurrentPaper.BitMachine
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
Fixed TM2 scanner for a Boolean stream: write one unary tick for each
initial `true`, and stop at the first `false` or end. This is the final scan
needed after pivot-equality flags have been physically materialized.
-/

namespace CurrentAdditive.GaussPrefixTrue

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .scan =>
      pop 0 (fun _ b => b)
        (branch (fun b => b == some true)
          (push 1 (fun _ => true) (goto fun _ => .scan))
          halt)

def cfg (l : Option Label) (v : Control) (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Control :=
  ⟨l, v, ![input, output]⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem replicate_cons_swap (n : Nat) (xs : List Bool) :
    List.replicate n true ++ true :: xs =
      true :: (List.replicate n true ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem run_acc (input accumulator : List Bool) (initial : Control) :
    ∃ (t : Nat) (rest : List Bool) (v : Control),
      t ≤ input.length + 1 ∧
      run t (cfg (some .scan) initial input accumulator) =
        cfg none v rest
          (List.replicate (input.takeWhile id).length true ++ accumulator) := by
  induction input generalizing accumulator initial with
  | nil =>
      refine ⟨1, [], none, by omega, ?_⟩
      simp [run, cfg, advance, program, TM2.step, TM2.stepAux]
  | cons b bs ih =>
      cases b with
      | false =>
          refine ⟨1, bs, some false, by omega, ?_⟩
          simp [run, cfg, advance, program, TM2.step, TM2.stepAux]
          funext i
          fin_cases i <;> simp
      | true =>
          obtain ⟨t, rest, v, ht, hr⟩ := ih (true :: accumulator) (some true)
          refine ⟨t + 1, rest, v, by simpa using Nat.add_le_add_right ht 1, ?_⟩
          have hstep : run 1 (cfg (some .scan) initial (true :: bs) accumulator) =
              cfg (some .scan) (some true) bs (true :: accumulator) := by
            simp [run, cfg, advance, program, TM2.step, TM2.stepAux]
            funext i
            fin_cases i <;> simp
          change ((advance program)^[t + 1])
            (cfg (some .scan) initial (true :: bs) accumulator) = _
          rw [Function.iterate_succ_apply]
          change run t (run 1 (cfg (some .scan) initial (true :: bs) accumulator)) = _
          rw [hstep]
          rw [hr]
          simp only [List.takeWhile]
          congr 1
          exact replicate_cons_swap _ _

def result (input : List Bool) : List Bool :=
  List.replicate (input.takeWhile id).length true

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 .scan none program

theorem rawInit_eq (input : List Bool) :
    rawInit (0 : Fin 2) .scan (none : Control) input =
      cfg (some .scan) none input [] := by
  unfold rawInit cfg
  congr 1
  funext i
  fin_cases i <;> rfl

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (input.length + 1) := by
  obtain ⟨t, rest, v, ht, hr⟩ := run_acc input [] none
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 .scan (none : Control)
    program input (result input) t (input.length + 1) ht
  · rw [rawInit_eq]
    change (run t (cfg (some .scan) none input [])).l = none
    rw [hr]
    rfl
  · rw [rawInit_eq]
    change (run t (cfg (some .scan) none input [])).stk 1 = result input
    rw [hr]
    simp [cfg, result]

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 1, 1, ?_⟩
  intro input
  simpa [pow_one] using outputs input

#print axioms outputs
#print axioms polytime

end CurrentAdditive.GaussPrefixTrue
