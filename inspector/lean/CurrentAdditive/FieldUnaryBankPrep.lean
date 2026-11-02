import CurrentAdditive.FieldSearchPackedCompletion

/-! Physical preparation of the field search's degree-derived words and the
field printer's unary length and pair counter. The source words are restored.
This local eleven-stack program is later embedded into a combined ambient
bank; its output slots are still raw words, not a semantic bank assignment. -/

namespace CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

abbrev Stack := Fin 11

inductive Label where
  | scanD | restoreD | dropShift | halve | scanN | restoreN | install
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def bank (degree length tempD tempN counter divisor shift half pair printerLength halfWork :
    List Bool) : Stack → List Bool :=
  ![degree, length, tempD, tempN, counter, divisor, shift, half, pair,
    printerLength, halfWork]

def cfg (l : Option Label) (s : Control)
    (degree length tempD tempN counter divisor shift half pair printerLength halfWork :
      List Bool) : Config :=
  ⟨l, s, bank degree length tempD tempN counter divisor shift half pair
    printerLength halfWork⟩

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scanD => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun _ => true)
          (push 4 (fun _ => false)
            (push 8 (fun _ => false)
              (push 8 (fun _ => false)
                (push 6 (fun _ => true)
                  (push 10 (fun _ => true) (goto (fun _ => .scanD))))))))
        (goto (fun _ => .restoreD)))
  | .restoreD => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true) (goto (fun _ => .restoreD)))
        (goto (fun _ => .dropShift)))
  | .dropShift => pop 6 (fun _ b => b) (goto (fun _ => .halve))
  | .halve => pop 10 (fun _ b => b)
      (branch Option.isSome
        (pop 10 (fun _ b => b)
          (branch Option.isSome
            (push 7 (fun _ => true) (goto (fun _ => .halve)))
            (goto (fun _ => .scanN))))
        (goto (fun _ => .scanN)))
  | .scanN => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 3 (fun _ => true)
          (push 9 (fun _ => true) (goto (fun _ => .scanN))))
        (goto (fun _ => .restoreN)))
  | .restoreN => pop 3 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun _ => true) (goto (fun _ => .restoreN)))
        (goto (fun _ => .install)))
  | .install => push 5 (fun _ => false) halt

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

theorem run_one {q r : Config} (h : TM2.step program q = some r) :
    run 1 q = r := by
  simp only [run, Function.iterate_one, advance, h, Option.getD_some]

theorem step_scanD_cons (length tempD tempN counter divisor shift half pair
    printerLength halfWork degree : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .scanD) s (true :: degree) length tempD tempN counter
        divisor shift half pair printerLength halfWork) =
      some (cfg (some .scanD) (some true) degree length (true :: tempD) tempN
        (false :: counter) divisor (true :: shift) half
        (false :: false :: pair) printerLength (true :: halfWork)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_scanD_nil (length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .scanD) s [] length tempD tempN counter divisor shift half
        pair printerLength halfWork) =
      some (cfg (some .restoreD) none [] length tempD tempN counter divisor
        shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem step_restoreD_cons (degree length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .restoreD) s degree length (true :: tempD) tempN counter
        divisor shift half pair printerLength halfWork) =
      some (cfg (some .restoreD) (some true) (true :: degree) length tempD tempN
        counter divisor shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_restoreD_nil (degree length tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .restoreD) s degree length [] tempN counter divisor shift half
        pair printerLength halfWork) =
      some (cfg (some .dropShift) none degree length [] tempN counter divisor
        shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem step_dropShift (degree length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .dropShift) s degree length tempD tempN counter divisor
        (true :: shift) half pair printerLength halfWork) =
      some (cfg (some .halve) (some true) degree length tempD tempN counter
        divisor shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_halve_pair (degree length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .halve) s degree length tempD tempN counter divisor shift
        half pair printerLength (true :: true :: halfWork)) =
      some (cfg (some .halve) (some true) degree length tempD tempN counter
        divisor shift (true :: half) pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_halve_one (degree length tempD tempN counter divisor shift half pair
    printerLength : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .halve) s degree length tempD tempN counter divisor shift
        half pair printerLength [true]) =
      some (cfg (some .scanN) none degree length tempD tempN counter divisor
        shift half pair printerLength []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_halve_nil (degree length tempD tempN counter divisor shift half pair
    printerLength : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .halve) s degree length tempD tempN counter divisor shift
        half pair printerLength []) =
      some (cfg (some .scanN) none degree length tempD tempN counter divisor
        shift half pair printerLength []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem step_scanN_cons (degree length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .scanN) s degree (true :: length) tempD tempN counter divisor
        shift half pair printerLength halfWork) =
      some (cfg (some .scanN) (some true) degree length tempD (true :: tempN)
        counter divisor shift half pair (true :: printerLength) halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_scanN_nil (degree tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .scanN) s degree [] tempD tempN counter divisor shift half
        pair printerLength halfWork) =
      some (cfg (some .restoreN) none degree [] tempD tempN counter divisor
        shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem step_restoreN_cons (degree length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .restoreN) s degree length tempD (true :: tempN) counter
        divisor shift half pair printerLength halfWork) =
      some (cfg (some .restoreN) (some true) degree (true :: length) tempD tempN
        counter divisor shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

theorem step_restoreN_nil (degree length tempD counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .restoreN) s degree length tempD [] counter divisor shift half
        pair printerLength halfWork) =
      some (cfg (some .install) none degree length tempD [] counter divisor
        shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem step_install (degree length tempD tempN counter divisor shift half pair
    printerLength halfWork : List Bool) (s : Control) :
    TM2.step program
      (cfg (some .install) s degree length tempD tempN counter divisor shift half
        pair printerLength halfWork) =
      some (cfg none s degree length tempD tempN counter (false :: divisor)
        shift half pair printerLength halfWork) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp

end CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep
