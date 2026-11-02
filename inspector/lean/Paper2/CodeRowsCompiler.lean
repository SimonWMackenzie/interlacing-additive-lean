import Paper2.GeneratorSource
import Paper2.GeneratorSerialization
import Paper2.CodeConstructorMachine
import Paper2.CodeCopiesMachine
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A physical arithmetic component for the actual graph-row code compiler.
The full fixed-program compiler is not claimed here. -/

namespace Paper2.CodeRowsCompiler

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorSource Paper2.GeneratorCode Paper2.GeneratorSerialization

inductive ArithLabel where
  | init | scan0 | scan1 | scan2 | scan3 | restore | accept
  deriving DecidableEq, Fintype

abbrev ArithControl := Option Bool

/-- Stack 0: retained unary `s`; stack 1: `unary (4*s)`; stack 2:
`unary (s-3)`; stack 3: restoring scratch. -/
def arithProgram : ArithLabel →
    TM2.Stmt (fun _ : Fin 4 => Bool) ArithLabel ArithControl
  | .init =>
      push 1 (fun _ => false)
        (push 2 (fun _ => false) (goto (fun _ => .scan0)))
  | .scan0 => arithScan .scan1 false
  | .scan1 => arithScan .scan2 false
  | .scan2 => arithScan .scan3 false
  | .scan3 => arithScan .scan3 true
  | .restore =>
      pop 3 (fun _ b => b)
        (branch Option.isSome
          (push 0 (fun b => b.getD false) (goto (fun _ => .restore)))
          (goto (fun _ => .accept)))
  | .accept => load (fun _ => none) halt
where
  arithScan (next : ArithLabel) (sub : Bool) :
      TM2.Stmt (fun _ : Fin 4 => Bool) ArithLabel ArithControl :=
    pop 0 (fun _ b => b)
      (branch Option.isSome
        (branch (fun b => b.getD false)
          (push 3 (fun _ => true)
            (push 1 (fun _ => true)
              (push 1 (fun _ => true)
                (push 1 (fun _ => true)
                  (push 1 (fun _ => true)
                    (if sub then push 2 (fun _ => true)
                      (goto (fun _ => next))
                    else goto (fun _ => next)))))))
          (push 0 (fun _ => false) (goto (fun _ => .restore))))
        (goto (fun _ => .restore)))

def arithContents (source fourS subS scratch : List Bool) :
    Fin 4 → List Bool :=
  fun i => if i = 0 then source else if i = 1 then fourS else
    if i = 2 then subS else scratch

def arithCfg (label : Option ArithLabel) (control : ArithControl)
    (source fourS subS scratch : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) ArithLabel ArithControl :=
  ⟨label, control, arithContents source fourS subS scratch⟩

def arithRun (steps : Nat)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) ArithLabel ArithControl) :=
  ((advance arithProgram)^[steps]) c

theorem arithRun_add (a b : Nat)
    (c : TM2.Cfg (fun _ : Fin 4 => Bool) ArithLabel ArithControl) :
    arithRun (a+b) c = arithRun b (arithRun a c) := by
  simpa only [arithRun, Nat.add_comm] using
    Function.iterate_add_apply (advance arithProgram) b a c

private theorem arith_scan0_true (rest four sub scratch : List Bool) :
    arithRun 1 (arithCfg (some .scan0) none (true :: rest) four sub scratch) =
      arithCfg (some .scan1) (some true) rest
        (true :: true :: true :: true :: four) sub (true :: scratch) := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]
  funext i
  fin_cases i <;> simp [arithContents]

private theorem arith_scan1_true (rest four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan1) control (true :: rest) four sub scratch) =
      arithCfg (some .scan2) (some true) rest
        (true :: true :: true :: true :: four) sub (true :: scratch) := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]
  funext i
  fin_cases i <;> simp [arithContents]

private theorem arith_scan2_true (rest four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan2) control (true :: rest) four sub scratch) =
      arithCfg (some .scan3) (some true) rest
        (true :: true :: true :: true :: four) sub (true :: scratch) := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]
  funext i
  fin_cases i <;> simp [arithContents]

private theorem arith_scan3_true (rest four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan3) control (true :: rest) four sub scratch) =
      arithCfg (some .scan3) (some true) rest
        (true :: true :: true :: true :: four) (true :: sub)
        (true :: scratch) := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]
  funext i
  fin_cases i <;> simp [arithContents]

private theorem arith_init (source : List Bool) :
    arithRun 1 (arithCfg (some .init) none source [] [] []) =
      arithCfg (some .scan0) none source [false] [false] [] := by
  simp [arithRun, arithCfg, arithProgram, advance, TM2.step,
    TM2.stepAux, arithContents]
  funext i
  fin_cases i <;> simp [arithContents]

private theorem arith_scan0_false (four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan0) control [false] four sub scratch) =
      arithCfg (some .restore) (some false) [false] four sub scratch := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]

private theorem arith_scan1_false (four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan1) control [false] four sub scratch) =
      arithCfg (some .restore) (some false) [false] four sub scratch := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]

private theorem arith_scan2_false (four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan2) control [false] four sub scratch) =
      arithCfg (some .restore) (some false) [false] four sub scratch := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]

private theorem arith_scan3_false (four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .scan3) control [false] four sub scratch) =
      arithCfg (some .restore) (some false) [false] four sub scratch := by
  simp [arithRun, arithCfg, arithProgram, arithProgram.arithScan,
    advance, TM2.step, TM2.stepAux, arithContents]

private theorem arith_restore_true (source four sub scratch : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .restore) control source four sub
      (true :: scratch)) =
      arithCfg (some .restore) (some true) (true :: source) four sub scratch := by
  simp [arithRun, arithCfg, arithProgram, advance, TM2.step,
    TM2.stepAux, arithContents]
  funext i
  fin_cases i <;> simp [arithContents]

private theorem arith_restore_empty (source four sub : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .restore) control source four sub []) =
      arithCfg (some .accept) none source four sub [] := by
  simp [arithRun, arithCfg, arithProgram, advance, TM2.step,
    TM2.stepAux, arithContents]

private theorem arith_accept (source four sub : List Bool)
    (control : ArithControl) :
    arithRun 1 (arithCfg (some .accept) control source four sub []) =
      arithCfg none none source four sub [] := by
  simp [arithRun, arithCfg, arithProgram, advance, TM2.step,
    TM2.stepAux]

private theorem replicate_true_commute (k : Nat) (tail : List Bool) :
    List.replicate k true ++ (true :: tail) =
      true :: (List.replicate k true ++ tail) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [List.replicate_succ, List.cons_append] using
        (congrArg (List.cons true) ih)

private theorem arith_scan3_run (r : Nat) (four sub scratch : List Bool) :
    arithRun r
      (arithCfg (some .scan3) (some true)
        (List.replicate r true ++ [false]) four sub scratch) =
      arithCfg (some .scan3) (some true) [false]
        (List.replicate (4*r) true ++ four)
        (List.replicate r true ++ sub)
        (List.replicate r true ++ scratch) := by
  induction r generalizing four sub scratch with
  | zero => simp [arithRun]
  | succ r ih =>
      have hadd := arithRun_add 1 r
        (arithCfg (some .scan3) (some true)
          (List.replicate (r+1) true ++ [false]) four sub scratch)
      have hstep :
          arithRun (r+1)
            (arithCfg (some .scan3) (some true)
              (List.replicate (r+1) true ++ [false]) four sub scratch) =
          arithRun r
            (arithRun 1 (arithCfg (some .scan3) (some true)
              (List.replicate (r+1) true ++ [false]) four sub scratch)) := by
        simpa only [Nat.add_comm 1 r] using hadd
      rw [hstep]
      simp only [List.replicate_succ, List.cons_append]
      rw [arith_scan3_true]
      rw [ih]
      simp [Nat.mul_succ, List.replicate_add,
        replicate_true_commute]

private theorem arith_restore_run (k : Nat) (source four sub : List Bool)
    (control : ArithControl) :
    arithRun k
      (arithCfg (some .restore) control source four sub
        (List.replicate k true)) =
      arithCfg (some .restore)
        (if k = 0 then control else some true)
        (List.replicate k true ++ source) four sub [] := by
  induction k generalizing source control with
  | zero => simp [arithRun]
  | succ k ih =>
      have hadd := arithRun_add 1 k
        (arithCfg (some .restore) control source four sub
          (List.replicate (k+1) true))
      have hstep :
          arithRun (k+1)
            (arithCfg (some .restore) control source four sub
              (List.replicate (k+1) true)) =
          arithRun k
            (arithRun 1 (arithCfg (some .restore) control source four sub
              (List.replicate (k+1) true))) := by
        simpa only [Nat.add_comm 1 k] using hadd
      rw [hstep]
      simp only [List.replicate_succ]
      rw [arith_restore_true]
      rw [ih]
      simp [List.cons_append, replicate_true_commute]

private theorem arith_first_three (r : Nat) :
    arithRun 3
      (arithCfg (some .scan0) none
        (List.replicate (r+3) true ++ [false]) [false] [false] []) =
      arithCfg (some .scan3) (some true)
        (List.replicate r true ++ [false])
        (List.replicate 12 true ++ [false]) [false]
        (List.replicate 3 true) := by
  have hrep : List.replicate (r+3) true ++ [false] =
      true :: true :: true :: (List.replicate r true ++ [false]) := by
    simp [List.replicate_succ]
  rw [show (3 : Nat) = 1+(1+1) by omega, arithRun_add 1 (1+1), hrep]
  rw [arith_scan0_true, arithRun_add 1 1, arith_scan1_true,
    arith_scan2_true]
  rfl

/-- The actual Boolean-stack arithmetic run for source widths at least 3.
Both derived unary operands are produced, the source survives, and the
scratch stack is empty at halt. Every input bit and output bit is charged. -/
theorem arith_run (s : Nat) (hs : 3 ≤ s) :
    arithRun (2*s+4)
      (arithCfg (some .init) none (unary s) [] [] []) =
      arithCfg none none (unary s) (unary (4*s)) (unary (s-3)) [] := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r+3 := ⟨s-3, by omega⟩
  have hrep : List.replicate r true ++ List.replicate 3 true =
      List.replicate (r+3) true := by simp [List.replicate_add]
  have hfour : List.replicate (4*r) true ++
      List.replicate 12 true ++ [false] = unary (4*(r+3)) := by
    simp [unary, Nat.mul_add, List.replicate_add, List.append_assoc]
  have hclock : 2*(r+3)+4 =
      1+(3+(r+(1+((r+3)+(1+1))))) := by omega
  have hdecomp (c : TM2.Cfg (fun _ : Fin 4 => Bool) ArithLabel ArithControl) :
      arithRun (1+(3+(r+(1+((r+3)+(1+1)))))) c =
        arithRun 1 (arithRun 1
          (arithRun (r+3) (arithRun 1
            (arithRun r (arithRun 3 (arithRun 1 c)))))) := by
    simp only [arithRun_add]
  rw [hclock]
  rw [hdecomp, arith_init]
  simp only [unary]
  rw [arith_first_three, arith_scan3_run, arith_scan3_false]
  rw [hrep, arith_restore_run, arith_restore_empty, arith_accept]
  simp [Nat.mul_add, List.replicate_add, List.append_assoc]

theorem arith_clock_linear (s : Nat) :
    2*s+4 ≤ 3*(unary s).length+1 := by
  rw [unary_length]
  omega

noncomputable def arithMachine :=
  ofFinite (0 : Fin 4) (1 : Fin 4) ArithLabel.init
    (none : ArithControl) arithProgram

theorem arith_machine_run (s : Nat) (hs : 3 ≤ s) :
    arithMachine.run (2*s+4)
      (renameCfg (Fintype.equivFin (Fin 4))
        (Fintype.equivFin ArithLabel) (Fintype.equivFin ArithControl)
        (arithCfg (some .init) none (unary s) [] [] [])) =
      renameCfg (Fintype.equivFin (Fin 4))
        (Fintype.equivFin ArithLabel) (Fintype.equivFin ArithControl)
        (arithCfg none none (unary s) (unary (4*s)) (unary (s-3)) []) := by
  exact (ofFinite_run (0 : Fin 4) (1 : Fin 4) ArithLabel.init
    (none : ArithControl) arithProgram
    (arithCfg (some .init) none (unary s) [] [] []) (2*s+4)).trans
    (congrArg (renameCfg (Fintype.equivFin (Fin 4))
      (Fintype.equivFin ArithLabel) (Fintype.equivFin ArithControl))
      (arith_run s hs))

theorem arith_source_targets (s : Nat) :
    (List.replicate (4*s) true ++ [false],
      List.replicate (s-3) true ++ [false]) =
      (unary (4*s), unary (s-3)) := rfl

theorem graphRows_unfold (n q₁ q₂ s : Nat) (c : Code) :
    graphRowsCode (V := Fin n) q₁ q₂ s c =
      .branch3 512 510 511
        (.append (.emit [false])
          (.append (.ticket s) (copies q₂ (.append (.ticket q₁) c))))
        (.append (.emit [true])
          (.append
            (.append (.ticket (4*s))
              (.append (.emit [false]) (.ticket n))) c))
        (.append (.emit [true])
          (.append
            (.append (.ticket (4*s))
              (.append (.emit [true]) (.ticket (s-3)))) c)) := by
  simp [graphRowsCode, rowsCode, vertexLabelsCode, auxiliaryLabelsCode,
    templateRowCode, templateCode]

#print axioms graphRows_unfold
#print axioms arith_run
#print axioms arith_machine_run
#print axioms arith_clock_linear

end Paper2.CodeRowsCompiler
