import Paper2.YaoLogPowerLoader
import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineInline
import Paper2.YaoLowerBoundProbability

/-! For fixed gap parameter `t` and failure parameter `lambda`, one
finite-control program writes the exact public selector-sample count from
unary `H`. Its parameter-dependent initializer has a finite number of
literal push instructions. In the paper's fixed-`t,lambda` regime these
are fixed controller constants, not unbounded input operations. -/

namespace Paper2.YaoParameterLoader

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoLowerBound
open Paper2.YaoLookup

def fixedS (t : ℕ) : ℕ := 2 ^ (2 ^ t - 1)
def fixedCoeff (t : ℕ) : ℕ := 8 * fixedS t ^ 2
def fixedWidth (t : ℕ) : ℕ := fixedCoeff t * 2 ^ (t - 1)
def fixedTail (t lambda : ℕ) : ℕ := fixedCoeff t * lambda

theorem selector_count_polynomial_formula (t b lambda : ℕ) :
    2 ^ b * fixedWidth t + fixedTail t lambda =
      selectorCount t b lambda := by
  unfold fixedWidth fixedTail fixedCoeff fixedS selectorCount
    Paper2.Yao.selectorSampleCount
  ring

abbrev CountLabel := Option MatrixAddressMachine.Label
abbrev CountConfig := TM2.Cfg (fun _ : Fin 6 => Bool) CountLabel Bool

def writeOn (k : Fin 6) : ℕ → TM2.Stmt (fun _ : Fin 6 => Bool) CountLabel Bool →
    TM2.Stmt (fun _ : Fin 6 => Bool) CountLabel Bool
  | 0, q => q
  | n + 1, q => push k (fun _ => true) (writeOn k n q)

private theorem replicate_cons_comm (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs =
      true :: (List.replicate n true ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons true) ih

private theorem writeOn_stepAux (k : Fin 6) (n : ℕ)
    (q : TM2.Stmt (fun _ : Fin 6 => Bool) CountLabel Bool)
    (v : Bool) (S : Fin 6 → List Bool) :
    TM2.stepAux (writeOn k n q) v S =
      TM2.stepAux q v (Function.update S k (List.replicate n true ++ S k)) := by
  induction n generalizing S with
  | zero => simp [writeOn]
  | succ n ih =>
      simp only [writeOn, TM2.stepAux, ih, List.replicate_succ]
      congr 1
      funext j
      by_cases h : j = k
      · subst j
        simp only [Function.update_self]
        exact replicate_cons_comm n (S k)
      · simp [h]

noncomputable def countProgram (t lambda : ℕ) :
    CountLabel → TM2.Stmt (fun _ : Fin 6 => Bool) CountLabel Bool
  | none => writeOn 1 (fixedWidth t)
      (writeOn 2 (fixedTail t lambda) (goto (fun _ => some .outer)))
  | some l => BitMachineInline.stmt some id id none
      (MatrixAddressMachine.program l)

def countStart (H : ℕ) : CountConfig :=
  ⟨some none, false, ![List.replicate H true, [], [], [], [], []]⟩

private theorem count_init (t lambda H : ℕ) :
    advance (countProgram t lambda) (countStart H) =
      BitMachineInline.cfg some id none
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate H true)
          (List.replicate (fixedWidth t) true)
          (List.replicate (fixedTail t lambda) true) [] [] []) := by
  simp only [advance, countProgram, countStart, TM2.step,
    writeOn_stepAux, TM2.stepAux, Option.getD_some,
    BitMachineInline.cfg, MatrixAddressMachine.cfg]
  congr 1
  funext j
  fin_cases j <;> simp [Function.update]

theorem count_run (t lambda H : ℕ) :
    ∃ steps ≤ 1 + MatrixAddressMachine.exactTime H
        (fixedWidth t) (fixedTail t lambda),
      ((advance (countProgram t lambda))^[steps]) (countStart H) =
        BitMachineInline.cfg some id none
          (MatrixAddressMachine.cfg none false
            (List.replicate H true)
            (List.replicate (fixedWidth t) true)
            (List.replicate (fixedTail t lambda) true) [] []
            (List.replicate (H * fixedWidth t + fixedTail t lambda) true)) := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate H true) (List.replicate (fixedWidth t) true)
    (List.replicate (fixedTail t lambda) true) [] [] []
  have hr := MatrixAddressMachine.address_run H (fixedWidth t)
    (fixedTail t lambda) false []
  have hh : (((advance MatrixAddressMachine.program)^[
      MatrixAddressMachine.exactTime H (fixedWidth t) (fixedTail t lambda)]) c).l = none := by
    change (MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime H (fixedWidth t) (fixedTail t lambda)) c).l = none
    rw [hr]; rfl
  obtain ⟨steps, hs, he⟩ := BitMachineInline.outputs some id id (by intro v; rfl)
    none MatrixAddressMachine.program (countProgram t lambda) (by intro l; rfl)
    c (MatrixAddressMachine.exactTime H (fixedWidth t) (fixedTail t lambda)) hh
  refine ⟨1 + steps, by omega, ?_⟩
  rw [show 1 + steps = steps + 1 by omega,
    Function.iterate_succ_apply, count_init]
  change ((advance (countProgram t lambda))^[steps])
    (BitMachineInline.cfg some id none c) = _
  rw [he]
  change BitMachineInline.cfg some id none
    (MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime H (fixedWidth t) (fixedTail t lambda)) c) = _
  rw [hr]
  simp only [List.append_nil]

noncomputable def selectorCountMachine (t lambda : ℕ) : Machine :=
  ofFinite (0 : Fin 6) (5 : Fin 6) (none : CountLabel) false
    (countProgram t lambda)

theorem selector_count_outputs (t b lambda : ℕ) :
    (selectorCountMachine t lambda).OutputsWithin
      (List.replicate (2 ^ b) true)
      (List.replicate (selectorCount t b lambda) true)
      (1 + MatrixAddressMachine.exactTime (2 ^ b)
        (fixedWidth t) (fixedTail t lambda)) := by
  obtain ⟨steps, hs, hr⟩ := count_run t lambda (2 ^ b)
  apply outputsWithin_of_raw_run (0 : Fin 6) (5 : Fin 6)
    (none : CountLabel) false (countProgram t lambda)
    (List.replicate (2 ^ b) true)
    (List.replicate (selectorCount t b lambda) true) steps
    (1 + MatrixAddressMachine.exactTime (2 ^ b)
      (fixedWidth t) (fixedTail t lambda)) hs
  · rw [show rawInit (0 : Fin 6) (none : CountLabel) false
        (List.replicate (2 ^ b) true) = countStart (2 ^ b) by
        unfold rawInit countStart; congr 1; funext j; fin_cases j <;> rfl, hr]
    rfl
  · rw [show rawInit (0 : Fin 6) (none : CountLabel) false
        (List.replicate (2 ^ b) true) = countStart (2 ^ b) by
        unfold rawInit countStart; congr 1; funext j; fin_cases j <;> rfl, hr]
    simp only [BitMachineInline.cfg, MatrixAddressMachine.cfg]
    exact congrArg (fun n => List.replicate n true)
      (selector_count_polynomial_formula t b lambda)

noncomputable def edgeToSelectorCountMachine (t lambda : ℕ) : Machine :=
  composition logPowerMachine (selectorCountMachine t lambda)

theorem edge_to_selector_count_outputs (t e lambda : ℕ) :
    (edgeToSelectorCountMachine t lambda).OutputsWithin
      (List.replicate e true)
      (List.replicate (selectorCount t (paddedEdgeBits e) lambda) true)
      (2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e +
        2*paddedEdgeCount e+2 +
        1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
          (fixedWidth t) (fixedTail t lambda)) := by
  simpa only [edgeToSelectorCountMachine, List.length_replicate,
    paddedEdgeCount, Nat.add_assoc] using composition_outputsWithin logPowerMachine
    (selectorCountMachine t lambda)
    (log_power_outputs e)
    (selector_count_outputs t (paddedEdgeBits e) lambda)

#print axioms edge_to_selector_count_outputs

end Paper2.YaoParameterLoader
