import CurrentAdditive.RawRatDenominatorCanonical
import EthInapproximability.CurrentPaper.BitMachineClearBank
import Mathlib.Tactic

/-! The canonical zero numerator physically forces a nonnegative sign. -/
namespace CurrentAdditive.RawRatSignCleanup

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding

abbrev Bank := RawRatPreparation.Bank
abbrev Control := Unit × Option Bool

inductive Label where
  | check | clear | done
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 13 => Bool) Label Control
  | .check => peek 1 (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome) halt (goto (fun _ => .clear)))
  | .clear => BitMachineClearBank.clearStep (0 : Fin 13) .clear .done
  | .done => halt

def result (S : Bank) : Bank :=
  if S 1 = [] then Function.update S 0 [] else S

def cfg (l : Option Label) (v : Control) (S : Bank) :
    TM2.Cfg (fun _ : Fin 13 => Bool) Label Control := ⟨l,v,S⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Fin 13 => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem check_nonempty (S : Bank) (b : Bool) (bs : List Bool) (h : S 1 = b :: bs) :
    run 1 (cfg (some .check) ((), none) S) = cfg none ((), some b) S := by
  simp [run, advance, TM2.step, program, cfg, TM2.stepAux, h]

theorem check_empty (S : Bank) (h : S 1 = []) :
    run 1 (cfg (some .check) ((), none) S) = cfg (some .clear) ((), none) S := by
  simp [run, advance, TM2.step, program, cfg, TM2.stepAux, h]

theorem clear_run (S : Bank) :
    run ((S 0).length + 2) (cfg (some .clear) ((), none) S) =
      cfg none ((), none) (Function.update S 0 []) := by
  have hc := BitMachineClearBank.clear_one_run program (0 : Fin 13)
    Label.clear Label.done rfl () S
  change run ((S 0).length + 1) (cfg (some .clear) ((), none) S) =
      cfg (some .done) ((), none) (Function.update S 0 []) at hc
  rw [show (S 0).length + 2 = ((S 0).length + 1) + 1 by omega]
  rw [run, Nat.add_comm, Function.iterate_add_apply]
  change run 1 (run ((S 0).length + 1) (cfg (some .clear) ((), none) S)) = _
  rw [hc]
  simp [run, advance, TM2.step, program, cfg, TM2.stepAux]

theorem total_run (S : Bank) :
    ∃ t ≤ (S 0).length + 3, ∃ v,
      run t (cfg (some .check) ((), none) S) = cfg none v (result S) := by
  cases h : S 1 with
  | nil =>
      refine ⟨(S 0).length + 3, le_rfl, ((), none), ?_⟩
      rw [show (S 0).length + 3 = 1 + ((S 0).length + 2) by omega,
        run, Nat.add_comm, Function.iterate_add_apply]
      change run ((S 0).length + 2)
        (run 1 (cfg (some .check) ((), none) S)) = _
      rw [check_empty S h, clear_run]
      simp [result, h]
  | cons b bs =>
      refine ⟨1, by omega, ((), some b), ?_⟩
      rw [check_nonempty S b bs h]
      simp [result, h]

theorem sign_correct (S : Bank) :
    result S 0 = if S 1 = [] then [] else S 0 := by
  by_cases h : S 1 = [] <;> simp [result, h]

theorem numerator_preserved (S : Bank) : result S 1 = S 1 := by
  by_cases h : S 1 = [] <;> simp [result, h]

theorem denominator_preserved (S : Bank) : result S 11 = S 11 := by
  by_cases h : S 1 = [] <;> simp [result, h]

end CurrentAdditive.RawRatSignCleanup
