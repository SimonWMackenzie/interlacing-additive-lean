import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.EncodedCommunication
import Mathlib.Tactic

/-!
# Source-preserving binary zero test

The base-`p` digit loop must stop on a numerically zero quotient, not merely
on an empty quotient stack: long division may leave high zero bits. This
two-bank finite-control routine restores the word and records whether any
bit was one. Runtime is linear in the word length.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBinaryZeroTest

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

structure Control where
  seenOne : Bool
  bit : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .scan => pop 0 (fun s b => ⟨s.seenOne || b.getD false, b⟩)
      (branch (fun s => s.bit.isSome)
        (push 1 (fun s => s.bit.getD false) (goto (fun _ => .scan)))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun s b => ⟨s.seenOne, b⟩)
      (branch (fun s => s.bit.isSome)
        (push 0 (fun s => s.bit.getD false) (goto (fun _ => .restore)))
        halt)

def bank (source scratch : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then source else scratch

def cfg (l : Option Label) (s : Control) (source scratch : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Control := ⟨l, s, bank source scratch⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control}
    {t : ℕ} (h : run t c = d) (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (s : Control) (x : Bool) (q saved : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: q) saved) =
      some (cfg (some .scan) ⟨s.seenOne || x, some x⟩ q (x :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_scan_nil (s : Control) (saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] saved) =
      some (cfg (some .restore) ⟨s.seenOne, none⟩ [] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_restore_cons (s : Control) (x : Bool) (q saved : List Bool) :
    TM2.step program (cfg (some .restore) s q (x :: saved)) =
      some (cfg (some .restore) ⟨s.seenOne, some x⟩ (x :: q) saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_nil (s : Control) (q : List Bool) :
    TM2.step program (cfg (some .restore) s q []) =
      some (cfg none ⟨s.seenOne, none⟩ q []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem scan_correct (s : Control) (q saved : List Bool) :
    run (q.length + 1) (cfg (some .scan) s q saved) =
      cfg (some .restore) ⟨s.seenOne || q.any id, none⟩
        [] (q.reverse ++ saved) := by
  induction q generalizing s saved with
  | nil => simpa using run_step (step_scan_nil s saved) 0
  | cons x q ih =>
      rw [List.length_cons, run_step (step_scan_cons s x q saved)]
      simpa [List.reverse_cons, List.append_assoc, Bool.or_assoc] using
        ih ⟨s.seenOne || x, some x⟩ (x :: saved)

theorem restore_correct (s : Control) (q saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s q saved) =
      cfg none ⟨s.seenOne, none⟩ (saved.reverse ++ q) [] := by
  induction saved generalizing s q with
  | nil => simpa using run_step (step_restore_nil s q) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step (step_restore_cons s x q saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.seenOne, some x⟩ (x :: q)

theorem run_correct (q : List Bool) :
    run (2 * q.length + 2) (cfg (some .scan) initial q []) =
      cfg none ⟨q.any id, none⟩ q [] := by
  have hs : run (q.length + 1) (cfg (some .scan) initial q []) =
      cfg (some .restore) ⟨q.any id, none⟩ [] q.reverse := by
    simpa [initial] using scan_correct initial q []
  have hr := restore_correct ⟨q.any id, none⟩ [] q.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have h := (run_add hs (q.length + 1)).trans hr
  rw [show 2 * q.length + 2 = (q.length + 1) + (q.length + 1) by omega]
  exact h

theorem any_false_iff_value_zero (q : List Bool) :
    q.any id = false ↔ EncodedCommunication.bitsValue q = 0 := by
  induction q with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons b q ih =>
      cases b <;>
        simp [EncodedCommunication.bitsValue, Nat.bit_val, ih]

end EthInapproximability.CurrentPaper.BitMachineBinaryZeroTest
