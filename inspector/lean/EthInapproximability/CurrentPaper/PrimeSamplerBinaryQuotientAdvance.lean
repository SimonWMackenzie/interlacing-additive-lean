import EthInapproximability.CurrentPaper.BitMachineBinaryZeroTest
import Mathlib.Tactic

/-!
# Numerical quotient test and next-dividend transfer

After one binary long division the LSB-first quotient may be a nonempty
all-zero word. This fixed three-bank controller scans and restores it, then
either reverses a positive quotient into the next MSB-first dividend or
clears a zero quotient. The finite `seenOne` flag, not list emptiness,
decides whether the digit loop continues.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryQuotientAdvance

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restore | transfer | clear
  deriving DecidableEq, Fintype

structure Control where
  seenOne : Bool
  bit : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan => pop 0 (fun s b => ⟨s.seenOne || b.getD false, b⟩)
      (branch (fun s => s.bit.isSome)
        (push 1 (fun s => s.bit.getD false) (goto (fun _ => .scan)))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun s b => ⟨s.seenOne, b⟩)
      (branch (fun s => s.bit.isSome)
        (push 0 (fun s => s.bit.getD false) (goto (fun _ => .restore)))
        (branch (fun s => s.seenOne)
          (goto (fun _ => .transfer))
          (goto (fun _ => .clear))))
  | .transfer => pop 0 (fun s b => ⟨s.seenOne, b⟩)
      (branch (fun s => s.bit.isSome)
        (push 2 (fun s => s.bit.getD false) (goto (fun _ => .transfer)))
        halt)
  | .clear => pop 0 (fun s b => ⟨s.seenOne, b⟩)
      (branch (fun s => s.bit.isSome)
        (goto (fun _ => .clear))
        halt)

def bank (quotient scratch nextDividend : List Bool) : Fin 3 → List Bool :=
  ![quotient, scratch, nextDividend]

def cfg (l : Option Label) (s : Control)
    (quotient scratch nextDividend : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨l,s,bank quotient scratch nextDividend⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    {t : ℕ} (h : run t c = d) (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (s : Control) (x : Bool)
    (q saved target : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: q) saved target) =
      some (cfg (some .scan) ⟨s.seenOne || x, some x⟩
        q (x :: saved) target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_scan_nil (s : Control) (saved target : List Bool) :
    TM2.step program (cfg (some .scan) s [] saved target) =
      some (cfg (some .restore) ⟨s.seenOne, none⟩ [] saved target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_restore_cons (s : Control) (x : Bool)
    (q saved target : List Bool) :
    TM2.step program (cfg (some .restore) s q (x :: saved) target) =
      some (cfg (some .restore) ⟨s.seenOne, some x⟩
        (x :: q) saved target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_nil_true (s : Control)
    (q target : List Bool) (h : s.seenOne = true) :
    TM2.step program (cfg (some .restore) s q [] target) =
      some (cfg (some .transfer) ⟨true, none⟩ q [] target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank, h]

private theorem step_restore_nil_false (s : Control)
    (q target : List Bool) (h : s.seenOne = false) :
    TM2.step program (cfg (some .restore) s q [] target) =
      some (cfg (some .clear) ⟨false, none⟩ q [] target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank, h]

theorem scan_correct (s : Control) (q saved target : List Bool) :
    run (q.length + 1) (cfg (some .scan) s q saved target) =
      cfg (some .restore) ⟨s.seenOne || q.any id, none⟩
        [] (q.reverse ++ saved) target := by
  induction q generalizing s saved with
  | nil => simpa using run_step (step_scan_nil s saved target) 0
  | cons x q ih =>
      rw [List.length_cons, run_step (step_scan_cons s x q saved target)]
      simpa [List.reverse_cons, List.append_assoc, Bool.or_assoc] using
        ih ⟨s.seenOne || x, some x⟩ (x :: saved)

theorem restore_correct (seen : Bool) (q saved target : List Bool) :
    run (saved.length + 1)
      (cfg (some .restore) ⟨seen, none⟩ q saved target) =
      cfg (some (if seen then .transfer else .clear)) ⟨seen, none⟩
        (saved.reverse ++ q) [] target := by
  induction saved generalizing q with
  | nil =>
      cases seen with
      | false =>
          simpa using run_step
            (step_restore_nil_false ⟨false, none⟩ q target rfl) 0
      | true =>
          simpa using run_step
            (step_restore_nil_true ⟨true, none⟩ q target rfl) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step
        (step_restore_cons ⟨seen, none⟩ x q saved target)]
      simpa [List.reverse_cons, List.append_assoc] using ih (x :: q)

private theorem step_transfer_cons (seen : Bool) (x : Bool)
    (q target : List Bool) :
    TM2.step program (cfg (some .transfer) ⟨seen, none⟩
      (x :: q) [] target) =
      some (cfg (some .transfer) ⟨seen, some x⟩ q [] (x :: target)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_transfer_nil (seen : Bool) (target : List Bool) :
    TM2.step program (cfg (some .transfer) ⟨seen, none⟩ [] [] target) =
      some (cfg none ⟨seen, none⟩ [] [] target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_clear_cons (seen : Bool) (x : Bool)
    (q target : List Bool) :
    TM2.step program (cfg (some .clear) ⟨seen, none⟩
      (x :: q) [] target) =
      some (cfg (some .clear) ⟨seen, some x⟩ q [] target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_clear_nil (seen : Bool) (target : List Bool) :
    TM2.step program (cfg (some .clear) ⟨seen, none⟩ [] [] target) =
      some (cfg none ⟨seen, none⟩ [] [] target) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem transfer_correct (seen : Bool) (q target : List Bool) :
    run (q.length + 1) (cfg (some .transfer) ⟨seen, none⟩ q [] target) =
      cfg none ⟨seen, none⟩ [] [] (q.reverse ++ target) := by
  induction q generalizing target with
  | nil => simpa using run_step (step_transfer_nil seen target) 0
  | cons x q ih =>
      rw [List.length_cons, run_step (step_transfer_cons seen x q target)]
      simpa [List.reverse_cons, List.append_assoc] using ih (x :: target)

theorem clear_correct (seen : Bool) (q target : List Bool) :
    run (q.length + 1) (cfg (some .clear) ⟨seen, none⟩ q [] target) =
      cfg none ⟨seen, none⟩ [] [] target := by
  induction q with
  | nil => simpa using run_step (step_clear_nil seen target) 0
  | cons x q ih =>
      rw [List.length_cons, run_step (step_clear_cons seen x q target)]
      simpa using ih

theorem run_correct (q target : List Bool) :
    run (3 * q.length + 3) (cfg (some .scan) initial q [] target) =
      cfg none ⟨q.any id, none⟩ [] []
        (if q.any id then q.reverse ++ target else target) := by
  have hs : run (q.length + 1) (cfg (some .scan) initial q [] target) =
      cfg (some .restore) ⟨q.any id, none⟩ [] q.reverse target := by
    simpa [initial] using scan_correct initial q [] target
  have hr := restore_correct (q.any id) [] q.reverse target
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have h := (run_add hs (q.length + 1)).trans hr
  cases hv : q.any id <;> simp only [hv, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · have hc := clear_correct false q target
    have h' := (run_add h (q.length + 1)).trans hc
    rw [show 3 * q.length + 3 =
      ((q.length + 1) + (q.length + 1)) + (q.length + 1) by omega]
    exact h'
  · have ht := transfer_correct true q target
    have h' := (run_add h (q.length + 1)).trans ht
    rw [show 3 * q.length + 3 =
      ((q.length + 1) + (q.length + 1)) + (q.length + 1) by omega]
    exact h'

theorem run_value (q target : List Bool) :
    run (3 * q.length + 3) (cfg (some .scan) initial q [] target) =
      cfg none ⟨(EncodedCommunication.bitsValue q != 0), none⟩ [] []
        (if EncodedCommunication.bitsValue q = 0 then target
          else q.reverse ++ target) := by
  rw [run_correct]
  have h := BitMachineBinaryZeroTest.any_false_iff_value_zero q
  cases hv : q.any id with
  | false =>
      have hz : EncodedCommunication.bitsValue q = 0 := h.mp hv
      simp [hv, hz]
  | true =>
      have hn : EncodedCommunication.bitsValue q ≠ 0 := by
        intro hz
        have : q.any id = false := h.mpr hz
        simp [hv] at this
      cases hvn : EncodedCommunication.bitsValue q with
      | zero => exact (hn hvn).elim
      | succ n => simp [hvn]

end EthInapproximability.CurrentPaper.PrimeSamplerBinaryQuotientAdvance
