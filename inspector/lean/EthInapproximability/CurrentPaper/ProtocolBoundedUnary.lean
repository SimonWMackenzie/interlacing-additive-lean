import EthInapproximability.CurrentPaper.ProtocolBinaryCounter
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Bounded conversion of binary values to unary counters

Source: locked v8 `03-exact-hardness.tex`, the NP verifier runtime.
Dimension fields are never expanded without first charging a literal input
budget. The program repeatedly tests for zero and subtracts one, at most once
per budget bit. All-zero padded binary words are treated as zero.
-/

namespace EthInapproximability.CurrentPaper.ProtocolBoundedUnary

open Turing Turing.TM2.Stmt BitMachineEncoding
open EncodedCommunication (bitsValue)

inductive Label where
  | zeroScan | zeroRestore | testCap | subtract | copy | restore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Bool

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Control
  | .zeroScan => pop 0 (fun s b => (b, s.2 || b.getD false))
      (branch (fun s => s.1.isSome)
        (push 2 (fun s => s.1.getD false) (goto (fun _ => .zeroScan)))
        (goto (fun _ => .zeroRestore)))
  | .zeroRestore => pop 2 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 0 (fun s => s.1.getD false) (goto (fun _ => .zeroRestore)))
        (branch Prod.snd (goto (fun _ => .testCap))
          (push 3 (fun _ => true) halt)))
  | .testCap => pop 1 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome) (goto (fun _ => .subtract))
        (push 3 (fun _ => false) halt))
  | .subtract => pop 0 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (branch (fun s => s.1.getD false)
          (push 2 (fun _ => false) (goto (fun _ => .copy)))
          (push 2 (fun _ => true) (goto (fun _ => .subtract)))) halt)
  | .copy => pop 0 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 2 (fun s => s.1.getD false) (goto (fun _ => .copy)))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun s b => (b, s.2))
      (branch (fun s => s.1.isSome)
        (push 0 (fun s => s.1.getD false) (goto (fun _ => .restore)))
        (push 3 (fun _ => true)
          (load (fun _ => (none, false)) (goto (fun _ => .zeroScan)))))

def stackContents (q cap work out : List Bool) : Fin 4 → List Bool :=
  fun k => if k = 0 then q else if k = 1 then cap else if k = 2 then work else out

@[simp] private theorem stack_zero (q cap work out : List Bool) :
    stackContents q cap work out 0 = q := rfl
@[simp] private theorem stack_one (q cap work out : List Bool) :
    stackContents q cap work out 1 = cap := rfl
@[simp] private theorem stack_two (q cap work out : List Bool) :
    stackContents q cap work out 2 = work := rfl
@[simp] private theorem stack_three (q cap work out : List Bool) :
    stackContents q cap work out 3 = out := rfl

def cfg (l : Option Label) (s : Control) (q cap work out : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) Label Control := ⟨l, s, stackContents q cap work out⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (s : Control) (b : Bool) (q cap work out : List Bool) :
    TM2.step program (cfg (some .zeroScan) s (b :: q) cap work out) =
      some (cfg (some .zeroScan) (some b, s.2 || b) q cap (b :: work) out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Control) (cap work out : List Bool) :
    TM2.step program (cfg (some .zeroScan) s [] cap work out) =
      some (cfg (some .zeroRestore) (none, s.2) [] cap work out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_zeroRestore_cons (s : Control) (b : Bool) (q cap work out : List Bool) :
    TM2.step program (cfg (some .zeroRestore) s q cap (b :: work) out) =
      some (cfg (some .zeroRestore) (some b, s.2) (b :: q) cap work out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_zeroRestore_nil (s : Control) (q cap out : List Bool) :
    TM2.step program (cfg (some .zeroRestore) s q cap [] out) =
      some (if s.2 then cfg (some .testCap) (none, true) q cap [] out
        else cfg none (none, false) q cap [] (true :: out)) := by
  rcases s with ⟨s, b⟩
  cases b <;> simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem scan_correct (s : Control) (q cap work out : List Bool) :
    run (q.length + 1) (cfg (some .zeroScan) s q cap work out) =
      cfg (some .zeroRestore) (none, s.2 || q.any id) [] cap (q.reverse ++ work) out := by
  induction q generalizing s work with
  | nil => simpa using run_succ (step_scan_nil s cap work out) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (step_scan_cons s b q cap work out), ih]
      simp [List.reverse_cons, List.append_assoc, Bool.or_assoc]

theorem zeroRestore_correct (s : Control) (q cap work out : List Bool) :
    run (work.length + 1) (cfg (some .zeroRestore) s q cap work out) =
      if s.2 then cfg (some .testCap) (none, true) (work.reverse ++ q) cap [] out
      else cfg none (none, false) (work.reverse ++ q) cap [] (true :: out) := by
  induction work generalizing s q with
  | nil => simpa using run_succ (step_zeroRestore_nil s q cap out) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_zeroRestore_cons s b q cap work out), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem zero_test (q cap out : List Bool) :
    run (2 * q.length + 2) (cfg (some .zeroScan) (none, false) q cap [] out) =
      if q.any id then cfg (some .testCap) (none, true) q cap [] out
      else cfg none (none, false) q cap [] (true :: out) := by
  have hs := scan_correct (none, false) q cap [] out
  simp only [Bool.false_or, List.append_nil] at hs
  have hr := zeroRestore_correct (none, q.any id) [] cap q.reverse out
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (run_add hs (q.length + 1)).trans hr

private theorem step_sub_false (s : Control) (q cap work out : List Bool) :
    TM2.step program (cfg (some .subtract) s (false :: q) cap work out) =
      some (cfg (some .subtract) (some false, s.2) q cap (true :: work) out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_sub_true (s : Control) (q cap work out : List Bool) :
    TM2.step program (cfg (some .subtract) s (true :: q) cap work out) =
      some (cfg (some .copy) (some true, s.2) q cap (false :: work) out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_copy_cons (s : Control) (b : Bool) (q cap work out : List Bool) :
    TM2.step program (cfg (some .copy) s (b :: q) cap work out) =
      some (cfg (some .copy) (some b, s.2) q cap (b :: work) out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_copy_nil (s : Control) (cap work out : List Bool) :
    TM2.step program (cfg (some .copy) s [] cap work out) =
      some (cfg (some .restore) (none, s.2) [] cap work out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_restore_cons (s : Control) (b : Bool) (q cap work out : List Bool) :
    TM2.step program (cfg (some .restore) s q cap (b :: work) out) =
      some (cfg (some .restore) (some b, s.2) (b :: q) cap work out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (q cap out : List Bool) :
    TM2.step program (cfg (some .restore) s q cap [] out) =
      some (cfg (some .zeroScan) (none, false) q cap [] (true :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem restore_correct (s : Control) (q cap work out : List Bool) :
    run (work.length + 1) (cfg (some .restore) s q cap work out) =
      cfg (some .zeroScan) (none, false) (work.reverse ++ q) cap [] (true :: out) := by
  induction work generalizing s q with
  | nil => simpa using run_succ (step_restore_nil s q cap out) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b q cap work out), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copy_correct (s : Control) (q cap work out : List Bool) :
    run (2 * q.length + work.length + 2) (cfg (some .copy) s q cap work out) =
      cfg (some .zeroScan) (none, false) (work.reverse ++ q) cap [] (true :: out) := by
  induction q generalizing s work with
  | nil =>
      rw [show 2 * ([] : List Bool).length + work.length + 2 =
        (work.length + 1) + 1 by simp,
        run_succ (step_copy_nil s cap work out), restore_correct]
  | cons b q ih =>
      rw [show 2 * (b :: q).length + work.length + 2 =
        (2 * q.length + (b :: work).length + 2) + 1 by simp; omega,
        run_succ (step_copy_cons s b q cap work out), ih]
      simp

theorem subtract_correct (s : Control) (q q' cap work out : List Bool)
    (hq : ProtocolBinaryCounter.subOne q = some q') :
    run (2 * q.length + work.length + 2) (cfg (some .subtract) s q cap work out) =
      cfg (some .zeroScan) (none, false) (work.reverse ++ q') cap [] (true :: out) := by
  induction q generalizing s q' work with
  | nil => simp [ProtocolBinaryCounter.subOne] at hq
  | cons b q ih =>
      cases b with
      | true =>
          simp only [ProtocolBinaryCounter.subOne, Option.some.injEq] at hq
          subst q'
          rw [show 2 * (true :: q).length + work.length + 2 =
            (2 * q.length + (false :: work).length + 2) + 1 by simp; omega,
            run_succ (step_sub_true s q cap work out), copy_correct]
          simp
      | false =>
          simp only [ProtocolBinaryCounter.subOne] at hq
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hq
          rw [show 2 * (false :: q).length + work.length + 2 =
            (2 * q.length + (true :: work).length + 2) + 1 by simp; omega,
            run_succ (step_sub_false s q cap work out), ih _ _ _ hr]
          simp

private theorem step_cap_nil (s : Control) (q out : List Bool) :
    TM2.step program (cfg (some .testCap) s q [] [] out) =
      some (cfg none (none, s.2) q [] [] (false :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_cap_cons (s : Control) (b : Bool) (q cap out : List Bool) :
    TM2.step program (cfg (some .testCap) s q (b :: cap) [] out) =
      some (cfg (some .subtract) (some b, s.2) q cap [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem any_eq_false_iff (q : List Bool) : q.any id = false ↔ bitsValue q = 0 := by
  induction q with
  | nil => simp [bitsValue]
  | cons b q ih =>
      cases b <;> simp [bitsValue, Nat.bit_val, ih]

def result (q cap out : List Bool) : List Bool :=
  decide (bitsValue q ≤ cap.length) ::
    (List.replicate (min (bitsValue q) cap.length) true ++ out)

/-- Every budget symbol authorizes at most one subtraction. The theorem
counts literal transitions and permits arbitrary binary padding and cap bits. -/
theorem bounded_run_framed (q cap out : List Bool) :
    ∃ t c, t ≤ (cap.length + 1) * (4 * q.length + 5) ∧
      run t (cfg (some .zeroScan) (none, false) q cap [] out) = c ∧
      c.l = none ∧ c.stk 3 = result q cap out ∧
      (c.stk 0).length = q.length ∧ c.stk 2 = [] ∧
      (c.stk 1).length ≤ cap.length := by
  induction cap generalizing q out with
  | nil =>
      by_cases hz : q.any id = false
      · have hv := (any_eq_false_iff q).mp hz
        refine ⟨2 * q.length + 2, cfg none (none, false) q [] [] (true :: out),
          by simp; omega, ?_, rfl, ?_, rfl, rfl, le_rfl⟩
        · simpa [hz] using zero_test q [] out
        · simp [cfg, result, hv]
      · have hb : q.any id = true := by cases h : q.any id <;> simp_all
        have hv : 0 < bitsValue q := by
          have := (any_eq_false_iff q).not.mp hz
          omega
        have hs : run (2 * q.length + 2)
            (cfg (some .zeroScan) (none, false) q [] [] out) =
              cfg (some .testCap) (none, true) q [] [] out := by
          simpa [hb] using zero_test q [] out
        have he := run_succ (step_cap_nil (none, true) q out) 0
        refine ⟨2 * q.length + 2 + 1, cfg none (none, true) q [] [] (false :: out),
          by simp; omega, (run_add hs 1).trans he, rfl, ?_, rfl, rfl, le_rfl⟩
        simp [cfg, result, Nat.ne_of_gt hv]
  | cons b cap ih =>
      by_cases hz : q.any id = false
      · have hv := (any_eq_false_iff q).mp hz
        refine ⟨2 * q.length + 2, cfg none (none, false) q (b :: cap) [] (true :: out),
          ?_, ?_, rfl, ?_, rfl, rfl, le_rfl⟩
        · simp only [List.length_cons]; nlinarith
        · simpa [hz] using zero_test q (b :: cap) out
        · simp [cfg, result, hv]
      · have hb : q.any id = true := by cases h : q.any id <;> simp_all
        have hv : 0 < bitsValue q := by
          have := (any_eq_false_iff q).not.mp hz
          omega
        have hspec := ProtocolBinaryCounter.subOne_spec q
        cases heq : ProtocolBinaryCounter.subOne q with
        | none => simp only [heq] at hspec; omega
        | some q' =>
            simp only [heq] at hspec
            obtain ⟨t, c, ht, hc, hhalt, hout, hlen, hwork, hcaplen⟩ := ih q' (true :: out)
            have hs : run (2 * q.length + 2)
                (cfg (some .zeroScan) (none, false) q (b :: cap) [] out) =
                  cfg (some .testCap) (none, true) q (b :: cap) [] out := by
              simpa [hb] using zero_test q (b :: cap) out
            have hcap := run_succ (step_cap_cons (none, true) b q cap out) 0
            have hsub := subtract_correct (some b, true) q q' cap [] out heq
            simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hsub
            have hpre := ((run_add hs 1).trans hcap)
            have hpre' := (run_add hpre (2 * q.length + 2)).trans hsub
            refine ⟨(2 * q.length + 2 + 1) + (2 * q.length + 2) + t, c,
              ?_, (run_add hpre' t).trans hc, hhalt, ?_, hlen.trans hspec.2,
              hwork, hcaplen.trans (by simp)⟩
            · rw [hspec.2] at ht
              simp only [List.length_cons]
              nlinarith
            · rw [hout]
              have hcmp : (bitsValue q' ≤ cap.length) =
                  (bitsValue q ≤ (b :: cap).length) := by
                simp only [List.length_cons]
                exact propext (by omega)
              have hmin : min (bitsValue q) (b :: cap).length =
                  min (bitsValue q') cap.length + 1 := by
                simp only [List.length_cons]
                omega
              simp only [result, hcmp, hmin, List.replicate_succ,
                List.cons_append]
              congr 1
              induction min (bitsValue q') cap.length with
              | zero => rfl
              | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (true :: ·) ih

theorem bounded_run (q cap out : List Bool) :
    ∃ t c, t ≤ (cap.length + 1) * (4 * q.length + 5) ∧
      run t (cfg (some .zeroScan) (none, false) q cap [] out) = c ∧
      c.l = none ∧ c.stk 3 = result q cap out := by
  obtain ⟨t, c, ht, hc, hl, ho, _⟩ := bounded_run_framed q cap out
  exact ⟨t, c, ht, hc, hl, ho⟩

theorem result_length (q cap out : List Bool) :
    (result q cap out).length = min (bitsValue q) cap.length + out.length + 1 := by
  simp [result, Nat.add_comm, Nat.add_left_comm]

theorem result_regressions :
    result [false, false] [false, false, true] [] = [true] ∧
    result [true, true] [false, false] [] = [false, true, true] ∧
    result [true, true] [false, false, false] [] = [true, true, true, true] ∧
    result [true, false, false] [] [] = [false] := by decide

end EthInapproximability.CurrentPaper.ProtocolBoundedUnary
