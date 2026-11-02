import EthInapproximability.CurrentPaper.SamplerEnumeration
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Actual fixed-width binary-word enumeration

Source: locked v8 Appendix E, `lem:exact-families`. Four Boolean stacks
hold a coefficient counter, its temporary reverse, a reversed output,
and the final output. Every coefficient is copied by actual instructions.
The all-ones stop flag is accumulated while copying, so the program has
fixed finite control and does not assume a supplied exponential loop count.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineEnumeration

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open SamplerMachineIncrement SamplerEnumeration

inductive Admin where
  | scan | restore | reverse
  deriving DecidableEq, Fintype

abbrev Stack := Fin 2 ⊕ Fin 2
abbrev Label := SamplerMachineIncrement.Label ⊕ Admin
abbrev Control := Option Bool × Option Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (none, none, true)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .scan) (SamplerMachineIncrement.program l)
  | .inr .scan => pop (.inl 0) (fun s b => (s.1, b, s.2.2))
      (branch (fun s => s.2.1.isSome)
        (push (.inl 1) (fun s => s.2.1.getD false)
          (push (.inr 0) (fun s => s.2.1.getD false)
            (load (fun s => (s.1, s.2.1, s.2.2 && s.2.1.getD false))
              (goto (fun _ => .inr .scan)))))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inl 1) (fun s b => (s.1, b, s.2.2))
      (branch (fun s => s.2.1.isSome)
        (push (.inl 0) (fun s => s.2.1.getD false) (goto (fun _ => .inr .restore)))
        (branch (fun s => s.2.2)
          (load (fun _ => initial) (goto (fun _ => .inr .reverse)))
          (load (fun _ => initial) (goto (fun _ => .inl .carry)))))
  | .inr .reverse => pop (.inr 0) (fun s b => (s.1, b, s.2.2))
      (branch (fun s => s.2.1.isSome)
        (push (.inr 1) (fun s => s.2.1.getD false) (goto (fun _ => .inr .reverse)))
        (load (fun _ => initial) halt))

def foreign (rev out : List Bool) : Fin 2 → List Bool := fun k => if k = 0 then rev else out

def cfg (l : Option Label) (s : Control) (q work rev out : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineIncrement.stackContents q work) (foreign rev out)⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_scan_cons (s : Control) (b : Bool) (q work rev out : List Bool) :
    TM2.step program (cfg (some (.inr .scan)) s (b :: q) work rev out) =
      some (cfg (some (.inr .scan)) (s.1, some b, s.2.2 && b)
        q (b :: work) (b :: rev) out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineIncrement.stackContents,
    foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

private theorem step_scan_nil (s : Control) (work rev out : List Bool) :
    TM2.step program (cfg (some (.inr .scan)) s [] work rev out) =
      some (cfg (some (.inr .restore)) (s.1, none, s.2.2) [] work rev out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineIncrement.stackContents,
    foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

private theorem step_restore_cons (s : Control) (b : Bool) (q work rev out : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s q (b :: work) rev out) =
      some (cfg (some (.inr .restore)) (s.1, some b, s.2.2) (b :: q) work rev out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineIncrement.stackContents,
    foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (q rev out : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s q [] rev out) =
      some (cfg (some (if s.2.2 then .inr .reverse else .inl .carry)) initial q [] rev out) := by
  cases h : s.2.2 <;>
    dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineIncrement.stackContents,
      foreign, Sum.elim_inl, Sum.elim_inr]
  all_goals
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false, Option.some.injEq, h, Bool.cond_true]
    congr 1
    funext k
    rcases k with k | k <;> fin_cases k <;> rfl

private theorem step_reverse_cons (s : Control) (b : Bool) (q work rev out : List Bool) :
    TM2.step program (cfg (some (.inr .reverse)) s q work (b :: rev) out) =
      some (cfg (some (.inr .reverse)) (s.1, some b, s.2.2) q work rev (b :: out)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineIncrement.stackContents,
    foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

private theorem step_reverse_nil (s : Control) (q work out : List Bool) :
    TM2.step program (cfg (some (.inr .reverse)) s q work [] out) =
      some (cfg none initial q work [] out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineIncrement.stackContents,
    foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

theorem scan_run (s : Control) (q work rev out : List Bool) :
    run (q.length + 1) (cfg (some (.inr .scan)) s q work rev out) =
      cfg (some (.inr .restore)) (s.1, none, s.2.2 && q.all id)
        [] (q.reverse ++ work) (q.reverse ++ rev) out := by
  induction q generalizing s work rev with
  | nil => simpa using run_succ (step_scan_nil s work rev out) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (step_scan_cons s b q work rev out)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.all_cons, id_eq, Bool.and_assoc] using
          ih (s.1, some b, s.2.2 && b) (b :: work) (b :: rev)

theorem restore_run (s : Control) (q work rev out : List Bool) :
    run (work.length + 1) (cfg (some (.inr .restore)) s q work rev out) =
      cfg (some (if s.2.2 then .inr .reverse else .inl .carry)) initial
        (work.reverse ++ q) [] rev out := by
  induction work generalizing s q with
  | nil => simpa using run_succ (step_restore_nil s q rev out) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b q work rev out)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, some b, s.2.2) (b :: q)

theorem emit_run (q rev out : List Bool) :
    run (2 * q.length + 2) (cfg (some (.inr .scan)) initial q [] rev out) =
      cfg (some (if q.all id then .inr .reverse else .inl .carry)) initial
        q [] (q.reverse ++ rev) out := by
  have hs := scan_run initial q [] rev out
  simp only [initial, Bool.true_and, List.append_nil] at hs
  have hr := restore_run (none, none, q.all id) [] q.reverse (q.reverse ++ rev) out
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * q.length + 2 = (q.length + 1) + (q.length + 1) by omega]
  simp only [initial] at ⊢
  simp only [run, Function.iterate_add_apply] at hs hr ⊢
  rw [hs, hr]
  rfl

theorem reverse_run (s : Control) (q work rev out : List Bool) :
    run (rev.length + 1) (cfg (some (.inr .reverse)) s q work rev out) =
      cfg none initial q work [] (rev.reverse ++ out) := by
  induction rev generalizing s out with
  | nil => simpa using run_succ (step_reverse_nil s q work out) 0
  | cons b rev ih =>
      rw [List.length_cons, run_succ (step_reverse_cons s b q work rev out)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, some b, s.2.2) (b :: out)

theorem increment_call (q rev out : List Bool) :
    ∃ t ≤ 2 * q.length + 2,
      run t (cfg (some (.inl .carry)) initial q [] rev out) =
        cfg (some (.inr .scan)) initial (increment q) [] rev out := by
  have hr := SamplerMachineIncrement.run_correct none q []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at hr
  have hh : (SamplerMachineIncrement.run (2 * carryCount q + 2)
      (SamplerMachineIncrement.cfg (some .carry) none q [])).l = none := by
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineIncrement.program program (some .scan) (fun _ => rfl)
    (none, true) (foreign rev out)
    (SamplerMachineIncrement.cfg (some .carry) none q []) (2 * carryCount q + 2) hh
  refine ⟨t, ht.trans (by have := carryCount_le_length q; omega), ?_⟩
  change ((advance program)^[t]) _ = _
  change ((advance program)^[t]) _ = liftCfg (some .scan) (none, true) (foreign rev out)
    (SamplerMachineIncrement.run (2 * carryCount q + 2) _) at hrun
  rw [hr] at hrun
  exact hrun

theorem overflow_iff_max (q : List Bool) :
    q.all id = true ↔ EncodedCommunication.bitsValue q + 1 = 2 ^ q.length := by
  have h := increment_value_with_overflow q
  have hq := bitsValue_lt q
  have hi := bitsValue_lt (increment q)
  rw [increment_length] at hi
  cases he : q.all id <;> simp [overflow, he] at h ⊢ <;> omega

theorem increment_value_of_not_overflow (q : List Bool) (hq : q.all id = false) :
    EncodedCommunication.bitsValue (increment q) = EncodedCommunication.bitsValue q + 1 := by
  simpa only [overflow, hq, Bool.false_eq_true, if_false, Nat.add_zero] using
    increment_value_with_overflow q

/-- Emit every remaining fixed-width counter through the final all-ones word.
The output is reversed until the last linear cleanup pass. -/
theorem stream_run (r : ℕ) (q rev out : List Bool)
    (hq : EncodedCommunication.bitsValue q + r + 1 = 2 ^ q.length) :
    ∃ t ≤ (r + 1) * (4 * q.length + 4),
      run t (cfg (some (.inr .scan)) initial q [] rev out) =
        cfg (some (.inr .reverse)) initial ((increment^[r]) q) []
          ((List.iterate increment q (r + 1)).flatten.reverse ++ rev) out := by
  induction r generalizing q rev with
  | zero =>
      have ho : q.all id = true := (overflow_iff_max q).mpr (by simpa using hq)
      refine ⟨2 * q.length + 2, by omega, ?_⟩
      simpa only [ho, if_true, Function.iterate_zero_apply,
        List.iterate, List.flatten_cons, List.flatten_nil, List.append_nil] using emit_run q rev out
  | succ r ih =>
      have ho : q.all id = false := by
        cases he : q.all id
        · rfl
        · have hm := (overflow_iff_max q).mp he
          omega
      have hnext : EncodedCommunication.bitsValue (increment q) + r + 1 =
          2 ^ (increment q).length := by
        rw [increment_length, increment_value_of_not_overflow q ho]
        omega
      have hemit := emit_run q rev out
      simp only [ho, Bool.false_eq_true, if_false] at hemit
      obtain ⟨ts, hts, hs⟩ := increment_call q (q.reverse ++ rev) out
      obtain ⟨tr, htr, hr⟩ := ih (increment q) (q.reverse ++ rev) hnext
      refine ⟨tr + ts + (2 * q.length + 2), ?_, ?_⟩
      · rw [increment_length] at htr
        nlinarith
      · simp only [run, Function.iterate_add_apply]
        change run tr (run ts (run (2 * q.length + 2) _)) = _
        rw [hemit, hs, hr]
        simp only [Function.iterate_succ_apply, List.iterate, List.flatten_cons,
          List.reverse_append, List.append_assoc, Function.iterate_zero_apply]

theorem iterate_flatten_length (q : List Bool) (k : ℕ) :
    (List.iterate increment q k).flatten.length = k * q.length := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
      simp only [List.iterate, List.flatten_cons, List.length_append, ih, increment_length]
      ring

/-- Complete raw-bank enumeration. Every output block has the original width,
and the block order is exactly the existing executable `allWords` order. -/
theorem run_counterWords (n : ℕ) :
    ∃ t ≤ (2 ^ n) * (5 * n + 4) + 1,
      run t (cfg (some (.inr .scan)) initial (List.replicate n false) [] [] []) =
        cfg none initial ((increment^[2 ^ n - 1]) (List.replicate n false)) [] []
          (counterWords n).flatten := by
  have hpos : 0 < 2 ^ n := by positivity
  have hzero : EncodedCommunication.bitsValue (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [EncodedCommunication.bitsValue, List.replicate_succ, ih, Nat.bit_val]
  have hcount : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  obtain ⟨ts, hts, hs⟩ := stream_run (2 ^ n - 1) (List.replicate n false) [] [] (by
    rw [hzero, List.length_replicate]
    omega)
  simp only [List.length_replicate, hcount, List.append_nil] at hts hs
  have hr := reverse_run initial ((increment^[2 ^ n - 1]) (List.replicate n false)) []
    (List.iterate increment (List.replicate n false) (2 ^ n)).flatten.reverse []
  simp only [List.length_reverse, iterate_flatten_length, List.length_replicate,
    List.reverse_reverse, List.append_nil] at hr
  refine ⟨(2 ^ n * n + 1) + ts, by nlinarith, ?_⟩
  simp only [run, Function.iterate_add_apply]
  change run (2 ^ n * n + 1) (run ts _) = _
  rw [hs, hr]
  rfl

theorem run_allWords (n : ℕ) :
    ∃ t ≤ (2 ^ n) * (5 * n + 4) + 1,
      run t (cfg (some (.inr .scan)) initial (List.replicate n false) [] [] []) =
        cfg none initial ((increment^[2 ^ n - 1]) (List.replicate n false)) [] []
          ((ExecutableSmallBiasSampler.allWords n).map SamplerMachine.encodeWord).flatten := by
  simpa only [counterWords_eq] using run_counterWords n

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (.inl (0 : Fin 2) : Stack) (.inr 1) (.inr .scan : Label) initial program

private theorem initial_eq (q : List Bool) :
    rawInit (.inl (0 : Fin 2) : Stack) (.inr .scan : Label) initial q =
      cfg (some (.inr .scan)) initial q [] [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  rcases k with k | k <;> fin_cases k <;> rfl

/-- The standard bit-machine wrapper takes the supplied all-zero coefficient
word and outputs the explicit fixed-width enumeration. Runtime is measured
in the unavoidable output scale, not asserted polynomial in `n` alone. -/
theorem bitMachine_outputs (n : ℕ) :
    bitMachine.OutputsWithin (List.replicate n false) (counterWords n).flatten
      (2 ^ n * (5 * n + 4) + 1) := by
  obtain ⟨t, ht, hr⟩ := run_counterWords n
  apply outputsWithin_of_raw_run (.inl (0 : Fin 2) : Stack) (.inr 1)
    (.inr .scan : Label) initial program (List.replicate n false) (counterWords n).flatten
    t (2 ^ n * (5 * n + 4) + 1) ht
  · change (run t _).l = none
    rw [initial_eq, hr]
    rfl
  · change (run t _).stk (.inr 1) = (counterWords n).flatten
    rw [initial_eq, hr]
    rfl

end EthInapproximability.CurrentPaper.SamplerMachineEnumeration
