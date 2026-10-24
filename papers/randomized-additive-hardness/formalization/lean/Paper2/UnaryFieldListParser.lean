import Paper2.UnaryLabelParser

/-! A fixed-control physical parser for consecutive bounded-unary fields.
Stack 0 is unread input; 1 is the unary bound; 2 is unary fields-left;
3 restores consumed bound marks; 4 stores canonical field tokens in reverse
field order; 5 records a final success bit. The output of each successful
field is `true^v ++ [false]`, with no reversal *within* a token. -/

namespace Paper2.UnaryFieldListParserScratch

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open RecursiveLabelCodecScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

inductive Label where
  | start | fieldStart | read | checkTrue | checkFalse | restore | accept | reject
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control
  | .start =>
      pop 2 (fun _ mark => mark)
        (branch (fun mark => mark.isSome)
          (branch (fun mark => mark.getD false)
            (goto (fun _ => .fieldStart))
            (goto (fun _ => .reject)))
          (goto (fun _ => .accept)))
  | .fieldStart => push 4 (fun _ => false) (goto (fun _ => .read))
  | .read =>
      pop 0 (fun _ bit => bit)
        (branch (fun bit => bit.isSome)
          (branch (fun bit => bit.getD false)
            (goto (fun _ => .checkTrue))
            (goto (fun _ => .checkFalse)))
          (goto (fun _ => .reject)))
  | .checkTrue =>
      pop 1 (fun _ mark => mark)
        (branch (fun mark => mark.isSome && mark.getD false)
          (push 3 (fun _ => true)
            (push 4 (fun _ => true) (goto (fun _ => .read))))
          (goto (fun _ => .reject)))
  | .checkFalse =>
      pop 1 (fun _ mark => mark)
        (branch (fun mark => mark.isSome && mark.getD false)
          (push 3 (fun _ => true) (goto (fun _ => .restore)))
          (goto (fun _ => .reject)))
  | .restore =>
      pop 3 (fun _ mark => mark)
        (branch (fun mark => mark.isSome)
          (branch (fun mark => mark.getD false)
            (push 1 (fun _ => true) (goto (fun _ => .restore)))
            (goto (fun _ => .reject)))
          (goto (fun _ => .start)))
  | .accept => push 5 (fun _ => true) halt
  | .reject => push 5 (fun _ => false) halt

def contents (input cap count used output status : List Bool) : Fin 6 → List Bool :=
  fun i => if i = 0 then input else if i = 1 then cap else
    if i = 2 then count else if i = 3 then used else
      if i = 4 then output else status

def cfg (label : Option Label) (control : Control)
    (input cap count used output status : List Bool) :
    TM2.Cfg (fun _ : Fin 6 => Bool) Label Control :=
  ⟨label, control, contents input cap count used output status⟩

def initial (a N : ℕ) (input : List Bool) :=
  cfg (some .start) none input (List.replicate a true)
    (List.replicate N true) [] [] []

def run (steps : ℕ) (c : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) :=
  ((advance program)^[steps]) c

def tokens {a : ℕ} (xs : List (Fin a)) : List Bool :=
  xs.flatMap (finCodec a).encode

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_start_more (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .start) control
      input cap (true :: count) used output status) =
      some (cfg (some .fieldStart) (some true)
        input cap count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_start_done (control : Control)
    (input cap used output status : List Bool) :
    TM2.step program (cfg (some .start) control
      input cap [] used output status) =
      some (cfg (some .accept) none
        input cap [] used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_field_start (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .fieldStart) control
      input cap count used output status) =
      some (cfg (some .read) control
        input cap count used (false :: output) status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_read_true (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .read) control
      (true :: input) cap count used output status) =
      some (cfg (some .checkTrue) (some true)
        input cap count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_read_false (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .read) control
      (false :: input) cap count used output status) =
      some (cfg (some .checkFalse) (some false)
        input cap count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_read_nil (control : Control)
    (cap count used output status : List Bool) :
    TM2.step program (cfg (some .read) control
      [] cap count used output status) =
      some (cfg (some .reject) none
        [] cap count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_check_true (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .checkTrue) control
      input (true :: cap) count used output status) =
      some (cfg (some .read) (some true)
        input cap count (true :: used) (true :: output) status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_check_true_nil (control : Control)
    (input count used output status : List Bool) :
    TM2.step program (cfg (some .checkTrue) control
      input [] count used output status) =
      some (cfg (some .reject) none
        input [] count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_check_false (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .checkFalse) control
      input (true :: cap) count used output status) =
      some (cfg (some .restore) (some true)
        input cap count (true :: used) output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_check_false_nil (control : Control)
    (input count used output status : List Bool) :
    TM2.step program (cfg (some .checkFalse) control
      input [] count used output status) =
      some (cfg (some .reject) none
        input [] count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_restore_mark (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .restore) control
      input cap count (true :: used) output status) =
      some (cfg (some .restore) (some true)
        input (true :: cap) count used output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_restore_done (control : Control)
    (input cap count output status : List Bool) :
    TM2.step program (cfg (some .restore) control
      input cap count [] output status) =
      some (cfg (some .start) none
        input cap count [] output status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_accept (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .accept) control
      input cap count used output status) =
      some (cfg none control
        input cap count used output (true :: status)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_reject (control : Control)
    (input cap count used output status : List Bool) :
    TM2.step program (cfg (some .reject) control
      input cap count used output status) =
      some (cfg none control
        input cap count used output (false :: status)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem run_two_true (input cap count used output status : List Bool)
    (n : ℕ) :
    run (2 + n) (cfg (some .read) (some true)
      (true :: input) (true :: cap) count used output status) =
      run n (cfg (some .read) (some true)
        input cap count (true :: used) (true :: output) status) := by
  rw [show 2 + n = (n + 1) + 1 by omega,
    run_succ (step_read_true (some true) input (true :: cap)
      count used output status),
    run_succ (step_check_true (some true) input cap
      count used output status)]

private theorem replicate_true_comm (v : ℕ) (tail : List Bool) :
    List.replicate v true ++ true :: tail =
      true :: (List.replicate v true ++ tail) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate_succ, ih]

theorem run_true_prefix (v : ℕ)
    (input cap count used output status : List Bool) :
    run (2 * v) (cfg (some .read) (some true)
      (List.replicate v true ++ input)
      (List.replicate v true ++ cap) count used output status) =
      cfg (some .read) (some true) input cap count
        (List.replicate v true ++ used)
        (List.replicate v true ++ output) status := by
  induction v generalizing used output with
  | zero => simp [run]
  | succ v ih =>
      rw [show 2 * (v + 1) = 2 + 2 * v by omega]
      simp only [List.replicate_succ, List.cons_append]
      rw [run_two_true _ _ _ _ _ _ (2 * v), ih]
      rw [replicate_true_comm, replicate_true_comm]

private theorem run_false (input cap count used output status : List Bool) :
    run 2 (cfg (some .read) (some true)
      (false :: input) (true :: cap) count used output status) =
      cfg (some .restore) (some true)
        input cap count (true :: used) output status := by
  rw [show (2 : ℕ) = 1 + 1 by omega,
    run_succ (step_read_false (some true) input (true :: cap)
      count used output status),
    run_succ (step_check_false (some false) input cap
      count used output status)]
  rfl

theorem run_restore (v : ℕ)
    (input cap count output status : List Bool) :
    run (v + 1) (cfg (some .restore) (some true)
      input cap count (List.replicate v true) output status) =
      cfg (some .start) none input
        (List.replicate v true ++ cap) count [] output status := by
  induction v generalizing cap with
  | zero =>
      simpa only [Nat.zero_add, List.replicate_zero, List.nil_append, run] using
        (run_succ (step_restore_done (some true) input cap count output status) 0)
  | succ v ih =>
      rw [show v + 1 + 1 = (v + 1) + 1 by omega]
      simp only [List.replicate_succ]
      rw [run_succ (step_restore_mark (some true) input cap count
        (List.replicate v true) output status) (v + 1), ih]
      rw [replicate_true_comm]
      rfl

/-- One field consumes its delimiter, restores the physical cap, and prepends
its canonical `finCodec` token to the output stack. -/
theorem run_one (a v : ℕ) (hv : v < a)
    (rest count output status : List Bool) (control : Control) :
    run (3 * v + 6) (cfg (some .start) control
      (List.replicate v true ++ false :: rest)
      (List.replicate a true) (true :: count) [] output status) =
      cfg (some .start) none rest (List.replicate a true) count []
        (List.replicate v true ++ false :: output) status := by
  let rem := a - v - 1
  have ha : a = v + (rem + 1) := by dsimp [rem]; omega
  have hcap : List.replicate a true =
      List.replicate v true ++ true :: List.replicate rem true := by
    conv_lhs => rw [ha, List.replicate_add, List.replicate_succ]
  have hrestore : List.replicate (v + 1) true ++
      List.replicate rem true = List.replicate a true := by
    rw [← List.replicate_add]
    congr 1
    dsimp [rem]
    omega
  rw [show 3 * v + 6 = ((2 * v + (2 + (v + 2))) + 1) + 1 by omega,
    run_succ (step_start_more control _ _ _ _ _ _),
    run_succ (step_field_start (some true) _ _ _ _ _ _)]
  rw [hcap]
  rw [run_add (run_true_prefix v (false :: rest)
    (true :: List.replicate rem true) count [] (false :: output) status)
    (2 + (v + 2))]
  simp only [List.append_nil]
  rw [run_add (run_false rest (List.replicate rem true) count
    (List.replicate v true) (List.replicate v true ++ false :: output) status)
    (v + 2)]
  rw [show v + 2 = (v + 1) + 1 by omega]
  rw [show true :: List.replicate v true =
    List.replicate (v + 1) true by rfl]
  rw [run_restore (v + 1)]
  rw [hrestore, ← hcap]

def duration {a : ℕ} : List (Fin a) → ℕ
  | [] => 0
  | x :: xs => (3 * x.val + 6) + duration xs

/-- The actual TM2 transitions parse exactly the supplied list, preserve
the unconsumed suffix, and leave canonical tokens in reverse field order. -/
theorem run_fields {a : ℕ} (xs : List (Fin a))
    (rest count output status : List Bool) :
    run (duration xs) (cfg (some .start) none
      (tokens xs ++ rest) (List.replicate a true)
      (List.replicate xs.length true ++ count) [] output status) =
      cfg (some .start) none rest (List.replicate a true)
        count [] (tokens xs.reverse ++ output) status := by
  induction xs generalizing output with
  | nil => simp [run, duration, tokens]
  | cons x xs ih =>
      simp only [duration, tokens, List.flatMap_cons, List.length_cons,
        List.replicate_succ, List.cons_append, List.append_assoc]
      rw [show (finCodec a).encode x =
        List.replicate x.val true ++ [false] by rfl]
      rw [show (List.replicate x.val true ++ [false]) ++
          (xs.flatMap (finCodec a).encode ++ rest) =
          List.replicate x.val true ++
            false :: (xs.flatMap (finCodec a).encode ++ rest) by
            simp [List.append_assoc]]
      rw [run_add (run_one a x.val x.isLt
        (xs.flatMap (finCodec a).encode ++ rest)
        (List.replicate xs.length true ++ count) output status none)
        (duration xs)]
      rw [show List.replicate x.val true ++ false :: output =
        (finCodec a).encode x ++ output by
          simp [finCodec, List.append_assoc]]
      simpa [tokens, List.flatMap_append, List.append_assoc] using
        ih ((finCodec a).encode x ++ output)

private theorem run_finish (input cap output status : List Bool) :
    run 2 (cfg (some .start) none input cap [] [] output status) =
      cfg none none input cap [] [] output (true :: status) := by
  rw [show (2 : ℕ) = 1 + 1 by omega,
    run_succ (step_start_done none input cap [] output status),
    run_succ (step_accept none input cap [] [] output status)]
  rfl

/-- A complete valid list finishes in the displayed, exact physical clock. -/
theorem run_valid {a : ℕ} (xs : List (Fin a)) (rest : List Bool) :
    run (duration xs + 2) (initial a xs.length (tokens xs ++ rest)) =
      cfg none none rest (List.replicate a true) [] []
        (tokens xs.reverse) [true] := by
  unfold initial
  have hr : run (duration xs) (cfg (some .start) none
      (tokens xs ++ rest) (List.replicate a true)
      (List.replicate xs.length true) [] [] []) =
      cfg (some .start) none rest (List.replicate a true)
        [] [] (tokens xs.reverse) [] := by
    simpa only [List.append_nil] using run_fields xs rest [] [] []
  rw [run_add hr 2]
  simpa only [List.append_nil] using
    run_finish rest (List.replicate a true) (tokens xs.reverse) []

theorem run_truncated (a v : ℕ) (hv : v ≤ a)
    (count output status : List Bool) (control : Control) :
    run (2 * v + 4) (cfg (some .start) control
      (List.replicate v true) (List.replicate a true)
      (true :: count) [] output status) =
      cfg none none [] (List.replicate (a - v) true)
        count (List.replicate v true)
        (List.replicate v true ++ false :: output)
        (false :: status) := by
  have ha : a = v + (a - v) := by omega
  have hcap : List.replicate a true =
      List.replicate v true ++ List.replicate (a - v) true := by
    conv_lhs => rw [ha, List.replicate_add]
  rw [show 2 * v + 4 = ((2 * v + 2) + 1) + 1 by omega,
    run_succ (step_start_more control _ _ _ _ _ _),
    run_succ (step_field_start (some true) _ _ _ _ _ _), hcap]
  have hp : run (2 * v) (cfg (some .read) (some true)
      (List.replicate v true)
      (List.replicate v true ++ List.replicate (a - v) true)
      count [] (false :: output) status) =
      cfg (some .read) (some true) [] (List.replicate (a - v) true)
        count (List.replicate v true)
        (List.replicate v true ++ false :: output) status := by
    simpa only [List.append_nil] using
      run_true_prefix v [] (List.replicate (a - v) true)
        count [] (false :: output) status
  rw [run_add hp 2]
  rw [show (2 : ℕ) = 1 + 1 by omega,
    run_succ (step_read_nil (some true)
      (List.replicate (a - v) true) count
      (List.replicate v true)
      (List.replicate v true ++ false :: output) status),
    run_succ (step_reject none [] (List.replicate (a - v) true)
      count (List.replicate v true)
      (List.replicate v true ++ false :: output) status)]
  rfl

theorem run_exhausted_cons (a : ℕ) (bit : Bool) (rest count output status : List Bool)
    (control : Control) :
    run (2 * a + 5) (cfg (some .start) control
      (List.replicate a true ++ bit :: rest)
      (List.replicate a true) (true :: count) [] output status) =
      cfg none none rest [] count (List.replicate a true)
        (List.replicate a true ++ false :: output)
        (false :: status) := by
  rw [show 2 * a + 5 = ((2 * a + 3) + 1) + 1 by omega,
    run_succ (step_start_more control _ _ _ _ _ _),
    run_succ (step_field_start (some true) _ _ _ _ _ _)]
  have hp : run (2 * a) (cfg (some .read) (some true)
      (List.replicate a true ++ bit :: rest)
      (List.replicate a true) count [] (false :: output) status) =
      cfg (some .read) (some true) (bit :: rest) [] count
        (List.replicate a true)
        (List.replicate a true ++ false :: output) status := by
    simpa only [List.append_nil] using
      run_true_prefix a (bit :: rest) [] count [] (false :: output) status
  rw [run_add hp 3]
  cases bit with
  | false =>
      rw [show (3 : ℕ) = (1 + 1) + 1 by omega,
        run_succ (step_read_false (some true) rest [] count
          (List.replicate a true)
          (List.replicate a true ++ false :: output) status),
        run_succ (step_check_false_nil (some false) rest count
          (List.replicate a true)
          (List.replicate a true ++ false :: output) status),
        run_succ (step_reject none rest [] count
          (List.replicate a true)
          (List.replicate a true ++ false :: output) status)]
      rfl
  | true =>
      rw [show (3 : ℕ) = (1 + 1) + 1 by omega,
        run_succ (step_read_true (some true) rest [] count
          (List.replicate a true)
          (List.replicate a true ++ false :: output) status),
        run_succ (step_check_true_nil (some true) rest count
          (List.replicate a true)
          (List.replicate a true ++ false :: output) status),
        run_succ (step_reject none rest [] count
          (List.replicate a true)
          (List.replicate a true ++ false :: output) status)]
      rfl

theorem duration_eq {a : ℕ} (xs : List (Fin a)) :
    duration xs = 3 * (tokens xs).length + 3 * xs.length := by
  induction xs with
  | nil => simp [duration, tokens]
  | cons x xs ih =>
      simp only [duration, tokens, List.flatMap_cons, List.length_cons,
        List.length_append, ih]
      have hlen : ((finCodec a).encode x).length = x.val + 1 := by
        simp [finCodec]
      rw [hlen]
      omega

def fuel (a N : ℕ) (input : List Bool) : ℕ :=
  3 * (input.length + a + N) + 2

private theorem run_halted (control : Control)
    (input cap count used output status : List Bool) (n : ℕ) :
    run n (cfg none control input cap count used output status) =
      cfg none control input cap count used output status := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run, Function.iterate_succ_apply] at ih ⊢
      have hh : advance program
          (cfg none control input cap count used output status) =
          cfg none control input cap count used output status := rfl
      rw [hh]
      exact ih

/-- The displayed clock is polynomial in physically supplied input, bound,
and count lengths; it does not assume an indexed family of control states. -/
theorem run_valid_fuel {a : ℕ} (xs : List (Fin a)) (rest : List Bool) :
    run (fuel a xs.length (tokens xs ++ rest))
      (initial a xs.length (tokens xs ++ rest)) =
      cfg none none rest (List.replicate a true) [] []
        (tokens xs.reverse) [true] := by
  have hclock : duration xs + 2 ≤
      fuel a xs.length (tokens xs ++ rest) := by
    rw [duration_eq]
    simp only [fuel, List.length_append]
    omega
  rw [show fuel a xs.length (tokens xs ++ rest) =
      (duration xs + 2) +
        (fuel a xs.length (tokens xs ++ rest) - (duration xs + 2)) by omega,
    run_add (run_valid xs rest)]
  exact run_halted _ _ _ _ _ _ _ _

def decodeFields (a : ℕ) : (N : ℕ) → List Bool →
    Option (List (Fin a) × List Bool)
  | 0, bits => some ([], bits)
  | N + 1, bits => do
      let (x, rest) ← (finCodec a).decode bits
      let (xs, tail) ← decodeFields a N rest
      pure (x :: xs, tail)

theorem decodeFields_roundtrip {a : ℕ} (xs : List (Fin a))
    (rest : List Bool) :
    decodeFields a xs.length (tokens xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [tokens] at ih
      simp [decodeFields, tokens, List.append_assoc,
        PrefixCodec.roundtrip, ih]

def observed (c : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) :
    Option (List Bool × List Bool) :=
  if c.stk 5 = [true] then some (c.stk 4, c.stk 0) else none

theorem observed_valid {a : ℕ} (xs : List (Fin a))
    (rest : List Bool) :
    observed (run (fuel a xs.length (tokens xs ++ rest))
      (initial a xs.length (tokens xs ++ rest))) =
      some (tokens xs.reverse, rest) := by
  rw [run_valid_fuel]
  simp [observed, cfg, contents]

private theorem classify_input (a : ℕ) (bits : List Bool) :
    (∃ v rest, v < a ∧ bits = List.replicate v true ++ false :: rest) ∨
    (∃ v, v ≤ a ∧ bits = List.replicate v true) ∨
    (∃ suffix, bits = List.replicate a true ++ suffix) := by
  induction a generalizing bits with
  | zero =>
      exact Or.inr (Or.inr ⟨bits, by simp⟩)
  | succ a ih =>
      cases bits with
      | nil =>
          exact Or.inr (Or.inl ⟨0, by omega, rfl⟩)
      | cons bit rest =>
          cases bit with
          | false =>
              exact Or.inl ⟨0, rest, by omega, rfl⟩
          | true =>
              rcases ih rest with ⟨v, tail, hv, hrest⟩ |
                ⟨v, hv, hrest⟩ | ⟨tail, hrest⟩
              · exact Or.inl ⟨v + 1, tail, by omega,
                  by simp [hrest, List.replicate_succ]⟩
              · exact Or.inr (Or.inl ⟨v + 1, by omega,
                  by simp [hrest, List.replicate_succ]⟩)
              · exact Or.inr (Or.inr ⟨tail,
                  by simp [hrest, List.replicate_succ]⟩)

/-- All-input parser correspondence. A successful observation contains
canonical tokens in reverse field order and the exact unread suffix;
truncated or out-of-range fields yield `none`. -/
theorem observed_run_eq_decode (a N : ℕ) (bits output : List Bool) :
    observed (run (fuel a N bits)
      (cfg (some .start) none bits (List.replicate a true)
        (List.replicate N true) [] output [])) =
      (decodeFields a N bits).map (fun p =>
        (tokens p.1.reverse ++ output, p.2)) := by
  induction N generalizing bits output with
  | zero =>
      have hclock : 2 ≤ fuel a 0 bits := by simp [fuel]
      simp only [List.replicate_zero]
      rw [show fuel a 0 bits = 2 + (fuel a 0 bits - 2) by omega,
        run_add (run_finish bits (List.replicate a true) output [])]
      rw [run_halted]
      simp [observed, decodeFields, tokens, cfg, contents]
  | succ N ih =>
      simp only [List.replicate_succ]
      rcases classify_input a bits with ⟨v, rest, hv, rfl⟩ |
        ⟨v, hv, rfl⟩ | ⟨suffix, rfl⟩
      · let x : Fin a := ⟨v, hv⟩
        have hclock : fuel a (N + 1)
            (List.replicate v true ++ false :: rest) =
            (3 * v + 6) + fuel a N rest := by
          simp [fuel]
          omega
        rw [hclock]
        rw [run_add (run_one a v hv rest (List.replicate N true)
          output [] none) (fuel a N rest)]
        have henc : (finCodec a).encode x ++ output =
            List.replicate v true ++ false :: output := by
          simp [x, finCodec, List.append_assoc]
        rw [← henc]
        rw [ih rest ((finCodec a).encode x ++ output)]
        have hd := UnaryLabelParserScratch.finCodec_decode_valid a v hv rest
        cases ht : decodeFields a N rest with
        | none => simp [decodeFields, hd, ht]
        | some p =>
            obtain ⟨xs, tail⟩ := p
            simp [decodeFields, hd, ht, tokens, List.flatMap_append,
              List.append_assoc]
            rfl
      · have hclock : 2 * v + 4 ≤
            fuel a (N + 1) (List.replicate v true) := by
          simp [fuel]
          omega
        rw [show fuel a (N + 1) (List.replicate v true) =
            (2 * v + 4) +
              (fuel a (N + 1) (List.replicate v true) - (2 * v + 4)) by omega,
          run_add (run_truncated a v hv
            (List.replicate N true) output [] none), run_halted]
        simp [observed, decodeFields, cfg, contents,
          UnaryLabelParserScratch.finCodec_reject_truncated]
      · cases suffix with
        | nil =>
            simp only [List.append_nil]
            have hclock : 2 * a + 4 ≤
                fuel a (N + 1) (List.replicate a true) := by
              simp [fuel]
              omega
            rw [show fuel a (N + 1) (List.replicate a true) =
                (2 * a + 4) +
                  (fuel a (N + 1) (List.replicate a true) - (2 * a + 4)) by omega,
              run_add (run_truncated a a (le_refl a)
                (List.replicate N true) output [] none), run_halted]
            simp [observed, decodeFields, cfg, contents,
              UnaryLabelParserScratch.finCodec_reject_truncated]
        | cons bit rest =>
            have hclock : 2 * a + 5 ≤
                fuel a (N + 1) (List.replicate a true ++ bit :: rest) := by
              simp [fuel]
              omega
            rw [show fuel a (N + 1)
                (List.replicate a true ++ bit :: rest) =
                (2 * a + 5) +
                  (fuel a (N + 1)
                    (List.replicate a true ++ bit :: rest) - (2 * a + 5)) by omega,
              run_add (run_exhausted_cons a bit rest
                (List.replicate N true) output [] none), run_halted]
            simp [observed, decodeFields, cfg, contents,
              UnaryLabelParserScratch.finCodec_reject_exhausted]

theorem observed_initial_eq_decode (a N : ℕ) (bits : List Bool) :
    observed (run (fuel a N bits) (initial a N bits)) =
      (decodeFields a N bits).map (fun p => (tokens p.1.reverse, p.2)) := by
  simpa only [initial, List.append_nil] using
    observed_run_eq_decode a N bits []

/-- The physical stream is exactly the established structural tuple codec's
forward encoding, not a replacement serialization. -/
theorem piCodec_encode_eq_tokens (a : ℕ) :
    (N : ℕ) → (f : Fin N → Fin a) →
      (piCodec (finCodec a) N).encode f = tokens (List.ofFn f)
  | 0, f => by simp [piCodec, emptyPiCodec, tokens]
  | N + 1, f => by
      simp [piCodec, transportCodec, prodCodec, tokens,
        List.ofFn_succ, piCodec_encode_eq_tokens a N, Fin.tail_def]

theorem decodeFields_eq_piCodec (a : ℕ) :
    (N : ℕ) → (bits : List Bool) →
      decodeFields a N bits =
        ((piCodec (finCodec a) N).decode bits).map
          (fun p => (List.ofFn p.1, p.2))
  | 0, bits => by simp [decodeFields, piCodec, emptyPiCodec]
  | N + 1, bits => by
      cases hfirst : (finCodec a).decode bits with
      | none =>
          simp [decodeFields, piCodec, transportCodec, prodCodec, hfirst]
      | some p =>
          obtain ⟨x, rest⟩ := p
          cases htail : (piCodec (finCodec a) N).decode rest with
          | none =>
              have ih := decodeFields_eq_piCodec a N rest
              simp [htail] at ih
              simp [decodeFields, piCodec, transportCodec, prodCodec,
                hfirst, htail, ih]
          | some p =>
              obtain ⟨xs, tail⟩ := p
              have ih := decodeFields_eq_piCodec a N rest
              simp [htail] at ih
              simp [decodeFields, piCodec, transportCodec, prodCodec,
                hfirst, htail, ih, List.ofFn_succ]

/-- All-input correspondence to the *actual* structural `piCodec`, including
malformed rejection; the only change is reversing the order of whole output
tokens for the stack-prepend convention. -/
theorem observed_run_eq_piCodec (a N : ℕ) (bits : List Bool) :
    observed (run (fuel a N bits) (initial a N bits)) =
      ((piCodec (finCodec a) N).decode bits).map
        (fun p => (tokens (List.ofFn p.1).reverse, p.2)) := by
  rw [observed_initial_eq_decode, decodeFields_eq_piCodec]
  cases h : (piCodec (finCodec a) N).decode bits with
  | none => rfl
  | some p => rfl

theorem observed_actual_tuple (a N : ℕ) (f : Fin N → Fin a)
    (rest : List Bool) :
    observed (run (fuel a N
      ((piCodec (finCodec a) N).encode f ++ rest))
      (initial a N ((piCodec (finCodec a) N).encode f ++ rest))) =
      some (tokens (List.ofFn f).reverse, rest) := by
  rw [piCodec_encode_eq_tokens]
  simpa only [List.length_ofFn] using
    observed_valid (List.ofFn f) rest

/-- Every input reaches a halted TM2 configuration by the same charged
clock, including malformed, truncated, and out-of-range fields. -/
theorem run_fuel_halts_from (a N : ℕ) (bits output : List Bool) :
    (run (fuel a N bits)
      (cfg (some .start) none bits (List.replicate a true)
        (List.replicate N true) [] output [])).l = none := by
  induction N generalizing bits output with
  | zero =>
      have hclock : 2 ≤ fuel a 0 bits := by simp [fuel]
      simp only [List.replicate_zero]
      rw [show fuel a 0 bits = 2 + (fuel a 0 bits - 2) by omega,
        run_add (run_finish bits (List.replicate a true) output []),
        run_halted]
      rfl
  | succ N ih =>
      simp only [List.replicate_succ]
      rcases classify_input a bits with ⟨v, rest, hv, rfl⟩ |
        ⟨v, hv, rfl⟩ | ⟨suffix, rfl⟩
      · have hclock : fuel a (N + 1)
            (List.replicate v true ++ false :: rest) =
            (3 * v + 6) + fuel a N rest := by
          simp [fuel]
          omega
        rw [hclock, run_add (run_one a v hv rest
          (List.replicate N true) output [] none) (fuel a N rest)]
        exact ih rest (List.replicate v true ++ false :: output)
      · have hclock : 2 * v + 4 ≤
            fuel a (N + 1) (List.replicate v true) := by
          simp [fuel]
          omega
        rw [show fuel a (N + 1) (List.replicate v true) =
            (2 * v + 4) +
              (fuel a (N + 1) (List.replicate v true) - (2 * v + 4)) by omega,
          run_add (run_truncated a v hv
            (List.replicate N true) output [] none), run_halted]
        rfl
      · cases suffix with
        | nil =>
            simp only [List.append_nil]
            have hclock : 2 * a + 4 ≤
                fuel a (N + 1) (List.replicate a true) := by
              simp [fuel]
              omega
            rw [show fuel a (N + 1) (List.replicate a true) =
                (2 * a + 4) +
                  (fuel a (N + 1) (List.replicate a true) - (2 * a + 4)) by omega,
              run_add (run_truncated a a (le_refl a)
                (List.replicate N true) output [] none), run_halted]
            rfl
        | cons bit rest =>
            have hclock : 2 * a + 5 ≤
                fuel a (N + 1) (List.replicate a true ++ bit :: rest) := by
              simp [fuel]
              omega
            rw [show fuel a (N + 1)
                (List.replicate a true ++ bit :: rest) =
                (2 * a + 5) +
                  (fuel a (N + 1)
                    (List.replicate a true ++ bit :: rest) - (2 * a + 5)) by omega,
              run_add (run_exhausted_cons a bit rest
                (List.replicate N true) output [] none), run_halted]
            rfl

theorem run_fuel_halts (a N : ℕ) (bits : List Bool) :
    (run (fuel a N bits) (initial a N bits)).l = none :=
  run_fuel_halts_from a N bits []

end Paper2.UnaryFieldListParserScratch
