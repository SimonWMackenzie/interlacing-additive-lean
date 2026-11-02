import Paper2.RecursiveLabelCodec
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A physical four-stack, fixed-control parser for the bounded unary
`Fin` field of the recursive source-label codec. Stack 0 is unread input,
stack 1 is a supplied unary bound, stack 2 accumulates the unary value,
and stack 3 receives one acceptance bit. -/

namespace Paper2.UnaryLabelParserScratch

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open RecursiveLabelCodecScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

inductive Label where
  | read | checkTrue | checkFalse | accept | reject
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Control
  | .read =>
      pop 0 (fun _ bit => bit)
        (branch (fun bit => bit.isSome)
          (branch (fun bit => bit.getD false)
            (goto (fun _ => .checkTrue))
            (goto (fun _ => .checkFalse)))
          (goto (fun _ => .reject)))
  | .checkTrue =>
      pop 1 (fun _ cap => cap)
        (branch (fun cap => cap.isSome)
          (push 2 (fun _ => true) (goto (fun _ => .read)))
          (goto (fun _ => .reject)))
  | .checkFalse =>
      pop 1 (fun _ cap => cap)
        (branch (fun cap => cap.isSome)
          (goto (fun _ => .accept))
          (goto (fun _ => .reject)))
  | .accept => push 3 (fun _ => true) halt
  | .reject => push 3 (fun _ => false) halt

def stackContents (input cap value status : List Bool) : Fin 4 → List Bool :=
  fun i => if i = 0 then input else if i = 1 then cap else
    if i = 2 then value else status

@[simp] private theorem stack_zero (input cap value status : List Bool) :
    stackContents input cap value status 0 = input := rfl
@[simp] private theorem stack_one (input cap value status : List Bool) :
    stackContents input cap value status 1 = cap := rfl
@[simp] private theorem stack_two (input cap value status : List Bool) :
    stackContents input cap value status 2 = value := rfl
@[simp] private theorem stack_three (input cap value status : List Bool) :
    stackContents input cap value status 3 = status := rfl

def cfg (l : Option Label) (control : Control)
    (input cap value status : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) Label Control :=
  ⟨l, control, stackContents input cap value status⟩

def run (steps : ℕ) (c : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control) :=
  ((advance program)^[steps]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_read_true (control : Control)
    (input cap value status : List Bool) :
    TM2.step program (cfg (some .read) control
      (true :: input) cap value status) =
      some (cfg (some .checkTrue) (some true)
        input cap value status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext i
  fin_cases i <;> rfl

private theorem step_read_false (control : Control)
    (input cap value status : List Bool) :
    TM2.step program (cfg (some .read) control
      (false :: input) cap value status) =
      some (cfg (some .checkFalse) (some false)
        input cap value status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext i
  fin_cases i <;> rfl

private theorem step_read_nil (control : Control)
    (cap value status : List Bool) :
    TM2.step program (cfg (some .read) control [] cap value status) =
      some (cfg (some .reject) none [] cap value status) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_true_cons (control : Control) (bit : Bool)
    (input cap value status : List Bool) :
    TM2.step program (cfg (some .checkTrue) control
      input (bit :: cap) value status) =
      some (cfg (some .read) (some bit)
        input cap (true :: value) status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext i
  fin_cases i <;> rfl

private theorem step_true_nil (control : Control)
    (input value status : List Bool) :
    TM2.step program (cfg (some .checkTrue) control
      input [] value status) =
      some (cfg (some .reject) none input [] value status) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_false_cons (control : Control) (bit : Bool)
    (input cap value status : List Bool) :
    TM2.step program (cfg (some .checkFalse) control
      input (bit :: cap) value status) =
      some (cfg (some .accept) (some bit) input cap value status) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext i
  fin_cases i <;> rfl

private theorem step_false_nil (control : Control)
    (input value status : List Bool) :
    TM2.step program (cfg (some .checkFalse) control
      input [] value status) =
      some (cfg (some .reject) none input [] value status) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_accept (control : Control)
    (input cap value status : List Bool) :
    TM2.step program (cfg (some .accept) control input cap value status) =
      some (cfg none control input cap value (true :: status)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext i
  fin_cases i <;> rfl

private theorem step_reject (control : Control)
    (input cap value status : List Bool) :
    TM2.step program (cfg (some .reject) control input cap value status) =
      some (cfg none control input cap value (false :: status)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext i
  fin_cases i <;> rfl

private theorem run_two_true (input cap value status : List Bool) (n : ℕ) :
    run (2 + n) (cfg (some .read) (some true)
      (true :: input) (true :: cap) value status) =
      run n (cfg (some .read) (some true)
        input cap (true :: value) status) := by
  rw [show 2 + n = (n + 1) + 1 by omega,
    run_succ (step_read_true (some true) input (true :: cap) value status),
    run_succ (step_true_cons (some true) true input cap value status)]

private theorem replicate_true_comm (v : ℕ) (tail : List Bool) :
    List.replicate v true ++ true :: tail =
      true :: (List.replicate v true ++ tail) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate_succ, ih]

/-- Each unary input symbol consumes one physical input cell and one cap
cell, while writing one physical output cell. -/
theorem run_true_prefix (v : ℕ) (rest cap value status : List Bool) :
    run (2 * v) (cfg (some .read) (some true)
      (List.replicate v true ++ rest)
      (List.replicate v true ++ cap) value status) =
      cfg (some .read) (some true) rest cap
        (List.replicate v true ++ value) status := by
  induction v generalizing value with
  | zero => simp [run]
  | succ v ih =>
      rw [show 2 * (v + 1) = 2 + 2 * v by omega]
      simp only [List.replicate_succ, List.cons_append]
      rw [run_two_true _ _ _ _ (2 * v), ih]
      rw [replicate_true_comm]

private theorem run_false_success (bit : Bool)
    (rest cap value status : List Bool) :
    run 3 (cfg (some .read) (some true)
      (false :: rest) (bit :: cap) value status) =
      cfg none (some bit) rest cap value (true :: status) := by
  rw [show (3 : ℕ) = (1 + 1) + 1 by omega,
    run_succ (step_read_false (some true) rest (bit :: cap) value status),
    run_succ (step_false_cons (some false) bit rest cap value status),
    run_succ (step_accept (some bit) rest cap value status)]
  rfl

private theorem run_empty_reject (cap value status : List Bool) :
    run 2 (cfg (some .read) (some true) [] cap value status) =
      cfg none none [] cap value (false :: status) := by
  rw [show (2 : ℕ) = 1 + 1 by omega,
    run_succ (step_read_nil (some true) cap value status),
    run_succ (step_reject none [] cap value status)]
  rfl

private theorem run_exhausted_reject (bit : Bool)
    (rest value status : List Bool) :
    run 3 (cfg (some .read) (some true)
      (bit :: rest) [] value status) =
      cfg none none rest [] value (false :: status) := by
  cases bit with
  | false =>
      rw [show (3 : ℕ) = (1 + 1) + 1 by omega,
        run_succ (step_read_false (some true) rest [] value status),
        run_succ (step_false_nil (some false) rest value status),
        run_succ (step_reject none rest [] value status)]
      rfl
  | true =>
      rw [show (3 : ℕ) = (1 + 1) + 1 by omega,
        run_succ (step_read_true (some true) rest [] value status),
        run_succ (step_true_nil (some true) rest value status),
        run_succ (step_reject none rest [] value status)]
      rfl

def initial (a : ℕ) (input : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) Label Control :=
  cfg (some .read) (some true) input (List.replicate a true) [] []

/-- A valid `Fin a` token is parsed in exactly `2*v+3` physical TM2
transitions. The arbitrary suffix remains the unread input stack. -/
theorem run_valid (a v : ℕ) (hv : v < a) (rest : List Bool) :
    run (2 * v + 3)
      (initial a (List.replicate v true ++ false :: rest)) =
      cfg none (some true) rest (List.replicate (a - v - 1) true)
        (List.replicate v true) [true] := by
  have ha : a = v + ((a - v - 1) + 1) := by omega
  have hcap : List.replicate a true =
      List.replicate v true ++ true :: List.replicate (a - v - 1) true := by
    conv_lhs => rw [ha, List.replicate_add, List.replicate_succ]
  unfold initial
  rw [hcap]
  rw [run_add (run_true_prefix v (false :: rest)
    (true :: List.replicate (a - v - 1) true) [] []) 3]
  simpa only [List.append_nil] using
    run_false_success true rest (List.replicate (a - v - 1) true)
      (List.replicate v true) []

private theorem decodeUnary_word (v : ℕ) (rest : List Bool) :
    decodeUnary (List.replicate v true ++ false :: rest) =
      some (v, rest) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate, decodeUnary, ih]

theorem finCodec_decode_valid (a v : ℕ) (hv : v < a)
    (rest : List Bool) :
    (finCodec a).decode (List.replicate v true ++ false :: rest) =
      some ((⟨v, hv⟩ : Fin a), rest) := by
  simp [finCodec, decodeUnary_word, hv]

/-- The accepting machine result is the same value and suffix returned by
the actual recursive-label codec. -/
theorem run_valid_matches_codec (a v : ℕ) (hv : v < a)
    (rest : List Bool) :
    (finCodec a).decode (List.replicate v true ++ false :: rest) =
      some ((⟨v, hv⟩ : Fin a), rest) ∧
    run (2 * v + 3)
      (initial a (List.replicate v true ++ false :: rest)) =
      cfg none (some true) rest (List.replicate (a - v - 1) true)
        (List.replicate v true) [true] :=
  ⟨finCodec_decode_valid a v hv rest, run_valid a v hv rest⟩

/-- A missing delimiter is rejected after the input prefix is consumed. -/
theorem run_truncated (a v : ℕ) (hv : v ≤ a) :
    run (2 * v + 2) (initial a (List.replicate v true)) =
      cfg none none [] (List.replicate (a - v) true)
        (List.replicate v true) [false] := by
  have ha : a = v + (a - v) := by omega
  have hcap : List.replicate a true =
      List.replicate v true ++ List.replicate (a - v) true := by
    conv_lhs => rw [ha, List.replicate_add]
  unfold initial
  rw [hcap]
  have hp : run (2 * v)
      (cfg (some .read) (some true) (List.replicate v true)
        (List.replicate v true ++ List.replicate (a - v) true) [] []) =
      cfg (some .read) (some true) [] (List.replicate (a - v) true)
        (List.replicate v true) [] := by
    simpa only [List.append_nil] using
      run_true_prefix v [] (List.replicate (a - v) true) [] []
  rw [run_add hp 2]
  simpa only [List.append_nil] using
    run_empty_reject (List.replicate (a - v) true)
      (List.replicate v true) []

/-- Once all `a` cap cells have been consumed, any next symbol rejects,
including the delimiter itself. The remainder after that symbol is untouched. -/
theorem run_exhausted_cons (a : ℕ) (bit : Bool) (rest : List Bool) :
    run (2 * a + 3)
      (initial a (List.replicate a true ++ bit :: rest)) =
      cfg none none rest [] (List.replicate a true) [false] := by
  unfold initial
  have hp : run (2 * a)
      (cfg (some .read) (some true) (List.replicate a true ++ bit :: rest)
        (List.replicate a true) [] []) =
      cfg (some .read) (some true) (bit :: rest) []
        (List.replicate a true) [] := by
    simpa only [List.append_nil] using
      run_true_prefix a (bit :: rest) [] [] []
  rw [run_add hp 3]
  simpa only [List.append_nil] using
    run_exhausted_reject bit rest (List.replicate a true) []

theorem run_exhausted_nil (a : ℕ) :
    run (2 * a + 2) (initial a (List.replicate a true)) =
      cfg none none [] [] (List.replicate a true) [false] := by
  simpa using run_truncated a a (le_refl a)

private theorem decodeUnary_truncated (v : ℕ) :
    decodeUnary (List.replicate v true) = none := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate, decodeUnary, ih]

theorem finCodec_reject_truncated (a v : ℕ) :
    (finCodec a).decode (List.replicate v true) = none := by
  simp [finCodec, decodeUnary_truncated]

theorem finCodec_reject_out_of_range (a v : ℕ) (h : a ≤ v)
    (rest : List Bool) :
    (finCodec a).decode (List.replicate v true ++ false :: rest) = none := by
  simp [finCodec, decodeUnary_word, Nat.not_lt.mpr h]

private theorem run_halted (control : Control)
    (input cap value status : List Bool) (n : ℕ) :
    run n (cfg none control input cap value status) =
      cfg none control input cap value status := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [run, Function.iterate_succ_apply] at ih ⊢
      have hh : advance program (cfg none control input cap value status) =
          cfg none control input cap value status := rfl
      rw [hh]
      exact ih

/-- This is a literal TM2 transition allocation, linear in the physical
input and the physically supplied unary bound. -/
def fuel (a : ℕ) (input : List Bool) : ℕ :=
  2 * (input.length + a) + 3

theorem run_valid_fuel (a v : ℕ) (hv : v < a) (rest : List Bool) :
    run (fuel a (List.replicate v true ++ false :: rest))
      (initial a (List.replicate v true ++ false :: rest)) =
      cfg none (some true) rest (List.replicate (a - v - 1) true)
        (List.replicate v true) [true] := by
  let input := List.replicate v true ++ false :: rest
  have hstep : 2 * v + 3 ≤ fuel a input := by
    dsimp [fuel, input]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hrun := run_valid a v hv rest
  rw [show fuel a input = (2 * v + 3) + (fuel a input - (2 * v + 3)) by omega,
    run_add hrun]
  exact run_halted _ _ _ _ _ _

theorem run_truncated_fuel (a v : ℕ) (hv : v ≤ a) :
    run (fuel a (List.replicate v true))
      (initial a (List.replicate v true)) =
      cfg none none [] (List.replicate (a - v) true)
        (List.replicate v true) [false] := by
  have hstep : 2 * v + 2 ≤ fuel a (List.replicate v true) := by
    simp [fuel]
    omega
  have hrun := run_truncated a v hv
  rw [show fuel a (List.replicate v true) =
      (2 * v + 2) + (fuel a (List.replicate v true) - (2 * v + 2)) by omega,
    run_add hrun]
  exact run_halted _ _ _ _ _ _

theorem run_exhausted_cons_fuel (a : ℕ) (bit : Bool)
    (rest : List Bool) :
    run (fuel a (List.replicate a true ++ bit :: rest))
      (initial a (List.replicate a true ++ bit :: rest)) =
      cfg none none rest [] (List.replicate a true) [false] := by
  have hstep : 2 * a + 3 ≤
      fuel a (List.replicate a true ++ bit :: rest) := by
    simp [fuel]
  have hrun := run_exhausted_cons a bit rest
  rw [show fuel a (List.replicate a true ++ bit :: rest) =
      (2 * a + 3) +
        (fuel a (List.replicate a true ++ bit :: rest) - (2 * a + 3)) by omega,
    run_add hrun]
  exact run_halted _ _ _ _ _ _

theorem run_exhausted_nil_fuel (a : ℕ) :
    run (fuel a (List.replicate a true))
      (initial a (List.replicate a true)) =
      cfg none none [] [] (List.replicate a true) [false] := by
  simpa using run_truncated_fuel a a (le_refl a)

theorem run_exhausted_fuel (a : ℕ) (suffix : List Bool) :
    run (fuel a (List.replicate a true ++ suffix))
      (initial a (List.replicate a true ++ suffix)) =
      cfg none none (suffix.drop 1) [] (List.replicate a true) [false] := by
  cases suffix with
  | nil => simpa using run_exhausted_nil_fuel a
  | cons bit rest => simpa using run_exhausted_cons_fuel a bit rest

private theorem decodeUnary_prefix_ge (a : ℕ) (bits : List Bool)
    (v : ℕ) (rest : List Bool)
    (h : decodeUnary (List.replicate a true ++ bits) = some (v, rest)) :
    a ≤ v := by
  induction a generalizing v rest with
  | zero => omega
  | succ a ih =>
      simp only [List.replicate_succ, List.cons_append, decodeUnary] at h
      cases hd : decodeUnary (List.replicate a true ++ bits) with
      | none => simp [hd] at h
      | some z =>
          obtain ⟨v', rest'⟩ := z
          simp [hd] at h
          have ha := ih v' rest' hd
          cases h
          omega

theorem finCodec_reject_exhausted (a : ℕ) (suffix : List Bool) :
    (finCodec a).decode (List.replicate a true ++ suffix) = none := by
  cases hd : decodeUnary (List.replicate a true ++ suffix) with
  | none => simp [finCodec, hd]
  | some z =>
      obtain ⟨v, rest⟩ := z
      have hv := decodeUnary_prefix_ge a suffix v rest hd
      simp [finCodec, hd, Nat.not_lt.mpr hv]

private theorem classifyInput (a : ℕ) (bits : List Bool) :
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

/-- Physical observation: successful status means the output unary stack
holds the parsed numeral and stack zero is the unconsumed suffix. -/
def observed (c : TM2.Cfg (fun _ : Fin 4 => Bool) Label Control) :
    Option (ℕ × List Bool) :=
  if c.stk 3 = [true] then some ((c.stk 2).length, c.stk 0) else none

/-- Complete all-input correspondence at a literal transition allocation.
No valid value or suffix is extracted from an unverified abstract parser. -/
theorem observed_run_eq_codec (a : ℕ) (bits : List Bool) :
    observed (run (fuel a bits) (initial a bits)) =
      ((finCodec a).decode bits).map (fun z => (z.1.val, z.2)) := by
  rcases classifyInput a bits with ⟨v, rest, hv, rfl⟩ |
    ⟨v, hv, rfl⟩ | ⟨suffix, rfl⟩
  · rw [run_valid_fuel a v hv rest, finCodec_decode_valid a v hv rest]
    simp [observed, cfg, stackContents]
  · rw [run_truncated_fuel a v hv, finCodec_reject_truncated]
    simp [observed, cfg, stackContents]
  · rw [run_exhausted_fuel, finCodec_reject_exhausted]
    simp [observed, cfg, stackContents]

theorem run_fuel_halts (a : ℕ) (bits : List Bool) :
    (run (fuel a bits) (initial a bits)).l = none := by
  rcases classifyInput a bits with ⟨v, rest, hv, rfl⟩ |
    ⟨v, hv, rfl⟩ | ⟨suffix, rfl⟩
  · rw [run_valid_fuel a v hv rest]
    rfl
  · rw [run_truncated_fuel a v hv]
    rfl
  · rw [run_exhausted_fuel]
    rfl

end Paper2.UnaryLabelParserScratch
