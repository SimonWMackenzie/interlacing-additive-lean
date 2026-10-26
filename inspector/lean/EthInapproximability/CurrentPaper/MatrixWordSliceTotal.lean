import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Totality of the literal word-access machine

This module extends `MatrixMaterialization.WordSlice` to every Boolean input,
including missing header delimiters. A missing delimiter is read as zero;
the remainder of the payload is then empty. The fixed program is unchanged.

The proof normalizes only the specification: the actual machine receives
the original input. Literal executions become equal after the two header
loops and the first skip transition, so the existing word-access execution
proof applies. The resulting bound is `6 * (input.length + 1)` transitions.
-/

namespace EthInapproximability.CurrentPaper.MatrixWordSliceTotal

open Turing BitMachineEncoding
open MatrixMaterialization.WordSlice

/-- Parse a unary prefix. A missing zero terminator leaves an empty suffix. -/
def unary : List Bool → ℕ × List Bool
  | [] => (0, [])
  | false :: q => (0, q)
  | true :: q => let r := unary q; (r.1 + 1, r.2)

theorem unary_length (q : List Bool) : (unary q).1 + (unary q).2.length ≤ q.length := by
  induction q with
  | nil => simp [unary]
  | cons x q ih => cases x <;> simp only [unary, List.length_cons] <;> omega

@[simp] theorem unary_replicate (n : ℕ) (q : List Bool) :
    unary (List.replicate n true ++ false :: q) = (n, q) := by
  induction n with
  | zero => simp [unary]
  | succ n ih => simp [List.replicate_succ, unary, ih]

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label (Option Bool)}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label (Option Bool)}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_offset_true (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countOffset) s (true :: q) o w b) =
      some (cfg (some .countOffset) (some true) q (true :: o) w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem step_offset_false (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countOffset) s (false :: q) o w b) =
      some (cfg (some .countWidth) (some false) q o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem step_offset_nil (s : Option Bool) (o w b : List Bool) :
    TM2.step program (cfg (some .countOffset) s [] o w b) =
      some (cfg (some .countWidth) none [] o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

private theorem step_width_true (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countWidth) s (true :: q) o w b) =
      some (cfg (some .countWidth) (some true) q o (true :: w) b) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem step_width_false (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countWidth) s (false :: q) o w b) =
      some (cfg (some .skip) (some false) q o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]
  funext k
  fin_cases k <;> rfl

private theorem step_width_nil (s : Option Bool) (o w b : List Bool) :
    TM2.step program (cfg (some .countWidth) s [] o w b) =
      some (cfg (some .skip) none [] o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg, stackContents]

private theorem offset_parse (q : List Bool) (m : ℕ) (s : Option Bool) (w b : List Bool) :
    ∃ t, run ((unary q).1 + 1)
      (cfg (some .countOffset) s q (List.replicate m true) w b) =
      cfg (some .countWidth) t (unary q).2
        (List.replicate ((unary q).1 + m) true) w b := by
  induction q generalizing m s with
  | nil =>
      refine ⟨none, ?_⟩
      simpa only [unary, Nat.zero_add] using
        run_succ (step_offset_nil s (List.replicate m true) w b) 0
  | cons x q ih =>
      cases x with
      | false =>
          refine ⟨some false, ?_⟩
          simpa only [unary, Nat.zero_add] using
            run_succ (step_offset_false s q (List.replicate m true) w b) 0
      | true =>
          obtain ⟨t, ht⟩ := ih (m + 1) (some true)
          refine ⟨t, ?_⟩
          simp only [unary]
          rw [run_succ (step_offset_true s _ _ _ _)]
          simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using ht

private theorem width_parse (q : List Bool) (m : ℕ) (s : Option Bool) (o b : List Bool) :
    ∃ t, run ((unary q).1 + 1)
      (cfg (some .countWidth) s q o (List.replicate m true) b) =
      cfg (some .skip) t (unary q).2 o
        (List.replicate ((unary q).1 + m) true) b := by
  induction q generalizing m s with
  | nil =>
      refine ⟨none, ?_⟩
      simpa only [unary, Nat.zero_add] using
        run_succ (step_width_nil s o (List.replicate m true) b) 0
  | cons x q ih =>
      cases x with
      | false =>
          refine ⟨some false, ?_⟩
          simpa only [unary, Nat.zero_add] using
            run_succ (step_width_false s q o (List.replicate m true) b) 0
      | true =>
          obtain ⟨t, ht⟩ := ih (m + 1) (some true)
          refine ⟨t, ?_⟩
          simp only [unary]
          rw [run_succ (step_width_true s _ _ _ _)]
          simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using ht

def offset (input : List Bool) : ℕ := (unary input).1
def width (input : List Bool) : ℕ := (unary (unary input).2).1
def payload (input : List Bool) : List Bool := (unary (unary input).2).2
def normalize (input : List Bool) : List Bool := encodeInput (offset input) (width input) (payload input)
def output (input : List Bool) : List Bool := padded (width input) ((payload input).drop (offset input))
def time (input : List Bool) : ℕ := exactTime (offset input) (width input) (payload input)
def prefixTime (input : List Bool) : ℕ := (offset input + 1) + (width input + 1)

private theorem parser_correct (input : List Bool) :
    ∃ s, run (prefixTime input) (cfg (some .countOffset) none input [] [] []) =
      cfg (some .skip) s (payload input)
        (List.replicate (offset input) true) (List.replicate (width input) true) [] := by
  obtain ⟨s, hs⟩ := offset_parse input 0 none [] []
  obtain ⟨t, ht⟩ := width_parse (unary input).2 0 s (List.replicate (offset input) true) []
  simp only [List.replicate_zero, Nat.add_zero] at hs ht
  refine ⟨t, ?_⟩
  exact (run_add hs (width input + 1)).trans ht

theorem normalize_fields (input : List Bool) :
    offset (normalize input) = offset input ∧ width (normalize input) = width input ∧
      payload (normalize input) = payload input := by
  simp [offset, width, payload, normalize, encodeInput]

private theorem prefix_run_eq (input : List Bool) :
    run (prefixTime input + 1) (cfg (some .countOffset) none input [] [] []) =
      run (prefixTime input + 1) (cfg (some .countOffset) none (normalize input) [] [] []) := by
  obtain ⟨s, hs⟩ := parser_correct input
  obtain ⟨t, ht⟩ := parser_correct (normalize input)
  obtain ⟨ho, hw, hq⟩ := normalize_fields input
  simp only [prefixTime, ho, hw, hq] at ht
  rw [show run (prefixTime input + 1) (cfg (some .countOffset) none input [] [] []) =
    advance program (run (prefixTime input) (cfg (some .countOffset) none input [] [] [])) from
      Function.iterate_succ_apply' _ _ _]
  rw [show run (prefixTime input + 1) (cfg (some .countOffset) none (normalize input) [] [] []) =
    advance program (run (prefixTime input)
      (cfg (some .countOffset) none (normalize input) [] [] [])) from
        Function.iterate_succ_apply' _ _ _]
  rw [hs]
  change advance program _ = advance program (run (offset input + 1 + (width input + 1)) _)
  rw [ht]
  rfl

theorem run_correct_total (input : List Bool) :
    run (time input) (cfg (some .countOffset) none input [] [] []) =
      cfg none none (output input) [] [] [] := by
  have hp : prefixTime input + 1 ≤ time input := by
    unfold prefixTime time exactTime
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hp
  have he := congrArg (run r) (prefix_run_eq input)
  have hcomp (x : List Bool) :
      run r (run (prefixTime input + 1) (cfg (some .countOffset) none x [] [] [])) =
        run (time input) (cfg (some .countOffset) none x [] [] []) := by
    rw [hr, Nat.add_comm (prefixTime input + 1) r]
    simp only [run, Function.iterate_add_apply]
  rw [hcomp, hcomp] at he
  exact he.trans (MatrixMaterialization.WordSlice.run_correct _ _ _)

theorem time_le (input : List Bool) : time input ≤ 6 * (input.length + 1) := by
  have h₁ := unary_length input
  have h₂ := unary_length (unary input).2
  have h₃ : (((payload input).drop (offset input)).drop (width input)).length ≤
      (payload input).length := by simp only [List.length_drop]; omega
  change offset input + (unary input).2.length ≤ input.length at h₁
  change width input + (payload input).length ≤ (unary input).2.length at h₂
  unfold time exactTime
  omega

theorem bitMachine_computes : bitMachine.ComputesWithin output (fun n => 6 * (n + 1)) := by
  intro input
  have hi : rawInit (0 : Fin 4) .countOffset (none : Option Bool) input =
      cfg (some .countOffset) none input [] [] [] := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 4) 0 .countOffset (none : Option Bool) program
    input (output input) (time input) _ (time_le input)
  · change (run (time input) _).l = none
    rw [hi, run_correct_total]
    rfl
  · change (run (time input) _).stk 0 = _
    rw [hi, run_correct_total]
    rfl

theorem polytime_output : BitMachine.Polytime output := by
  refine ⟨bitMachine, 6, 1, ?_⟩
  simpa only [pow_one] using bitMachine_computes

theorem output_encodeInput (o w : ℕ) (q : List Bool) :
    output (encodeInput o w q) = padded w (q.drop o) := by
  simp [output, offset, width, payload, encodeInput]

end EthInapproximability.CurrentPaper.MatrixWordSliceTotal
