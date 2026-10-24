import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# A literal fixed-word comparator for the source alphabet and arity headers

The expected canonical binary word is part of finite program syntax. Each
input bit is popped and compared with that fixed word; a missing, incorrect,
or extra bit produces `false`. The comparison consumes no unbounded control
register and takes at most one transition per expected bit plus one.
-/

namespace EthInapproximability.CurrentPaper.SourceFixedBinaryCheck

open Turing BitMachineEncoding

inductive Label (expected : List Bool) where
  | compare (i : Fin (expected.length + 1))
  deriving DecidableEq, Fintype

abbrev Config (expected : List Bool) :=
  TM2.Cfg (fun _ : Fin 2 => Bool) (Label expected) (Option Bool)

def contents (word status : List Bool) : Fin 2 → List Bool := ![word, status]

def program (expected : List Bool) : Label expected →
    TM2.Stmt (fun _ : Fin 2 => Bool) (Label expected) (Option Bool)
  | .compare i =>
      if h : i.val < expected.length then
        .pop 0 (fun _ b => b)
          (.branch (fun b => decide (b = some expected[i.val]))
            (.goto (fun _ => .compare ⟨i.val + 1, by omega⟩))
            (.push 1 (fun _ => false) .halt))
      else
        .pop 0 (fun _ b => b)
          (.branch Option.isSome
            (.push 1 (fun _ => false) .halt)
            (.push 1 (fun _ => true) .halt))

def run (expected : List Bool) (t : Nat) (c : Config expected) :=
  ((advance (program expected))^[t]) c

theorem run_one (expected : List Bool) (c : Config expected) :
    run expected 1 c = advance (program expected) c := rfl

theorem run_add (expected : List Bool) (t u : Nat) (c : Config expected) :
    run expected (t + u) c = run expected u (run expected t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program expected)) u t c

theorem step_good (expected : List Bool) (i : Fin (expected.length + 1))
    (hi : i.val < expected.length) (v : Option Bool)
    (tail status : List Bool) :
    advance (program expected)
      (⟨some (.compare i), v,
        contents (expected[i.val] :: tail) status⟩ : Config expected) =
      ⟨some (.compare ⟨i.val + 1, by omega⟩), some expected[i.val],
        contents tail status⟩ := by
  simp [advance, TM2.step, program, hi, TM2.stepAux, contents]
  funext k
  fin_cases k <;> simp

theorem step_bad (expected : List Bool) (i : Fin (expected.length + 1))
    (hi : i.val < expected.length) (v : Option Bool)
    (b : Bool) (tail status : List Bool) (hb : b ≠ expected[i.val]) :
    advance (program expected)
      (⟨some (.compare i), v, contents (b :: tail) status⟩ : Config expected) =
      ⟨none, some b, contents tail (false :: status)⟩ := by
  simp [advance, TM2.step, program, hi, TM2.stepAux, contents, hb]
  funext k
  fin_cases k <;> simp

theorem step_missing (expected : List Bool) (i : Fin (expected.length + 1))
    (hi : i.val < expected.length) (v : Option Bool) (status : List Bool) :
    advance (program expected)
      (⟨some (.compare i), v, contents [] status⟩ : Config expected) =
      ⟨none, none, contents [] (false :: status)⟩ := by
  simp [advance, TM2.step, program, hi, TM2.stepAux, contents]
  funext k
  fin_cases k <;> simp

theorem step_end_empty (expected : List Bool) (i : Fin (expected.length + 1))
    (hi : i.val = expected.length) (v : Option Bool) (status : List Bool) :
    advance (program expected)
      (⟨some (.compare i), v, contents [] status⟩ : Config expected) =
      ⟨none, none, contents [] (true :: status)⟩ := by
  have hnot : ¬ i.val < expected.length := by omega
  simp [advance, TM2.step, program, hnot, TM2.stepAux, contents]
  funext k
  fin_cases k <;> simp

theorem step_end_extra (expected : List Bool) (i : Fin (expected.length + 1))
    (hi : i.val = expected.length) (v : Option Bool)
    (b : Bool) (tail status : List Bool) :
    advance (program expected)
      (⟨some (.compare i), v, contents (b :: tail) status⟩ : Config expected) =
      ⟨none, some b, contents tail (false :: status)⟩ := by
  have hnot : ¬ i.val < expected.length := by omega
  simp [advance, TM2.step, program, hnot, TM2.stepAux, contents]
  funext k
  fin_cases k <;> simp

/-- Total comparison on arbitrary bit strings. The status bit is true
exactly when the complete supplied word equals the fixed program word. -/
theorem run_from (expected : List Bool) (i : Fin (expected.length + 1))
    (word status : List Bool) (v : Option Bool) :
    ∃ t c, t ≤ expected.length - i.val + 1 ∧
      run expected t (⟨some (.compare i), v, contents word status⟩ : Config expected) = c ∧
      c.l = none ∧
      c.stk 1 = decide (word = expected.drop i.val) :: status := by
  by_cases hi : i.val < expected.length
  · have hdrop : expected.drop i.val =
        expected[i.val] :: expected.drop (i.val + 1) := by
      exact List.drop_eq_getElem_cons hi
    cases word with
    | nil =>
        refine ⟨1, ⟨none, none, contents [] (false :: status)⟩,
          by omega, ?_, rfl, ?_⟩
        · exact run_one expected _ |>.trans (step_missing expected i hi v status)
        · change false :: status = decide ([] = expected.drop i.val) :: status
          have hne : ([] : List Bool) ≠ expected.drop i.val := by
            intro he
            rw [← he] at hdrop
            cases hdrop
          simp [hne]
    | cons b tail =>
        by_cases hb : b = expected[i.val]
        · subst b
          obtain ⟨t, c, ht, hr, hh, hs⟩ :=
            run_from expected ⟨i.val + 1, by omega⟩ tail status
              (some expected[i.val])
          refine ⟨t + 1, c, ?_, ?_, hh, ?_⟩
          · have hrem : expected.length - i.val =
                (expected.length - (i.val + 1)) + 1 := by omega
            have ht' : t ≤ expected.length - (i.val + 1) + 1 := by
              simpa only [] using ht
            omega
          · rw [show t + 1 = 1 + t by omega,
              run_add, run_one, step_good expected i hi v tail status]
            exact hr
          · simpa only [hdrop, List.cons.injEq, true_and, decide_true] using hs
        · refine ⟨1, ⟨none, some b, contents tail (false :: status)⟩,
            by omega, ?_, rfl, ?_⟩
          · exact run_one expected _ |>.trans
              (step_bad expected i hi v b tail status hb)
          · change false :: status = decide (b :: tail = expected.drop i.val) :: status
            have hne : b :: tail ≠ expected.drop i.val := by
              rw [hdrop]
              intro he
              exact hb (List.cons.inj he).1
            simp [hne]
  · have he : i.val = expected.length := by omega
    have hdrop : expected.drop i.val = [] := by
      rw [he]
      exact List.drop_eq_nil_of_le le_rfl
    cases word with
    | nil =>
        refine ⟨1, ⟨none, none, contents [] (true :: status)⟩,
          by omega, ?_, rfl, ?_⟩
        · exact run_one expected _ |>.trans
            (step_end_empty expected i he v status)
        · simp [contents, hdrop]
    | cons b tail =>
        refine ⟨1, ⟨none, some b, contents tail (false :: status)⟩,
          by omega, ?_, rfl, ?_⟩
        · exact run_one expected _ |>.trans
            (step_end_extra expected i he v b tail status)
        · simp [contents, hdrop]
termination_by expected.length - i.val

theorem compare_total (expected word : List Bool) :
    ∃ t c, t ≤ expected.length + 1 ∧
      run expected t (⟨some (.compare 0), none, contents word []⟩ : Config expected) = c ∧
      c.l = none ∧ c.stk 1 = [decide (word = expected)] := by
  obtain ⟨t, c, ht, hr, hh, hs⟩ := run_from expected 0 word [] none
  refine ⟨t, c, by simpa only [Fin.val_zero, Nat.sub_zero] using ht,
    hr, hh, ?_⟩
  simpa only [List.drop_zero, List.cons_append, List.nil_append] using hs

end EthInapproximability.CurrentPaper.SourceFixedBinaryCheck
