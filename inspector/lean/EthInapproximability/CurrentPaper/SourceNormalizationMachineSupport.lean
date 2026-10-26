import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Physical support bits and endpoint ranks

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, deletion of
isolated vertices in their inherited order. A support vector has one bit per
old vertex. Marking an endpoint and counting the marked vertices preceding
it are implemented by scanning and restoring actual Boolean stacks.
This is a raw finite-stack subroutine, not a completed graph normalizer.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineSupport

open Turing TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label Control

def program (mark : Bool) : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .scan => pop 1 (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (pop 0 (fun v b => (b, v.2))
          (branch (fun v => v.1.isSome)
            (push 2 (fun v => v.1.getD false)
              (branch (fun v => v.1.getD false)
                (push 3 (fun _ => true) (goto (fun _ => .scan)))
                (goto (fun _ => .scan)))) halt))
        (pop 0 (fun _ b => (b, b.getD false))
          (branch (fun v => v.1.isSome)
            (push 0 (fun v => mark || v.2) (goto (fun _ => .restore))) halt)))
  | .restore => pop 2 (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome)
        (push 0 (fun v => v.1.getD false) (push 1 (fun _ => true)
          (goto (fun _ => .restore)))) halt)

def cfg (l : Option Label) (s : Control)
    (vector index saved rank payload : List Bool) : Config :=
  ⟨l, s, ![vector, index, saved, rank, payload]⟩

def run (mark : Bool) (t : ℕ) (c : Config) := ((advance (program mark))^[t]) c

private theorem run_succ (mark : Bool) {c d : Config}
    (h : TM2.step (program mark) c = some d) (t : ℕ) :
    run mark (t + 1) c = run mark t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (mark : Bool) {c d : Config} {t : ℕ}
    (h : run mark t c = d) (u : ℕ) : run mark (t + u) c = run mark u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_prefix (mark : Bool) (xs : List Bool) (b : Bool)
    (suffix saved payload : List Bool) (r : ℕ) (s : Control) :
    run mark (xs.length + 1)
      (cfg (some .scan) s (xs ++ b :: suffix) (List.replicate xs.length true)
        saved (List.replicate r true) payload) =
    cfg (some .restore) (some b, b) ((mark || b) :: suffix) []
      (xs.reverse ++ saved) (List.replicate (r + xs.count true) true) payload := by
  induction xs generalizing saved r s with
  | nil =>
      apply congrArg (fun S => (⟨some .restore, (some b, b), S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons x xs ih =>
      have hs : TM2.step (program mark)
          (cfg (some .scan) s ((x :: xs) ++ b :: suffix)
            (List.replicate (x :: xs).length true) saved (List.replicate r true) payload) =
          some (cfg (some .scan) (some x, s.2) (xs ++ b :: suffix)
            (List.replicate xs.length true) (x :: saved)
            (List.replicate (r + if x then 1 else 0) true) payload) := by
        cases x <;>
          apply congrArg (fun S => some (⟨some .scan, (some _, s.2), S⟩ : Config)) <;>
          funext k <;> fin_cases k <;> rfl
      simp only [List.length_cons] at hs ⊢
      rw [run_succ mark hs, ih]
      congr 1
      · simp [List.reverse_cons, List.append_assoc]
      · cases x <;> simp [List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem restore_list (mark : Bool) (xs : List Bool)
    (vector payload : List Bool) (i r : ℕ) (s : Control) :
    run mark (xs.length + 1)
      (cfg (some .restore) s vector (List.replicate i true) xs
        (List.replicate r true) payload) =
    cfg none (none, s.2) (xs.reverse ++ vector)
      (List.replicate (i + xs.length) true) [] (List.replicate r true) payload := by
  induction xs generalizing vector i s with
  | nil =>
      apply congrArg (fun S => (⟨none, (none, s.2), S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons x xs ih =>
      have hs : TM2.step (program mark)
          (cfg (some .restore) s vector (List.replicate i true) (x :: xs)
            (List.replicate r true) payload) =
          some (cfg (some .restore) (some x, s.2) (x :: vector)
            (List.replicate (i + 1) true) xs (List.replicate r true) payload) := by
        apply congrArg (fun S => some (⟨some .restore, (some x, s.2), S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      rw [List.length_cons, run_succ mark hs, ih]
      congr 1
      · simp [List.reverse_cons, List.append_assoc]
      · simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The original support vector is restored except for the selected mark;
the original endpoint index and arbitrary graph payload are retained. The
rank is the number of old support bits strictly preceding the endpoint. -/
theorem support_run (mark : Bool) (before : List Bool) (b : Bool)
    (suffix payload : List Bool) :
    run mark (2 * before.length + 2)
      (cfg (some .scan) (none, false) (before ++ b :: suffix)
        (List.replicate before.length true) [] [] payload) =
    cfg none (none, b) (before ++ (mark || b) :: suffix)
      (List.replicate before.length true) []
      (List.replicate (before.count true) true) payload := by
  have hs := scan_prefix mark before b suffix [] payload 0 (none, false)
  simp only [List.append_nil, Nat.zero_add, List.replicate_zero] at hs
  have hr := restore_list mark before.reverse ((mark || b) :: suffix) payload
    0 (before.count true) (some b, b)
  simp only [List.length_reverse, List.reverse_reverse, Nat.zero_add,
    List.replicate_zero] at hr
  have h := (run_add mark hs (before.length + 1)).trans hr
  have ht : before.length + 1 + (before.length + 1) = 2 * before.length + 2 := by omega
  rw [ht] at h
  exact h

theorem mark_run (before : List Bool) (b : Bool) (suffix payload : List Bool) :
    run true (2 * before.length + 2)
      (cfg (some .scan) (none, false) (before ++ b :: suffix)
        (List.replicate before.length true) [] [] payload) =
    cfg none (none, b) (before ++ true :: suffix)
      (List.replicate before.length true) []
      (List.replicate (before.count true) true) payload := by
  simpa only [Bool.true_or] using support_run true before b suffix payload

theorem rank_run (before : List Bool) (b : Bool) (suffix payload : List Bool) :
    run false (2 * before.length + 2)
      (cfg (some .scan) (none, false) (before ++ b :: suffix)
        (List.replicate before.length true) [] [] payload) =
    cfg none (none, b) (before ++ b :: suffix)
      (List.replicate before.length true) []
      (List.replicate (before.count true) true) payload := by
  simpa only [Bool.false_or] using support_run false before b suffix payload

end EthInapproximability.CurrentPaper.SourceNormalizationMachineSupport
