import Paper2.CodeTableFallback
import Paper2.FiniteFallbackSearch
import Mathlib.Tactic

/-! U16 printing piece (private): a fixed physical entry machine for the
identity table of the finite-source fallback (v12 D:108-110, `k ≥ 2`), as an
actual `MatrixTableWriter.EntryRuns` instance with a charged per-entry clock,
and the resulting physical row-major print of `FiniteFallbackIdentity.identityMatrix`.
The machine compares the two unary index stacks by moving matched units to two
scratch stacks, then restores both indices; every step is counted. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.FallbackIdentityCell

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := MatrixTableWriter.CellStack 2

inductive Label where
  | move | restoreA | restoreB
  deriving DecidableEq

abbrev Control := Option Bool × Option Bool × Bool

def eqCell : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .move =>
      pop (.inr 0) (fun s a => (a, s.2.1, s.2.2))
        (pop (.inr 1) (fun s b => (s.1, b, s.2.2))
          (branch (fun s => s.1.isSome && s.2.1.isSome)
            (push (.inl 0) (fun _ => true)
              (push (.inl 1) (fun _ => true) (goto (fun _ => .move))))
            (branch (fun s => s.1.isSome)
              (push (.inr 0) (fun _ => true)
                (load (fun _ => (none, none, false)) (goto (fun _ => .restoreA))))
              (branch (fun s => s.2.1.isSome)
                (push (.inr 1) (fun _ => true)
                  (load (fun _ => (none, none, false)) (goto (fun _ => .restoreA))))
                (load (fun _ => (none, none, true)) (goto (fun _ => .restoreA)))))))
  | .restoreA =>
      pop (.inl 0) (fun s a => (a, s.2.1, s.2.2))
        (branch (fun s => s.1.isSome)
          (push (.inr 0) (fun _ => true) (goto (fun _ => .restoreA)))
          (goto (fun _ => .restoreB)))
  | .restoreB =>
      pop (.inl 1) (fun s b => (s.1, b, s.2.2))
        (branch (fun s => s.2.1.isSome)
          (push (.inr 1) (fun _ => true) (goto (fun _ => .restoreB)))
          (push (.inr 2) (fun s => s.2.2) halt))

def st (A B X Y ans : List Bool) : Stack → List Bool :=
  Sum.elim ![A, B] ![X, Y, ans]

def cfg (l : Option Label) (s : Control) (A B X Y ans : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨l, s, st A B X Y ans⟩

abbrev step := advance eqCell

theorem cfg_eq {c : TM2.Cfg (fun _ : Stack => Bool) Label Control}
    {l : Option Label} {s : Control} {A B X Y ans : List Bool}
    (hl : c.l = l) (hv : c.var = s) (hs : ∀ k, c.stk k = st A B X Y ans k) :
    c = cfg l s A B X Y ans := by
  cases c with
  | mk l' v' S =>
    simp only at hl hv
    subst hl hv
    have : S = st A B X Y ans := funext hs
    subst this
    rfl

theorem move_both (s : Control) (A B X Y ans : List Bool) :
    step (cfg (some .move) s A B (true :: X) (true :: Y) ans) =
      cfg (some .move) (some true, some true, s.2.2)
        (true :: A) (true :: B) X Y ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem move_equal (s : Control) (A B ans : List Bool) :
    step (cfg (some .move) s A B [] [] ans) =
      cfg (some .restoreA) (none, none, true) A B [] [] ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem move_left (s : Control) (A B X ans : List Bool) :
    step (cfg (some .move) s A B (true :: X) [] ans) =
      cfg (some .restoreA) (none, none, false) A B (true :: X) [] ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem move_right (s : Control) (A B Y ans : List Bool) :
    step (cfg (some .move) s A B [] (true :: Y) ans) =
      cfg (some .restoreA) (none, none, false) A B [] (true :: Y) ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem restoreA_some (p q : Option Bool) (f : Bool) (A B X Y ans : List Bool) :
    step (cfg (some .restoreA) (p, q, f) (true :: A) B X Y ans) =
      cfg (some .restoreA) (some true, q, f) A B (true :: X) Y ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem restoreA_none (p q : Option Bool) (f : Bool) (B X Y ans : List Bool) :
    step (cfg (some .restoreA) (p, q, f) [] B X Y ans) =
      cfg (some .restoreB) (none, q, f) [] B X Y ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem restoreB_some (p q : Option Bool) (f : Bool) (A B X Y ans : List Bool) :
    step (cfg (some .restoreB) (p, q, f) A (true :: B) X Y ans) =
      cfg (some .restoreB) (p, some true, f) A B X (true :: Y) ans := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem restoreB_none (p q : Option Bool) (f : Bool) (A X Y ans : List Bool) :
    step (cfg (some .restoreB) (p, q, f) A [] X Y ans) =
      cfg none (p, none, f) A [] X Y (f :: ans) := by
  apply cfg_eq
  · rfl
  · rfl
  · intro k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem rep_cons (i : Nat) (A : List Bool) :
    List.replicate i true ++ true :: A = List.replicate (i + 1) true ++ A := by
  rw [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem move_loop (i : Nat) : ∀ (s : Control) (A B X Y ans : List Bool),
    ∃ s', (step^[i]) (cfg (some .move) s A B (List.replicate i true ++ X)
        (List.replicate i true ++ Y) ans) =
      cfg (some .move) s' (List.replicate i true ++ A)
        (List.replicate i true ++ B) X Y ans := by
  induction i with
  | zero => intro s A B X Y ans; exact ⟨s, rfl⟩
  | succ i ih =>
    intro s A B X Y ans
    obtain ⟨s', hs'⟩ := ih (some true, some true, s.2.2) (true :: A) (true :: B) X Y ans
    refine ⟨s', ?_⟩
    rw [Function.iterate_succ_apply]
    have h1 : step (cfg (some .move) s A B (List.replicate (i + 1) true ++ X)
        (List.replicate (i + 1) true ++ Y) ans) =
        cfg (some .move) (some true, some true, s.2.2) (true :: A) (true :: B)
          (List.replicate i true ++ X) (List.replicate i true ++ Y) ans :=
      move_both s A B _ _ ans
    rw [h1, hs', rep_cons, rep_cons]

theorem restoreA_loop (i : Nat) : ∀ (p q : Option Bool) (f : Bool) (B X Y ans : List Bool),
    ∃ p', (step^[i]) (cfg (some .restoreA) (p, q, f) (List.replicate i true) B X Y ans) =
      cfg (some .restoreA) (p', q, f) [] B (List.replicate i true ++ X) Y ans := by
  induction i with
  | zero => intro p q f B X Y ans; exact ⟨p, rfl⟩
  | succ i ih =>
    intro p q f B X Y ans
    obtain ⟨p', hp'⟩ := ih (some true) q f B (true :: X) Y ans
    refine ⟨p', ?_⟩
    rw [Function.iterate_succ_apply]
    have h1 : step (cfg (some .restoreA) (p, q, f) (List.replicate (i + 1) true) B X Y ans) =
        cfg (some .restoreA) (some true, q, f) (List.replicate i true) B (true :: X) Y ans :=
      restoreA_some p q f _ B X Y ans
    rw [h1, hp', rep_cons]

theorem restoreB_loop (i : Nat) : ∀ (p q : Option Bool) (f : Bool) (A X Y ans : List Bool),
    ∃ q', (step^[i]) (cfg (some .restoreB) (p, q, f) A (List.replicate i true) X Y ans) =
      cfg (some .restoreB) (p, q', f) A [] X (List.replicate i true ++ Y) ans := by
  induction i with
  | zero => intro p q f A X Y ans; exact ⟨q, rfl⟩
  | succ i ih =>
    intro p q f A X Y ans
    obtain ⟨q', hq'⟩ := ih p (some true) f A X (true :: Y) ans
    refine ⟨q', ?_⟩
    rw [Function.iterate_succ_apply]
    have h1 : step (cfg (some .restoreB) (p, q, f) A (List.replicate (i + 1) true) X Y ans) =
        cfg (some .restoreB) (p, some true, f) A (List.replicate i true) X (true :: Y) ans :=
      restoreB_some p q f A _ X Y ans
    rw [h1, hq', rep_cons]

/-- Common tail: from the restore phase with `m` matched units. -/
theorem restore_tail (m : Nat) (f : Bool) (X Y : List Bool) :
    ∃ v, (step^[m + 1 + (m + 1)]) (cfg (some .restoreA) (none, none, f)
        (List.replicate m true) (List.replicate m true) X Y []) =
      cfg none v [] [] (List.replicate m true ++ X) (List.replicate m true ++ Y) [f] := by
  obtain ⟨p', hA⟩ := restoreA_loop m none none f (List.replicate m true) X Y []
  obtain ⟨q', hB⟩ := restoreB_loop m none none f [] (List.replicate m true ++ X) Y []
  refine ⟨(none, none, f), ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_succ_apply',
    Function.iterate_succ_apply', hA, restoreA_none, hB, restoreB_none]

theorem cell_run (x y : Nat) :
    ∃ t ≤ 3 * x + 3, ∃ v,
      (step^[t]) (cfg (some .move) (none, none, false) [] []
        (List.replicate x true) (List.replicate y true) []) =
      cfg none v [] [] (List.replicate x true) (List.replicate y true) [decide (x = y)] := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, y = x + d + 1 := ⟨y - x - 1, by omega⟩
    obtain ⟨s', hm⟩ := move_loop x (none, none, false) [] [] []
      (true :: List.replicate d true) []
    obtain ⟨v, ht⟩ := restore_tail x false [] (true :: List.replicate d true)
    simp only [List.append_nil] at hm ht
    refine ⟨(x + 1 + (x + 1)) + (1 + x), by omega, v, ?_⟩
    have e2 : List.replicate (x + d + 1) true =
        List.replicate x true ++ true :: List.replicate d true := by
      rw [rep_cons, ← List.replicate_add]; congr 1; omega
    rw [e2, Function.iterate_add_apply, Function.iterate_add_apply step 1 x, hm,
      Function.iterate_one, move_right, ht,
      decide_eq_false (by omega : ¬ x = x + d + 1)]
  · subst h
    obtain ⟨s', hm⟩ := move_loop x (none, none, false) [] [] [] [] []
    obtain ⟨v, ht⟩ := restore_tail x true [] []
    simp only [List.append_nil] at hm ht
    refine ⟨(x + 1 + (x + 1)) + (1 + x), by omega, v, ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply step 1 x, hm,
      Function.iterate_one, move_equal, ht, decide_eq_true rfl]
  · obtain ⟨d, rfl⟩ : ∃ d, x = y + d + 1 := ⟨x - y - 1, by omega⟩
    obtain ⟨s', hm⟩ := move_loop y (none, none, false) [] []
      (true :: List.replicate d true) [] []
    obtain ⟨v, ht⟩ := restore_tail y false (true :: List.replicate d true) []
    simp only [List.append_nil] at hm ht
    refine ⟨(y + 1 + (y + 1)) + (1 + y), by omega, v, ?_⟩
    have e2 : List.replicate (y + d + 1) true =
        List.replicate y true ++ true :: List.replicate d true := by
      rw [rep_cons, ← List.replicate_add]; congr 1; omega
    rw [e2, Function.iterate_add_apply, Function.iterate_add_apply step 1 y, hm,
      Function.iterate_one, move_left, ht,
      decide_eq_false (by omega : ¬ y + d + 1 = y)]

def emptyBank : Fin 2 → List Bool := ![[], []]

theorem eqCell_entryRuns (r c : Nat) :
    MatrixTableWriter.EntryRuns eqCell Label.move ((none, none, false) : Control)
      emptyBank r c (3 * r + 3) (fun x y => decide (x = y)) := by
  intro x hx y hy
  obtain ⟨t, ht, v, h⟩ := cell_run x y
  exact ⟨t, by omega, v, h⟩

/-- Physical row-major print of the literal identity matrix. -/
theorem write_identity_table (N : Nat) :
    ∃ t ≤ MatrixTableWriter.writerBound N N (3 * N + 3), ∃ v,
      MatrixTableWriter.run eqCell Label.move ((none, none, false) : Control) t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (((none, none, false) : Control), none)
          (MatrixTableWriter.ready emptyBank N N 0 0 0 0 [] [])) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready emptyBank N N 0 0 0 0 []
          (MatrixMaterialization.rowMajor (FiniteFallbackIdentity.identityMatrix N))) := by
  simpa using MatrixTableWriter.write_rowMajor eqCell Label.move
    ((none, none, false) : Control) emptyBank N N (3 * N + 3)
    (fun x y => decide (x = y)) (FiniteFallbackIdentity.identityMatrix N)
    (by intro x y; simp [FiniteFallbackIdentity.identityMatrix, Fin.ext_iff])
    (eqCell_entryRuns N N) []

/-- Printing clock of the identity branch, polynomial in the side length
(`2^(k-1)` in v12 D:108-110). -/
theorem identity_print_clock_le (N : Nat) :
    MatrixTableWriter.writerBound N N (3 * N + 3) ≤ 20 * (5 * N + 4) ^ 3 := by
  have h := MatrixTableWriter.writerBound_polynomial N N (3 * N + 3)
  have e : N + N + (3 * N + 3) + 1 = 5 * N + 4 := by omega
  rwa [e] at h

#print axioms cell_run
#print axioms eqCell_entryRuns
#print axioms write_identity_table
#print axioms identity_print_clock_le

#print axioms move_both
#print axioms restoreB_none

end Paper2.FallbackIdentityCell
