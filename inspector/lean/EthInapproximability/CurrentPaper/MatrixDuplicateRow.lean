import EthInapproximability.CurrentPaper.MatrixTemplateMachine

/-!
# The two extra row labels as literal Boolean-stack operations

Source: locked v8 `eq:exact-duplicate-labels`. The input is a first-family
prefix word, without its three tail coordinates. This fixed machine appends
its first two bits, so the two extra labels name exactly the first and second
original coordinates. Gathering the prefix from the flat payload is separate.
-/

namespace EthInapproximability.CurrentPaper.MatrixDuplicateRow

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | first | second | scan | reverse
  deriving DecidableEq, Fintype

abbrev Control := Bool × Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .first => pop 0 (fun _ b => (b.getD false, false, b))
      (branch (fun s => s.2.2.isSome)
        (push 1 Prod.fst (goto (fun _ => .second))) (goto (fun _ => .second)))
  | .second => pop 0 (fun s b => (s.1, b.getD false, b))
      (branch (fun s => s.2.2.isSome)
        (push 1 (fun s => s.2.1) (goto (fun _ => .scan))) (goto (fun _ => .scan)))
  | .scan => pop 0 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 1 (fun s => s.2.2.getD false) (goto (fun _ => .scan)))
        (push 1 Prod.fst (push 1 (fun s => s.2.1) (goto (fun _ => .reverse)))))
  | .reverse => pop 1 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 0 (fun s => s.2.2.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => (false, false, none)) halt))

def cfg (l : Option Label) (s : Control) (input buffer : List Bool) : Config :=
  ⟨l, s, ![input, buffer]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_cons (s : Control) (b : Bool) (q buffer : List Bool) :
    TM2.step program (cfg (some .scan) s (b :: q) buffer) =
      some (cfg (some .scan) (s.1, s.2.1, some b) q (b :: buffer)) := by
  apply congrArg (fun S => some (⟨some .scan, (s.1, s.2.1, some b), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem scan_nil (s : Control) (buffer : List Bool) :
    TM2.step program (cfg (some .scan) s [] buffer) =
      some (cfg (some .reverse) (s.1, s.2.1, none) [] (s.2.1 :: s.1 :: buffer)) := by
  apply congrArg (fun S => some (⟨some .reverse, (s.1, s.2.1, none), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem reverse_cons (s : Control) (b : Bool) (q buffer : List Bool) :
    TM2.step program (cfg (some .reverse) s q (b :: buffer)) =
      some (cfg (some .reverse) (s.1, s.2.1, some b) (b :: q) buffer) := by
  apply congrArg (fun S => some (⟨some .reverse, (s.1, s.2.1, some b), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem reverse_nil (s : Control) (q : List Bool) :
    TM2.step program (cfg (some .reverse) s q []) =
      some (cfg none (false, false, none) q []) := by
  apply congrArg (fun S => some (⟨none, (false, false, none), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem scan_run (s : Control) (q buffer : List Bool) :
    run (q.length + 1) (cfg (some .scan) s q buffer) =
      cfg (some .reverse) (s.1, s.2.1, none) []
        (s.2.1 :: s.1 :: (q.reverse ++ buffer)) := by
  induction q generalizing s buffer with
  | nil => simpa using run_succ (scan_nil s buffer) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (scan_cons _ _ _ _) _]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, s.2.1, some b) (b :: buffer)

theorem reverse_run (s : Control) (q buffer : List Bool) :
    run (buffer.length + 1) (cfg (some .reverse) s q buffer) =
      cfg none (false, false, none) (buffer.reverse ++ q) [] := by
  induction buffer generalizing s q with
  | nil => simpa using run_succ (reverse_nil s q) 0
  | cons b buffer ih =>
      rw [List.length_cons, run_succ (reverse_cons _ _ _ _) _]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, s.2.1, some b) (b :: q)

theorem duplicate_run (b₀ b₁ : Bool) (q : List Bool) :
    run (2 * q.length + 8) (cfg (some .first) (false, false, none) (b₀ :: b₁ :: q) []) =
      cfg none (false, false, none) ((b₀ :: b₁ :: q) ++ [b₀, b₁]) [] := by
  have h₁ : TM2.step program (cfg (some .first) (false, false, none) (b₀ :: b₁ :: q) []) =
      some (cfg (some .second) (b₀, false, some b₀) (b₁ :: q) [b₀]) := by
    apply congrArg (fun S => some (⟨some .second, (b₀, false, some b₀), S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have h₂ : TM2.step program (cfg (some .second) (b₀, false, some b₀) (b₁ :: q) [b₀]) =
      some (cfg (some .scan) (b₀, b₁, some b₁) q [b₁, b₀]) := by
    apply congrArg (fun S => some (⟨some .scan, (b₀, b₁, some b₁), S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have h₃ := scan_run (b₀, b₁, some b₁) q [b₁, b₀]
  have h₄ := reverse_run (b₀, b₁, none) [] (b₁ :: b₀ :: (q.reverse ++ [b₁, b₀]))
  have h := (run_add ((run_add ((run_add (run_succ h₁ 0) 1).trans (run_succ h₂ 0))
      (q.length + 1)).trans h₃) _).trans h₄
  have ht : 1 + 1 + (q.length + 1) +
      ((b₁ :: b₀ :: (q.reverse ++ [b₁, b₀])).length + 1) = 2 * q.length + 8 := by
    simp only [List.length_cons, List.length_append, List.length_reverse, List.length_nil]
    omega
  simp only [Nat.zero_add] at h
  rw [ht] at h
  simpa only [List.length_cons, List.length_append, List.length_reverse, List.length_nil,
    List.reverse_cons, List.reverse_append, List.reverse_reverse, List.reverse_nil,
    List.nil_append, List.append_nil, List.append_assoc, List.singleton_append,
    List.cons_append, Nat.zero_add, Nat.add_zero, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc, Nat.two_mul] using h

theorem word_run (q : List Bool) (hq : 2 ≤ q.length) :
    run (2 * q.length + 4) (cfg (some .first) (false, false, none) q []) =
      cfg none (false, false, none)
        (q ++ [q[0]?.getD false, q[1]?.getD false]) [] := by
  cases q with
  | nil => simp at hq
  | cons b₀ q =>
      cases q with
      | nil => simp at hq
      | cons b₁ q =>
          simpa only [List.length_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
            Option.getD_some, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using duplicate_run b₀ b₁ q

def prefixWord {a N₁ : ℕ} (C₁ : ExactConstruction.FirstFamily a N₁) (ℓ : Fin N₁) : List Bool :=
  List.ofFn (fun j : Fin (ExactConstruction.prefixLength a) =>
    C₁ ℓ (ExactConstruction.prefixCoordinate a j))

theorem prefixWord_duplication {a N₁ : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (ℓ : Fin N₁) :
    prefixWord C₁ ℓ ++ [(prefixWord C₁ ℓ)[0]?.getD false, (prefixWord C₁ ℓ)[1]?.getD false] =
      MatrixTemplateMachine.duplicatedRow ha C₁ ℓ := by
  have hp := ExactConstruction.two_le_prefix a ha
  have hp₀ : 0 < ExactConstruction.prefixLength a := by omega
  have hp₁ : 1 < ExactConstruction.prefixLength a := by omega
  have hw := Construction.qOne_add_two a (by omega : 1 ≤ a)
  apply List.ext_getElem
  · simp only [prefixWord, MatrixTemplateMachine.duplicatedRow, List.length_append,
      List.length_ofFn, List.length_cons, List.length_nil]
    exact hw
  · intro i hi hj
    have hwi : i < ExactConstruction.width a := by
      simpa only [MatrixTemplateMachine.duplicatedRow, List.length_ofFn] using hj
    simp only [MatrixTemplateMachine.duplicatedRow, List.getElem_ofFn]
    by_cases h : i < ExactConstruction.prefixLength a
    · rw [List.getElem_append_left (by simpa [prefixWord] using h)]
      simp only [prefixWord, List.getElem_ofFn, ExactConstruction.duplicateLabel, h, ↓reduceDIte]
    · by_cases he : i = ExactConstruction.prefixLength a
      · subst i
        simp [prefixWord, List.getElem_append_right, ExactConstruction.duplicateLabel, hp₀]
      · have he' : i = ExactConstruction.prefixLength a + 1 := by
          change ExactConstruction.prefixLength a + 2 = ExactConstruction.width a at hw
          omega
        subst i
        simp [prefixWord, List.getElem_append_right, ExactConstruction.duplicateLabel, hp₁]

/-- The executable two-extra-label operation produces the literal first-family
row used by the exact template query, not a supplied answer to that query. -/
theorem sampled_prefix_run {a N₁ : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (ℓ : Fin N₁) :
    run (2 * ExactConstruction.prefixLength a + 4)
      (cfg (some .first) (false, false, none) (prefixWord C₁ ℓ) []) =
        cfg none (false, false, none) (MatrixTemplateMachine.duplicatedRow ha C₁ ℓ) [] := by
  have h := word_run (prefixWord C₁ ℓ) (by
    simpa only [prefixWord, List.length_ofFn] using ExactConstruction.two_le_prefix a ha)
  rw [prefixWord_duplication ha] at h
  simpa only [prefixWord, List.length_ofFn] using h

end EthInapproximability.CurrentPaper.MatrixDuplicateRow
