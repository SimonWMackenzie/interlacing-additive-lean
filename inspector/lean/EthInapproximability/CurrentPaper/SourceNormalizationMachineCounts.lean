import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.ParameterizedNP.GuardedSourceGraph

/-!
# Physical repetition count for source-graph normalization

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
The number of graph copies is `max 1 ((n + m) / (m + 1))`.
This file executes that arithmetic on unary stacks. In particular, the
original variable count `n` is retained as actual data, not a program parameter.
The original edge count and the graph payload are retained as well.
Parsing, isolated-vertex deletion, relabelling, and graph writing are separate
obligations; this is only the literal counting subroutine.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineCounts

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ParameterizedNP.GuardedSourceGraph

inductive Phase where
  | copyN | restoreN | copyM | restoreM | divide | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin 6 ⊕ Fin 3
abbrev Label := MatrixUnaryDivision.Label ⊕ Phase
abbrev Control := Bool × Unit
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Phase.finish) (MatrixUnaryDivision.program l)
  | .inr .copyN => pop (.inr 0) (fun _ b => (b.isSome, ()))
      (branch Prod.fst
        (push (.inl 0) (fun _ => true) (push (.inl 2) (fun _ => true)
          (goto (fun _ => .inr .copyN))))
        (goto (fun _ => .inr .restoreN)))
  | .inr .restoreN => pop (.inl 2) (fun _ b => (b.isSome, ()))
      (branch Prod.fst (push (.inr 0) (fun _ => true)
        (goto (fun _ => .inr .restoreN))) (goto (fun _ => .inr .copyM)))
  | .inr .copyM => pop (.inr 1) (fun _ b => (b.isSome, ()))
      (branch Prod.fst
        (push (.inl 0) (fun _ => true) (push (.inl 1) (fun _ => true)
          (push (.inl 2) (fun _ => true) (goto (fun _ => .inr .copyM)))))
        (goto (fun _ => .inr .restoreM)))
  | .inr .restoreM => pop (.inl 2) (fun _ b => (b.isSome, ()))
      (branch Prod.fst (push (.inr 1) (fun _ => true)
        (goto (fun _ => .inr .restoreM))) (goto (fun _ => .inr .divide)))
  | .inr .divide => push (.inl 1) (fun _ => true)
      (load (fun _ => (false, ())) (goto (fun _ => .inl .start)))
  | .inr .finish => pop (.inl 4) (fun _ _ => (false, ()))
      (push (.inl 4) (fun _ => true) halt)

def cfg (l : Option Label) (s : Bool)
    (input divisor count remainder quotient saved originalN originalM payload : List Bool) :
    Config := ⟨l, (s, ()), Sum.elim ![input, divisor, count, remainder, quotient, saved]
      ![originalN, originalM, payload]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem copyN_run (n a b : ℕ) (s : Bool) (m payload : List Bool) :
    run (n + 1) (cfg (some (.inr .copyN)) s
      (List.replicate a true) [] (List.replicate b true) [] [] []
      (List.replicate n true) m payload) =
    cfg (some (.inr .restoreN)) false
      (List.replicate (a + n) true) [] (List.replicate (b + n) true) [] [] []
      [] m payload := by
  induction n generalizing a b s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .restoreN), (false, ()), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ n ih =>
      have hs : TM2.step program
          (cfg (some (.inr .copyN)) s (List.replicate a true) []
            (List.replicate b true) [] [] [] (List.replicate (n + 1) true) m payload) =
          some (cfg (some (.inr .copyN)) true (List.replicate (a + 1) true) []
            (List.replicate (b + 1) true) [] [] [] (List.replicate n true) m payload) := by
        apply congrArg (fun S => some (⟨some (.inr .copyN), (true, ()), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
        | inr k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (n + 1)).trans (ih (a + 1) (b + 1) true)

private theorem restoreN_run (n b : ℕ) (s : Bool) (input m payload : List Bool) :
    run (n + 1) (cfg (some (.inr .restoreN)) s input []
      (List.replicate n true) [] [] [] (List.replicate b true) m payload) =
    cfg (some (.inr .copyM)) false input [] [] [] [] []
      (List.replicate (b + n) true) m payload := by
  induction n generalizing b s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .copyM), (false, ()), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ n ih =>
      have hs : TM2.step program
          (cfg (some (.inr .restoreN)) s input [] (List.replicate (n + 1) true)
            [] [] [] (List.replicate b true) m payload) =
          some (cfg (some (.inr .restoreN)) true input [] (List.replicate n true)
            [] [] [] (List.replicate (b + 1) true) m payload) := by
        apply congrArg (fun S => some (⟨some (.inr .restoreN), (true, ()), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
        | inr k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (n + 1)).trans (ih (b + 1) true)

private theorem copyM_run (m a b c : ℕ) (s : Bool) (n payload : List Bool) :
    run (m + 1) (cfg (some (.inr .copyM)) s (List.replicate a true)
      (List.replicate b true) (List.replicate c true) [] [] [] n
      (List.replicate m true) payload) =
    cfg (some (.inr .restoreM)) false (List.replicate (a + m) true)
      (List.replicate (b + m) true) (List.replicate (c + m) true) [] [] [] n [] payload := by
  induction m generalizing a b c s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .restoreM), (false, ()), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ m ih =>
      have hs : TM2.step program
          (cfg (some (.inr .copyM)) s (List.replicate a true) (List.replicate b true)
            (List.replicate c true) [] [] [] n (List.replicate (m + 1) true) payload) =
          some (cfg (some (.inr .copyM)) true (List.replicate (a + 1) true)
            (List.replicate (b + 1) true) (List.replicate (c + 1) true)
            [] [] [] n (List.replicate m true) payload) := by
        apply congrArg (fun S => some (⟨some (.inr .copyM), (true, ()), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
        | inr k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (m + 1)).trans (ih (a + 1) (b + 1) (c + 1) true)

private theorem restoreM_run (m b : ℕ) (s : Bool) (input divisor n payload : List Bool) :
    run (m + 1) (cfg (some (.inr .restoreM)) s input divisor
      (List.replicate m true) [] [] [] n (List.replicate b true) payload) =
    cfg (some (.inr .divide)) false input divisor [] [] [] [] n
      (List.replicate (b + m) true) payload := by
  induction m generalizing b s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .divide), (false, ()), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ m ih =>
      have hs : TM2.step program
          (cfg (some (.inr .restoreM)) s input divisor (List.replicate (m + 1) true)
            [] [] [] n (List.replicate b true) payload) =
          some (cfg (some (.inr .restoreM)) true input divisor (List.replicate m true)
            [] [] [] n (List.replicate (b + 1) true) payload) := by
        apply congrArg (fun S => some (⟨some (.inr .restoreM), (true, ()), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
        | inr k => fin_cases k <;> simp only [List.replicate_succ] <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (m + 1)).trans (ih (b + 1) true)

/-- The physical prelude constructs the dividend and divisor and restores
both source counters. It does not inspect the graph payload. -/
theorem prepare_run (n m : ℕ) (payload : List Bool) :
    run (2 * n + 2 * m + 5)
      (cfg (some (.inr .copyN)) false [] [] [] [] [] []
        (List.replicate n true) (List.replicate m true) payload) =
      cfg (some (.inl .start)) false (List.replicate (n + m) true)
        (List.replicate (m + 1) true) [] [] [] []
        (List.replicate n true) (List.replicate m true) payload := by
  have h₁ := copyN_run n 0 0 false (List.replicate m true) payload
  have h₂ := restoreN_run n 0 false (List.replicate n true) (List.replicate m true) payload
  have h₃ := copyM_run m n 0 0 false (List.replicate n true) payload
  have h₄ := restoreM_run m 0 false (List.replicate (n + m) true)
    (List.replicate m true) (List.replicate n true) payload
  simp only [Nat.zero_add, List.replicate_zero] at h₁ h₂ h₃ h₄
  have h₅ : run 1
      (cfg (some (.inr .divide)) false (List.replicate (n + m) true)
        (List.replicate m true) [] [] [] [] (List.replicate n true)
        (List.replicate m true) payload) =
      cfg (some (.inl .start)) false (List.replicate (n + m) true)
        (List.replicate (m + 1) true) [] [] [] [] (List.replicate n true)
        (List.replicate m true) payload := by
    apply congrArg (fun S => (⟨some (.inl .start), (false, ()), S⟩ : Config))
    funext k
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  have h := (run_add h₁ (n + 1)).trans h₂
  have h := (run_add h (m + 1)).trans h₃
  have h := (run_add h (m + 1)).trans h₄
  have h := (run_add h 1).trans h₅
  have ht : n + 1 + (n + 1) + (m + 1) + (m + 1) + 1 =
      2 * n + 2 * m + 5 := by omega
  rw [ht] at h
  exact h

/-- A literal finite-stack computation of the normalization repetition count,
with the original variable count and graph bits physically unchanged. -/
theorem count_run (n m : ℕ) (payload : List Bool) :
    ∃ t ≤ 10 * n + 13 * m + 13,
      run t (cfg (some (.inr .copyN)) false [] [] [] [] [] []
        (List.replicate n true) (List.replicate m true) payload) =
      cfg none false [] (List.replicate (m + 1) true) []
        (List.replicate ((n + m) % (m + 1)) true)
        (List.replicate (copyCount n m) true) []
        (List.replicate n true) (List.replicate m true) payload := by
  let c := MatrixUnaryDivision.cfg (some .start) false
    (List.replicate (n + m) true) (List.replicate (m + 1) true) [] [] [] []
  let T : Fin 3 → List Bool := ![List.replicate n true, List.replicate m true, payload]
  have hd := MatrixUnaryDivision.division_run (n + m) (m + 1) (by omega)
  obtain ⟨u, hu, he⟩ := BitMachineSubroutine.lift_outputs
    MatrixUnaryDivision.program program (some Phase.finish) (fun _ => rfl)
    () T c (MatrixUnaryDivision.exactTime (n + m) (m + 1))
    (by simpa only [MatrixUnaryDivision.run, c] using congrArg TM2.Cfg.l hd)
  rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.exactTime
    (n + m) (m + 1)]) c = _ from hd] at he
  have he' : run u
      (cfg (some (.inl .start)) false (List.replicate (n + m) true)
        (List.replicate (m + 1) true) [] [] [] [] (List.replicate n true)
        (List.replicate m true) payload) =
      cfg (some (.inr .finish)) false [] (List.replicate (m + 1) true) []
        (List.replicate ((n + m) % (m + 1)) true)
        (List.replicate ((n + m) / (m + 1)) true) []
        (List.replicate n true) (List.replicate m true) payload := he
  have hf : run 1
      (cfg (some (.inr .finish)) false [] (List.replicate (m + 1) true) []
        (List.replicate ((n + m) % (m + 1)) true)
        (List.replicate ((n + m) / (m + 1)) true) []
        (List.replicate n true) (List.replicate m true) payload) =
      cfg none false [] (List.replicate (m + 1) true) []
        (List.replicate ((n + m) % (m + 1)) true)
        (List.replicate (copyCount n m) true) []
        (List.replicate n true) (List.replicate m true) payload := by
    generalize hq : (n + m) / (m + 1) = q
    unfold copyCount
    rw [hq]
    cases q with
    | zero =>
        apply congrArg (fun S => (⟨none, (false, ()), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
    | succ q =>
        rw [Nat.max_eq_right (by omega : 1 ≤ q + 1)]
        apply congrArg (fun S => (⟨none, (false, ()), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
  refine ⟨2 * n + 2 * m + 5 + u + 1, ?_, ?_⟩
  · have hb := MatrixUnaryDivision.exactTime_bound (n + m) (m + 1)
    omega
  · exact (run_add ((run_add (prepare_run n m payload) u).trans he') 1).trans hf

end EthInapproximability.CurrentPaper.SourceNormalizationMachineCounts
