import EthInapproximability.CurrentPaper.SourceClauseRowTruthBranch

/-!
# Writing fixed unary operands by finite control

For fixed alphabet and arity, tuple symbols, literal positions, table
ordinals, and the chain width can be program constants. This tiny program
actually pushes their unary words; those words are not granted as data in the
initial bank. The target stack must start empty and all other stacks survive.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseFixedUnary

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Label (N : ℕ) := Fin (N + 1)

def program {K : Type*} [DecidableEq K] (target : K) (N : ℕ) :
    Label N → TM2.Stmt (fun _ : K => Bool) (Label N) Unit
  | i => if h : i.val < N then
      push target (fun _ => true)
        (goto (fun _ => ⟨i.val + 1, by omega⟩))
    else halt

def state {K : Type*} [DecidableEq K] {N : ℕ} (target : K)
    (S : K → List Bool) (i : Fin (N + 1)) (suffix : List Bool) :
    TM2.Cfg (fun _ : K => Bool) (Label N) Unit :=
  ⟨some i, (), Function.update S target (List.replicate i.val true ++ suffix)⟩

theorem step {K : Type*} [DecidableEq K] {N : ℕ} (target : K)
    (S : K → List Bool) (i : Fin (N + 1)) (h : i.val < N)
    (suffix : List Bool) :
    advance (program target N) (state target S i suffix) =
      state target S ⟨i.val + 1, by omega⟩ suffix := by
  simp only [advance, TM2.step, program, dif_pos h, TM2.stepAux,
    state, Function.update_self, Option.getD_some]
  congr 1
  funext x
  by_cases hx : x = target
  · subst x
    simp [Function.update, List.replicate_succ]
  · simp [Function.update, hx]

theorem finish {K : Type*} [DecidableEq K] {N : ℕ} (target : K)
    (S : K → List Bool) (i : Fin (N + 1)) (h : i.val = N)
    (suffix : List Bool) :
    advance (program target N) (state target S i suffix) =
      ⟨none, (), Function.update S target (List.replicate N true ++ suffix)⟩ := by
  have hn : ¬i.val < N := by omega
  simp [advance, TM2.step, program, hn, state, h]

theorem run_from {K : Type*} [DecidableEq K] {N : ℕ} (target : K)
    (S : K → List Bool) (i : Fin (N + 1)) (steps : ℕ)
    (hi : i.val + steps = N) (suffix : List Bool) :
    ((advance (program target N))^[steps + 1])
      (state target S i suffix) =
      ⟨none, (), Function.update S target (List.replicate N true ++ suffix)⟩ := by
  induction steps generalizing i with
  | zero =>
      exact finish target S i (by omega) suffix
  | succ steps ih =>
      have hlt : i.val < N := by omega
      let next : Fin (N + 1) := ⟨i.val + 1, by omega⟩
      have hn : next.val + steps = N := by simp only [next, Fin.val_mk]; omega
      rw [show (steps + 1) + 1 = (steps + 1) + 1 by rfl,
        Function.iterate_succ_apply, step target S i hlt suffix]
      exact ih next hn

theorem run {K : Type*} [DecidableEq K] (target : K)
    (S : K → List Bool) (N : ℕ) (h : S target = []) :
    ((advance (program target N))^[N + 1])
      (⟨some (0 : Label N), (), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label N) Unit) =
      ⟨none, (), Function.update S target (List.replicate N true)⟩ := by
  have hr := run_from target S (0 : Label N) N (by simp) []
  have hs : Function.update S target [] = S := by
    funext x
    by_cases hx : x = target <;> simp [Function.update, hx, h]
  simpa [state, hs] using hr

end EthInapproximability.CurrentPaper.SourceClauseFixedUnary
