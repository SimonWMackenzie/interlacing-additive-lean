import Paper2.CappedTicketCodec
import Paper2.RecursiveLabelCodec
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import Mathlib.Tactic

namespace Paper2.TicketStatus

set_option maxRecDepth 16384

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition

abbrev Stack := Fin 10 ⊕ Fin 1
def result : Stack := .inl 9
def accumulator : Stack := .inr 0

inductive Label where
  | first | tally
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .first =>
      pop result (fun _ b => b)
        (branch Option.isSome
          (push accumulator (fun _ => false) (goto (fun _ => .tally)))
          (load (fun _ => some false) halt))
  | .tally =>
      pop result (fun _ b => b)
        (branch Option.isSome
          (push accumulator (fun _ => true) (goto (fun _ => .tally)))
          (load (fun _ => some true) halt))

def bank (S : Fin 10 → List Bool) (acc : List Bool) : Stack → List Bool :=
  Sum.elim S (fun _ => acc)

def cfg (l : Option Label) (v : Option Bool) (S : Fin 10 → List Bool)
    (acc : List Bool) : TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool) :=
  ⟨l, v, bank S acc⟩

private theorem first_abort (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = []) :
    advance program (cfg (some .first) none S acc) = cfg none (some false) S acc := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank, result, h]
  simp only [Sum.elim_inl, h, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => by_cases hk : k = 9 <;> simp [Function.update, hk, h]
  | inr k => fin_cases k <;> simp [Function.update]

private theorem first_success (S : Fin 10 → List Bool) (acc : List Bool)
    (q : List Bool) (h : S 9 = true :: q) :
    advance program (cfg (some .first) none S acc) =
      cfg (some .tally) (some true) (Function.update S 9 q) (false :: acc) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    result, accumulator, h]
  simp only [Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => simp [bank, Function.update]
  | inr k => fin_cases k <;> rfl

private theorem tally_success (S : Fin 10 → List Bool) (acc : List Bool)
    (q : List Bool) (h : S 9 = true :: q) :
    advance program (cfg (some .tally) (some true) S acc) =
      cfg (some .tally) (some true) (Function.update S 9 q) (true :: acc) := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank,
    result, accumulator, h]
  simp only [Sum.elim_inl, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => simp [bank, Function.update]
  | inr k => fin_cases k <;> rfl

private theorem tally_done (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = []) :
    advance program (cfg (some .tally) (some true) S acc) = cfg none (some true) S acc := by
  simp only [advance, TM2.step, TM2.stepAux, program, cfg, bank, result, h]
  simp only [Sum.elim_inl, h, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => by_cases hk : k = 9 <;> simp [Function.update, hk, h]
  | inr k => fin_cases k <;> simp [Function.update]

theorem abort (S : Fin 10 → List Bool) (acc : List Bool) (h : S 9 = []) :
    ((advance program)^[1]) (cfg (some .first) none S acc) =
      cfg none (some false) S acc := by simpa using first_abort S acc h

theorem tally (q : ℕ) (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = List.replicate q true) :
    ((advance program)^[q+1]) (cfg (some .tally) (some true) S acc) =
      cfg none (some true) (Function.update S 9 []) (List.replicate q true ++ acc) := by
  induction q generalizing S acc with
  | zero =>
      have hn : S 9 = [] := by simpa using h
      simpa [show Function.update S 9 [] = S by funext k; by_cases hk : k = 9 <;> simp [Function.update, hk, hn]]
        using tally_done S acc hn
  | succ q ih =>
      have hc : S 9 = true :: List.replicate q true := by simpa using h
      have hs := tally_success S acc (List.replicate q true) hc
      rw [show q + 1 + 1 = (q+1)+1 by omega,
        Function.iterate_succ_apply, hs]
      have hh : (Function.update S 9 (List.replicate q true)) 9 =
          List.replicate q true := by simp
      rw [ih _ _ hh]
      simp [Function.update_idem, List.replicate_succ', List.append_assoc]

theorem success (q : ℕ) (S : Fin 10 → List Bool) (acc : List Bool)
    (h : S 9 = true :: List.replicate q true) :
    ((advance program)^[q+2]) (cfg (some .first) none S acc) =
      cfg none (some true) (Function.update S 9 [])
        (List.replicate q true ++ [false] ++ acc) := by
  have hs := first_success S acc (List.replicate q true) h
  have ht := tally q (Function.update S 9 (List.replicate q true)) (false :: acc)
    (by simp)
  rw [show q+2 = (q+1)+1 by omega, Function.iterate_succ_apply, hs, ht]
  simp [Function.update_idem, List.append_assoc]


#print axioms abort
#print axioms success

end Paper2.TicketStatus
