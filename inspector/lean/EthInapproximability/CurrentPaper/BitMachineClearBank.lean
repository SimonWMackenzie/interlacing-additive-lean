import EthInapproximability.CurrentPaper.BitMachineSubroutine
import Mathlib.Data.Fin.VecNotation

/-!
# Clearing a finite bank of Boolean stacks

Source: fixed bit-machine implementation in frozen v8 `06-eth.tex` and
`B-effectivity-details.tex`. Each Boolean cell is explicitly popped. The
program has one finite loop label per bank stack and a final reset label.
Foreign stacks are unchanged, and the runtime charges every discarded cell,
every empty-stack test, and the final finite-control reset.
-/

namespace EthInapproximability.CurrentPaper.BitMachineClearBank

open Turing
open BitMachineEncoding
open scoped BigOperators

variable {K L V : Type*} [DecidableEq K]

def clearStep (source : K) (again next : L) :
    TM2.Stmt (fun _ : K => Bool) L (V × Option Bool) :=
  .pop source (fun v b => (v.1, b))
    (.branch (fun v => v.2.isSome)
      (.load (fun v => (v.1, none)) (.goto (fun _ => again)))
      (.load (fun v => (v.1, none)) (.goto (fun _ => next))))

def finishStep (reset : V → V) (next : L) :
    TM2.Stmt (fun _ : K => Bool) L (V × Option Bool) :=
  .load (fun v => (reset v.1, none)) (.goto (fun _ => next))

def cleared {n : ℕ} (bank : Fin n → K) (S : K → List Bool) : K → List Bool :=
  fun k => if ∃ i, bank i = k then [] else S k

theorem cleared_zero (bank : Fin 0 → K) (S : K → List Bool) : cleared bank S = S := by
  funext k
  simp [cleared]

theorem cleared_succ {n : ℕ} (bank : Fin (n + 1) → K) (S : K → List Bool) :
    cleared (fun i : Fin n => bank i.succ) (Function.update S (bank 0) []) =
      cleared bank S := by
  funext k
  by_cases hh : bank 0 = k
  · subst k; simp [cleared]
  · have hk : k ≠ bank 0 := Ne.symm hh
    by_cases ht : ∃ i : Fin n, bank i.succ = k <;>
      simp [cleared, Fin.exists_fin_succ, hh, hk, ht]

theorem clear_one_run
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source : K) (again next : L) (hp : P again = clearStep source again next)
    (v : V) (S : K → List Bool) :
    ((advance P)^[(S source).length + 1]) ⟨some again, (v, none), S⟩ =
      ⟨some next, (v, none), Function.update S source []⟩ := by
  generalize hs : S source = bits
  induction bits generalizing S with
  | nil =>
      simp [advance, TM2.step, hp, clearStep, TM2.stepAux, hs]
  | cons b bits ih =>
      have hstep : advance P ⟨some again, (v, none), S⟩ =
          ⟨some again, (v, none), Function.update S source bits⟩ := by
        simp [advance, TM2.step, hp, clearStep, TM2.stepAux, hs]
      rw [List.length_cons, Function.iterate_succ_apply, hstep,
        ih _ (Function.update_self source bits S)]
      congr 1
      funext k
      by_cases hk : k = source <;> simp [Function.update_apply, hk]

/-- The ambient controller executes the prescribed clear-bank statements;
this theorem proves the complete operational run, not merely its cost. -/
theorem clear_bank_run
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (reset : V → V) (next : L) (n : ℕ) (bank : Fin n → K)
    (hbank : Function.Injective bank) (label : Fin (n + 1) → L)
    (hsteps : ∀ i : Fin n, P (label i.castSucc) =
      clearStep (bank i) (label i.castSucc) (label i.succ))
    (hfinish : P (label (Fin.last n)) = finishStep reset next)
    (v : V) (S : K → List Bool) :
    ((advance P)^[(∑ i, (S (bank i)).length) + n + 1])
      ⟨some (label 0), (v, none), S⟩ =
      ⟨some next, (reset v, none), cleared bank S⟩ := by
  induction n generalizing S with
  | zero =>
      have hf : P (label 0) = finishStep reset next := hfinish
      simp [advance, TM2.step, hf, finishStep, TM2.stepAux, cleared_zero]
  | succ n ih =>
      let tailBank : Fin n → K := fun i => bank i.succ
      let tailLabel : Fin (n + 1) → L := fun i => label i.succ
      let S' := Function.update S (bank 0) []
      have htailInj : Function.Injective tailBank := hbank.comp (Fin.succ_injective n)
      have htailSteps : ∀ i : Fin n, P (tailLabel i.castSucc) =
          clearStep (tailBank i) (tailLabel i.castSucc) (tailLabel i.succ) := by
        intro i
        exact hsteps i.succ
      have htailFinish : P (tailLabel (Fin.last n)) = finishStep reset next := hfinish
      have htail := ih tailBank htailInj tailLabel htailSteps htailFinish S'
      have hsums : (∑ i : Fin n, (S' (tailBank i)).length) =
          ∑ i : Fin n, (S (bank i.succ)).length := by
        apply Finset.sum_congr rfl
        intro i _
        have hne : bank i.succ ≠ bank 0 := by
          intro h
          have he := hbank h
          have hv := congrArg Fin.val he
          simp at hv
        simp [S', tailBank, hne]
      rw [hsums] at htail
      have htime : (∑ i : Fin (n + 1), (S (bank i)).length) + (n + 1) + 1 =
          ((∑ i : Fin n, (S (bank i.succ)).length) + n + 1) +
            ((S (bank 0)).length + 1) := by
        rw [Fin.sum_univ_succ]
        omega
      rw [htime, Function.iterate_add_apply,
        clear_one_run P (bank 0) (label 0) (label (Fin.succ 0)) (hsteps 0) v S]
      change ((advance P)^[(∑ i : Fin n, (S (bank i.succ)).length) + n + 1])
        ⟨some (tailLabel 0), (v, none), S'⟩ = _
      rw [htail]
      congr 1
      exact cleared_succ bank S

theorem cleared_bank {n : ℕ} (bank : Fin n → K) (S : K → List Bool) (i : Fin n) :
    cleared bank S (bank i) = [] := by simp [cleared]

theorem cleared_foreign {n : ℕ} (bank : Fin n → K) (S : K → List Bool) (k : K)
    (hk : ∀ i, bank i ≠ k) : cleared bank S k = S k := by simp [cleared, hk]

end EthInapproximability.CurrentPaper.BitMachineClearBank
