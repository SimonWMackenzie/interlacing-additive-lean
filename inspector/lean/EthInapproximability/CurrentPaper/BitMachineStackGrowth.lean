import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# A uniform stack-growth bound for finite Boolean-stack programs

A single transition executes one finite statement tree. The number of
pushes along any branch is bounded by the syntax of that tree, independent
of data on the stacks. Taking a finite supremum over instruction labels
gives a concrete machine-dependent per-transition growth constant.
-/

namespace EthInapproximability.CurrentPaper.BitMachineStackGrowth

open Turing BitMachineEncoding

variable {K L V : Type*} [DecidableEq K]

def pushes : TM2.Stmt (fun _ : K => Bool) L V → Nat
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

private theorem update_cons_length_le (S : K → List Bool)
    (k j : K) (b : Bool) :
    (Function.update S k (b :: S k) j).length ≤ (S j).length + 1 := by
  by_cases h : j = k
  · subst j
    simp
  · rw [Function.update_of_ne h]
    omega

private theorem update_tail_length_le (S : K → List Bool)
    (k j : K) :
    (Function.update S k (S k).tail j).length ≤ (S j).length := by
  by_cases h : j = k
  · subst j
    simp
  · rw [Function.update_of_ne h]

theorem stepAux_growth (q : TM2.Stmt (fun _ : K => Bool) L V)
    (v : V) (S : K → List Bool) (j : K) :
    ((TM2.stepAux q v S).stk j).length ≤ (S j).length + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
      simpa only [TM2.stepAux, pushes, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (Nat.le_trans (ih v (Function.update S k (f v :: S k)))
          (Nat.add_le_add_right (update_cons_length_le S k j (f v)) (pushes q)))
  | peek k f q ih =>
      simpa only [TM2.stepAux, pushes] using ih (f v ((S k).head?)) S
  | pop k f q ih =>
      have h := ih (f v ((S k).head?))
        (Function.update S k (S k).tail)
      simpa only [TM2.stepAux, pushes] using
        h.trans (Nat.add_le_add_right (update_tail_length_le S k j) (pushes q))
  | load f q ih =>
      simpa only [TM2.stepAux, pushes] using ih (f v) S
  | branch f q r ihq ihr =>
      cases h : f v
      · simpa only [TM2.stepAux, h, cond_false, pushes] using
          (ihr v S).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      · simpa only [TM2.stepAux, h, cond_true, pushes] using
          (ihq v S).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

def perStep [Fintype L] (P : L → TM2.Stmt (fun _ : K => Bool) L V) : Nat :=
  Finset.univ.sup (fun l => pushes (P l))

theorem pushes_le_perStep [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) (l : L) :
    pushes (P l) ≤ perStep P :=
  Finset.le_sup (f := fun x => pushes (P x)) (Finset.mem_univ l)

theorem advance_growth [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (j : K) :
    ((advance P c).stk j).length ≤ (c.stk j).length + perStep P := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => simp [advance, TM2.step]
  | some l =>
      simpa [advance, TM2.step] using
        (stepAux_growth (P l) v S j).trans
          (Nat.add_le_add_left (pushes_le_perStep P l) _)

theorem run_growth [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (t : Nat) (j : K) :
    ((((advance P)^[t]) c).stk j).length ≤
      (c.stk j).length + perStep P * t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have hs := advance_growth P (((advance P)^[t]) c) j
      simp only [Nat.mul_succ]
      omega

end EthInapproximability.CurrentPaper.BitMachineStackGrowth
