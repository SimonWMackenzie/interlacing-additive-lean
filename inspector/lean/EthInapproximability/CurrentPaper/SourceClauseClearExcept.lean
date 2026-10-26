import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Charged cleanup between clause-writer calls

For a fixed finite stack alphabet and fixed set of retained registers, this
machine physically pops every other register. The retained registers can be
the validated row, persistent unary counters, reversed clause payload, and
clause count. It is a reusable reset component, not an assertion that a
particular row-gate endpoint has already been recycled.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseClearExcept

open Turing BitMachineEncoding

variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev Work (keep : Finset K) := {k : K // k ∉ keep}
abbrev workCount (keep : Finset K) := Fintype.card (Work keep)

noncomputable def workBank (keep : Finset K) : Fin (workCount keep) → K :=
  fun i => ((Fintype.equivFin (Work keep)).symm i).val

theorem workBank_injective (keep : Finset K) :
    Function.Injective (workBank keep) := by
  intro i j h
  apply (Fintype.equivFin (Work keep)).symm.injective
  apply Subtype.ext
  exact h

theorem workBank_range (keep : Finset K) (x : K) :
    (∃ i, workBank keep i = x) ↔ x ∉ keep := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ((Fintype.equivFin (Work keep)).symm i).property
  · intro hx
    let y : Work keep := ⟨x, hx⟩
    refine ⟨Fintype.equivFin (Work keep) y, ?_⟩
    simp [workBank, y]

inductive Label (n : ℕ) where
  | clear : Fin (n + 1) → Label n
  | done
  deriving DecidableEq, Fintype

noncomputable def program (keep : Finset K) :
    Label (workCount keep) →
      TM2.Stmt (fun _ : K => Bool) (Label (workCount keep))
        (Unit × Option Bool)
  | .clear i => if h : i.val < workCount keep then
      BitMachineClearBank.clearStep (workBank keep ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep id .done
  | .done => .halt

theorem step_rule (keep : Finset K) (i : Fin (workCount keep)) :
    program keep (.clear i.castSucc) =
      BitMachineClearBank.clearStep (workBank keep i)
        (.clear i.castSucc) (.clear i.succ) := by
  have hi : (i.castSucc : Fin (workCount keep + 1)).val < workCount keep := i.isLt
  simp only [program, dif_pos hi]
  rfl

theorem finish_rule (keep : Finset K) :
    program keep (.clear (Fin.last (workCount keep))) =
      BitMachineClearBank.finishStep id .done := by
  simp [program]

theorem cleaned_eq (keep : Finset K) (S : K → List Bool) (x : K) :
    BitMachineClearBank.cleared (workBank keep) S x =
      if x ∈ keep then S x else [] := by
  simp [BitMachineClearBank.cleared, workBank_range keep x]

noncomputable def result (keep : Finset K) (S : K → List Bool) :
    K → List Bool := fun x => if x ∈ keep then S x else []

theorem run (keep : Finset K) (S : K → List Bool) :
    ((advance (program keep))^[
      (∑ i : Fin (workCount keep), (S (workBank keep i)).length) +
        workCount keep + 2])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label (workCount keep))
          (Unit × Option Bool)) =
      ⟨none, ((), none), result keep S⟩ := by
  have hc := BitMachineClearBank.clear_bank_run (program keep) id .done
    (workCount keep) (workBank keep) (workBank_injective keep)
    (fun i => Label.clear i) (step_rule keep) (finish_rule keep)
    () S
  rw [show (∑ i : Fin (workCount keep), (S (workBank keep i)).length) +
      workCount keep + 2 =
      ((∑ i : Fin (workCount keep), (S (workBank keep i)).length) +
        workCount keep + 1) + 1 by omega,
    Function.iterate_succ_apply']
  rw [hc]
  simp only [advance, TM2.step, program, TM2.stepAux,
    Option.getD_some]
  congr 1
  funext x
  exact cleaned_eq keep S x

theorem retained (keep : Finset K) (S : K → List Bool)
    (x : K) (hx : x ∈ keep) : result keep S x = S x := by
  simp [result, hx]

theorem emptied (keep : Finset K) (S : K → List Bool)
    (x : K) (hx : x ∉ keep) : result keep S x = [] := by
  simp [result, hx]

end EthInapproximability.CurrentPaper.SourceClauseClearExcept
