import EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
import EthInapproximability.CurrentPaper.GenericPairOneMachine

/-! Exact finite physical composition of all ordered pairs at one vertex.
The one-pair callback is the concrete checked routine, not an assumed oracle. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF SourceGenericPrefix
open SourceBooleanPrefix SourceBooleanPrefix.PairMachineComposition
open SourceGenericPrefixMachine

def payload {n a : Nat} (q : Nat) (v : Fin n)
    (st : Fin a × Fin a) : List Bool :=
  (clauseFields (pairChain q v st)).reverse

private theorem clauseFields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clauseFields, ih, List.append_assoc]

theorem foldSaved_source {n a : Nat} (q : Nat) (v : Fin n)
    (xs : List (Fin a × Fin a)) (saved : List Bool) :
    foldSaved (payload q v) xs saved =
      (clauseFields ((xs.map (pairChain q v)).flatten)).reverse ++ saved := by
  induction xs generalizing saved with
  | nil => simp [foldSaved, clauseFields]
  | cons st xs ih =>
      change foldSaved (payload q v) xs (payload q v st ++ saved) =
        (clauseFields (pairChain q v st ++
          (xs.map (pairChain q v)).flatten)).reverse ++ saved
      rw [ih]
      simp only [clauseFields_append, List.reverse_append, payload]
      simp [List.append_assoc]

noncomputable def vertexRoutine (a q : Nat) : Routine :=
  listRoutine (fun st : Fin a × Fin a =>
    PairOneMachine.routine a q st.1 st.2) (pairs a)

noncomputable def vertexCost {n : Nat} (a q : Nat) (v : Fin n)
    (saved output count : List Bool) : Nat :=
  listCost (fun st saved output count =>
      PairOneMachine.cost (q := q) v st.1 st.2 saved output count)
    (payload q v) (pairs a) saved output count

theorem vertex_run {n a : Nat} (q : Nat) (v : Fin n)
    (saved output count : List Bool) :
    Runs (vertexRoutine a q)
      (PairUnitLift.pairBank n v.val 0 saved output count)
      (PairUnitLift.pairBank n v.val 0
        ((clauseFields (vertexChains a q v)).reverse ++ saved)
        output (List.replicate (8*(a*a)) true ++ count))
      (vertexCost a q v saved output count) := by
  have hstep : ∀ st : Fin a × Fin a, ∀ saved output count,
      Runs (PairOneMachine.routine a q st.1 st.2)
        (PairUnitLift.pairBank n v.val 0 saved output count)
        (PairUnitLift.pairBank n v.val 0
          (payload q v st ++ saved) output
          (List.replicate 8 true ++ count))
        (PairOneMachine.cost (q := q) v st.1 st.2 saved output count) := by
    intro st saved output count
    rcases st with ⟨s,t⟩
    simpa only [payload, pairChain] using
      (PairOneMachine.run (q := q) v s t saved output count)
  have h := list_run n v.val
    (fun st : Fin a × Fin a => PairOneMachine.routine a q st.1 st.2)
    (fun st saved output count =>
      PairOneMachine.cost (q := q) v st.1 st.2 saved output count)
    (payload q v) (pairs a) saved output count hstep
  rw [foldSaved_source q v (pairs a) saved, pairs_length] at h
  exact h

#print axioms foldSaved_source
#print axioms vertex_run

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
