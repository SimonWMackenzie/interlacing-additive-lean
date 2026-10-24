import EthInapproximability.CurrentPaper.SourceGenericOrder
import EthInapproximability.CurrentPaper.SourceClauseCircuitClock
import EthInapproximability.CurrentPaper.SourceClausePairUnitLift
import EthInapproximability.CurrentPaper.SourceClausePairMachineComposition

/-! Source-ordered finite pair enumeration for one vertex. The physical
one-pair callback is deliberately supplied only by a later concrete module. -/

namespace EthInapproximability.CurrentPaper.SourceGenericPairEnumeration

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF SourceGenericPrefix
open SourceClauseCallback
open SourceBooleanPrefix
open SourceBooleanPrefix.PairMachineComposition

/-- All ordered alphabet pairs, with the first coordinate outermost. -/
def pairs (a : Nat) : List (Fin a × Fin a) :=
  (List.ofFn fun s : Fin a => List.ofFn fun t : Fin a => (s,t)).flatten

theorem pairs_eq_source_order (a : Nat) :
    pairs a =
      List.ofFn (fun u : Fin (a*a) => finProdFinEquiv.symm u) := by
  unfold pairs
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext s
  apply congrArg List.ofFn
  funext t
  have hu : (⟨s.val*a+t.val, by
      have hs := s.isLt
      have ht := t.isLt
      nlinarith⟩ : Fin (a*a)) = finProdFinEquiv (s,t) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [hu, Equiv.symm_apply_apply]

def pairChain {n a : Nat} (q : Nat) (v : Fin n)
    (st : Fin a × Fin a) : List Clause :=
  chain (base n a q (pairOrdinal v st.1 st.2))
    (pairPayload v st.1 st.2)

def vertexChains {n : Nat} (a q : Nat) (v : Fin n) : List Clause :=
  ((pairs a).map (pairChain q v)).flatten

theorem vertexChains_eq_source {n a : Nat} (q : Nat) (v : Fin n) :
    vertexChains a q v =
      (List.ofFn fun u : Fin (a*a) =>
        let st : Fin a × Fin a := finProdFinEquiv.symm u
        chain (base n a q (pairOrdinal v st.1 st.2))
          (pairPayload v st.1 st.2)).flatten := by
  simp only [vertexChains, pairs_eq_source_order, List.map_ofFn]
  rfl

theorem pairs_length (a : Nat) : (pairs a).length = a*a := by
  rw [pairs_eq_source_order]
  simp

theorem vertexChains_length {n a : Nat} (q : Nat) (v : Fin n) :
    (vertexChains a q v).length = 8*(a*a) := by
  rw [vertexChains_eq_source]
  -- Every indexed pair chain has length eight, including the diagonal.
  have hs : ∀ u : Fin (a*a),
      (pairChain q v (finProdFinEquiv.symm u)).length = 8 := by
    intro u
    exact SourceGenericPrefix.pair_chain_length v _ _
  simp only [List.length_flatten, List.map_ofFn]
  have hm : List.ofFn (fun u : Fin (a*a) =>
      (pairChain q v (finProdFinEquiv.symm u)).length) =
      List.ofFn (fun _ : Fin (a*a) => 8) := by
    apply congrArg List.ofFn
    funext u
    exact hs u
  change (List.ofFn (fun u : Fin (a*a) =>
    (pairChain q v (finProdFinEquiv.symm u)).length)).sum = 8*(a*a)
  rw [hm]
  simp [List.ofFn_const, Nat.mul_comm]

/-! The finite-sequence machinery below is intentionally generic. A concrete
pair endpoint must still supply `hstep`; no desired output or runtime
certificate is built into the controller. -/

def idle : Routine :=
  fromProgram (fun _ : Unit => Turing.TM2.Stmt.halt) () ()

theorem idle_run (S : PairUnitLift.Stack → List Bool) : Runs idle S S 1 := by
  exact ⟨1, le_rfl, rfl⟩

noncomputable def listRoutine {α : Type} (C : α → Routine) :
    List α → Routine
  | [] => idle
  | x :: xs => sequence (C x) (listRoutine C xs)

def foldSaved {α : Type} (payload : α → List Bool)
    (xs : List α) (saved : List Bool) : List Bool :=
  xs.foldl (fun acc x => payload x ++ acc) saved

noncomputable def listCost {α : Type}
    (stepCost : α → List Bool → List Bool → List Bool → Nat)
    (payload : α → List Bool) : List α → List Bool → List Bool → List Bool → Nat
  | [], _, _, _ => 1
  | x :: xs, saved, output, count =>
      stepCost x saved output count +
        listCost stepCost payload xs (payload x ++ saved) output
          (List.replicate 8 true ++ count) + 1

theorem list_run {α : Type} (n vertex : Nat)
    (C : α → Routine)
    (stepCost : α → List Bool → List Bool → List Bool → Nat)
    (payload : α → List Bool) (xs : List α)
    (saved output count : List Bool)
    (hstep : ∀ x saved output count,
      Runs (C x)
        (PairUnitLift.pairBank n vertex 0 saved output count)
        (PairUnitLift.pairBank n vertex 0
          (payload x ++ saved) output (List.replicate 8 true ++ count))
        (stepCost x saved output count)) :
    Runs (listRoutine C xs)
      (PairUnitLift.pairBank n vertex 0 saved output count)
      (PairUnitLift.pairBank n vertex 0
        (foldSaved payload xs saved) output
        (List.replicate (8*xs.length) true ++ count))
      (listCost stepCost payload xs saved output count) := by
  induction xs generalizing saved count with
  | nil =>
      simpa [listRoutine, listCost, foldSaved] using
        idle_run (PairUnitLift.pairBank n vertex 0 saved output count)
  | cons x xs ih =>
      have hhead := hstep x saved output count
      have htail := ih (payload x ++ saved) (List.replicate 8 true ++ count)
      have hseq := runs_sequence (C x) (listRoutine C xs)
        (PairUnitLift.pairBank n vertex 0 saved output count)
        (PairUnitLift.pairBank n vertex 0
          (payload x ++ saved) output (List.replicate 8 true ++ count))
        (PairUnitLift.pairBank n vertex 0
          (foldSaved payload xs (payload x ++ saved)) output
          (List.replicate (8*xs.length) true ++
            (List.replicate 8 true ++ count)))
        (stepCost x saved output count)
        (listCost stepCost payload xs (payload x ++ saved) output
          (List.replicate 8 true ++ count)) hhead htail
      have hcount :
          List.replicate (8*(x::xs).length) true ++ count =
            List.replicate (8*xs.length) true ++
              (List.replicate 8 true ++ count) := by
        rw [List.length_cons, Nat.mul_add, Nat.mul_one,
          List.replicate_add, List.append_assoc]
      simpa only [listRoutine, listCost, foldSaved, List.foldl_cons,
        hcount] using hseq

#print axioms pairs_eq_source_order
#print axioms vertexChains_eq_source
#print axioms vertexChains_length
#print axioms list_run

end EthInapproximability.CurrentPaper.SourceGenericPairEnumeration
