import EthInapproximability.CurrentPaper.GenericPairVertexLoopCallback

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairVertexLoop

open Turing BitMachineEncoding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceGenericPairEnumeration
open scoped Classical

def word (n a q k : Nat) : List Bool :=
  if h : k < n then
    (clauseFields (vertexChains a q (⟨k,h⟩ : Fin n))).reverse
  else []

def savedAt (n a q : Nat) (saved : List Bool) : Nat → List Bool
  | 0 => saved
  | k+1 => word n a q k ++ savedAt n a q saved k

def countAt (a : Nat) (count : List Bool) (k : Nat) : List Bool :=
  List.replicate ((8*(a*a))*k) true ++ count

theorem word_of_lt (n a q k : Nat) (h : k < n) :
    word n a q k =
      (clauseFields (vertexChains a q (⟨k,h⟩ : Fin n))).reverse := by
  simp [word,h]

theorem countAt_next (a : Nat) (count : List Bool) (k : Nat) :
    countAt a count (k+1) =
      List.replicate (8*(a*a)) true ++ countAt a count k := by
  unfold countAt
  rw [show (8*(a*a))*(k+1) = (8*(a*a))+(8*(a*a))*k by ring,
    List.replicate_add,List.append_assoc]

noncomputable def callCost (n a q : Nat)
    (saved output count : List Bool) (k : Nat) : Nat :=
  if h : k < n then
    vertexCost a q (⟨k,h⟩ : Fin n)
      (savedAt n a q saved k) output (countAt a count k)
  else 0

noncomputable def tailCost (n a q : Nat)
    (saved output count : List Bool) (k : Nat) : Nat → Nat
  | 0 => 1
  | r+1 => 2 + callCost n a q saved output count k +
      tailCost n a q saved output count (k+1) r

noncomputable def checking (n a q k r : Nat)
    (saved output count : List Bool) :=
  (⟨some (.inr .check),
    ((PairVertexLoopCallback.routine a q).initial,none),
    PairVertexLoopMachine.blank n k
      (savedAt n a q saved k) output (countAt a count k)
      (List.replicate r true)⟩ :
    PairVertexLoopMachine.Config
      (PairVertexLoopCallback.routine a q).Label
      (PairVertexLoopCallback.routine a q).Control)

noncomputable def finished (n a q : Nat)
    (saved output count : List Bool) :=
  (⟨none,
    ((PairVertexLoopCallback.routine a q).initial,none),
    PairVertexLoopMachine.blank n n
      (savedAt n a q saved n) output (countAt a count n) []⟩ :
    PairVertexLoopMachine.Config
      (PairVertexLoopCallback.routine a q).Label
      (PairVertexLoopCallback.routine a q).Control)

private theorem run_add {L V : Type*}
    (P : L → TM2.Stmt (fun _ : PairVertexLoopMachine.Stack => Bool) L V)
    {c c' : TM2.Cfg (fun _ : PairVertexLoopMachine.Stack => Bool) L V}
    {x : Nat} (h : ((advance P)^[x]) c = c') (y : Nat) :
    ((advance P)^[x+y]) c = ((advance P)^[y]) c' := by
  rw [Nat.add_comm,Function.iterate_add_apply]
  exact congrArg ((advance P)^[y]) h

theorem tail_run (n a q k r : Nat) (saved output count : List Bool)
    (hk : k+r=n) :
    ∃ u ≤ tailCost n a q saved output count k r,
      ((advance (PairVertexLoopCallback.program a q))^[u])
        (checking n a q k r saved output count) =
        finished n a q saved output count := by
  induction r generalizing k with
  | zero =>
      have hkn : k=n := by omega
      subst k
      refine ⟨1,by simp [tailCost],?_⟩
      simpa only [checking,finished,Function.iterate_one] using
        (PairVertexLoopMachine.check_done
          (PairVertexLoopCallback.routine a q).program
          (PairVertexLoopCallback.routine a q).start
          (PairVertexLoopCallback.routine a q).initial
          n n (savedAt n a q saved n) output (countAt a count n))
  | succ r ih =>
      have hlt : k<n := by omega
      have hnext : k+1+r=n := by omega
      let S := savedAt n a q saved k
      let C := countAt a count k
      let rest := List.replicate r true
      let v : Fin n := ⟨k,hlt⟩
      have hcheck :
          ((advance (PairVertexLoopCallback.program a q))^[1])
            (checking n a q k (r+1) saved output count) =
            ⟨some (.inl (PairVertexLoopCallback.routine a q).start),
              ((PairVertexLoopCallback.routine a q).initial,none),
              PairVertexLoopMachine.blank n k S output C rest⟩ := by
        simpa only [checking,S,C,rest,List.replicate_succ,
          Function.iterate_one,PairVertexLoopCallback.program] using
          (PairVertexLoopMachine.check_more
            (PairVertexLoopCallback.routine a q).program
            (PairVertexLoopCallback.routine a q).start
            (PairVertexLoopCallback.routine a q).initial
            n k S output C rest)
      obtain ⟨u,hu,hcallback⟩ := PairVertexLoopCallback.run q v S output C rest
      have hcost : callCost n a q saved output count k =
          vertexCost a q v S output C := by
        simp [callCost,hlt,v,S,C]
      have hnextSaved : savedAt n a q saved (k+1) = word n a q k ++ S := rfl
      have hchain : word n a q k =
          (clauseFields (vertexChains a q v)).reverse :=
        word_of_lt n a q k hlt
      have hincrement :
          ((advance (PairVertexLoopCallback.program a q))^[1])
            ⟨some (.inr .increment),
              ((PairVertexLoopCallback.routine a q).initial,none),
              PairVertexLoopMachine.blank n k
                (word n a q k ++ S) output
                (List.replicate (8*(a*a)) true ++ C) rest⟩ =
            checking n a q (k+1) r saved output count := by
        simpa only [checking,PairVertexLoopCallback.program,
          Function.iterate_one,hnextSaved,countAt_next,S,C,rest] using
          (PairVertexLoopMachine.increment_step
            (PairVertexLoopCallback.routine a q).program
            (PairVertexLoopCallback.routine a q).start
            (PairVertexLoopCallback.routine a q).initial
            n k (word n a q k ++ S) output
            (List.replicate (8*(a*a)) true ++ C) rest)
      obtain ⟨z,hz,htail⟩ := ih (k+1) hnext
      have hcallback' :
          ((advance (PairVertexLoopCallback.program a q))^[u])
            ⟨some (.inl (PairVertexLoopCallback.routine a q).start),
              ((PairVertexLoopCallback.routine a q).initial,none),
              PairVertexLoopMachine.blank n k S output C rest⟩ =
            ⟨some (.inr .increment),
              ((PairVertexLoopCallback.routine a q).initial,none),
              PairVertexLoopMachine.blank n k (word n a q k ++ S)
                output (List.replicate (8*(a*a)) true ++ C) rest⟩ := by
        simpa only [v,Fin.val_mk,hchain] using hcallback
      have hfirst := run_add (PairVertexLoopCallback.program a q) hcheck u
      rw [hcallback'] at hfirst
      have hsecond := run_add (PairVertexLoopCallback.program a q) hfirst 1
      rw [hincrement] at hsecond
      have htotal := run_add (PairVertexLoopCallback.program a q) hsecond z
      rw [htail] at htotal
      refine ⟨1+u+1+z,?_,?_⟩
      · simp only [tailCost]
        rw [hcost]
        omega
      · exact htotal

def prefixFields (n a q k : Nat) : List Bool :=
  (List.range k).flatMap (fun j => (word n a q j).reverse)

theorem savedAt_eq_prefix (n a q k : Nat) (saved : List Bool) :
    savedAt n a q saved k = (prefixFields n a q k).reverse ++ saved := by
  induction k with
  | zero => simp [savedAt,prefixFields]
  | succ k ih =>
      rw [savedAt,ih]
      simp only [prefixFields,List.range_succ,List.flatMap_append,
        List.flatMap_singleton,List.reverse_append,List.reverse_reverse]
      simp [List.append_assoc]

theorem run (n a q : Nat) (saved output count : List Bool) :
    ∃ u ≤ 2*n+2+tailCost n a q saved output count 0 n,
      ((advance (PairVertexLoopCallback.program a q))^[u])
        (⟨some (.inr .copyScan),
          ((PairVertexLoopCallback.routine a q).initial,none),
          PairVertexLoopMachine.blank n 0 saved output count []⟩ :
          PairVertexLoopMachine.Config
            (PairVertexLoopCallback.routine a q).Label
            (PairVertexLoopCallback.routine a q).Control) =
        ⟨none,((PairVertexLoopCallback.routine a q).initial,none),
          PairVertexLoopMachine.blank n n
            ((prefixFields n a q n).reverse ++ saved)
            output (List.replicate ((8*(a*a))*n) true ++ count) []⟩ := by
  have hcopy := PairVertexLoopMachine.copy_prep
    (PairVertexLoopCallback.routine a q).program
    (PairVertexLoopCallback.routine a q).start
    (PairVertexLoopCallback.routine a q).initial n saved output count
  obtain ⟨u,hu,htail⟩ := tail_run n a q 0 n saved output count (by omega)
  have hcombo := run_add (PairVertexLoopCallback.program a q) hcopy u
  change ((advance (PairVertexLoopCallback.program a q))^[2*n+2+u])
    (⟨some (.inr .copyScan),
      ((PairVertexLoopCallback.routine a q).initial,none),
      PairVertexLoopMachine.blank n 0 saved output count []⟩ :
      PairVertexLoopMachine.Config
        (PairVertexLoopCallback.routine a q).Label
        (PairVertexLoopCallback.routine a q).Control) =
    ((advance (PairVertexLoopCallback.program a q))^[u])
      (checking n a q 0 n saved output count) at hcombo
  rw [htail] at hcombo
  refine ⟨2*n+2+u,by omega,?_⟩
  simpa only [finished,countAt,savedAt,savedAt_eq_prefix,
    List.replicate_zero,List.nil_append] using hcombo

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairVertexLoop
