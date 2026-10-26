import EthInapproximability.CurrentPaper.GenericAtLeastLoopCallback

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastLoop

open Turing BitMachineEncoding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

def word (n a q k : Nat) : List Bool :=
  if h : k < n then
    (clauseFields (chain (SourceGenericPrefix.base n a q k)
      (SourceGenericPrefix.atLeastPayload (a := a) (⟨k,h⟩ : Fin n)))).reverse
  else []

def savedAt (n a q : Nat) (saved : List Bool) : Nat → List Bool
  | 0 => saved
  | k+1 => word n a q k ++ savedAt n a q saved k

def countAt (a : Nat) (count : List Bool) (k : Nat) : List Bool :=
  List.replicate ((3*a+2)*k) true ++ count

theorem word_of_lt (n a q k : Nat) (h : k < n) :
    word n a q k =
      (clauseFields (chain (SourceGenericPrefix.base n a q k)
        (SourceGenericPrefix.atLeastPayload (a := a)
          (⟨k,h⟩ : Fin n)))).reverse := by
  simp [word,h]

theorem countAt_next (a : Nat) (count : List Bool) (k : Nat) :
    countAt a count (k+1) =
      List.replicate (3*a+2) true ++ countAt a count k := by
  unfold countAt
  rw [show (3*a+2)*(k+1) = (3*a+2)+(3*a+2)*k by ring,
    List.replicate_add,List.append_assoc]

noncomputable def callCost (n a q : Nat)
    (saved output count : List Bool) (k : Nat) : Nat :=
  if h : k < n then
    AtLeastClock.cost (a := a) (q := q) (⟨k,h⟩ : Fin n)
      (savedAt n a q saved k) output (countAt a count k)
  else 0

noncomputable def tailCost (n a q : Nat)
    (saved output count : List Bool) (k : Nat) : Nat → Nat
  | 0 => 1
  | r+1 => 2 + callCost n a q saved output count k +
      tailCost n a q saved output count (k+1) r

private def cfgOf {L V : Type*}
    (_ : L → TM2.Stmt (fun _ : PrefixLoopMachine.CoreStack => Bool) L V)
    (c : PrefixLoopMachine.Config L V) : PrefixLoopMachine.Config L V := c

noncomputable def checking (n a q k r : Nat)
    (saved output count : List Bool) :=
  cfgOf (AtLeastLoopCallback.callback a q).program
  ⟨some (.inr .check),((AtLeastLoopCallback.callback a q).initial,none),
    PrefixLoopMachine.blank n k (savedAt n a q saved k) output
      (countAt a count k) (List.replicate r true)⟩

noncomputable def finished (n a q : Nat)
    (saved output count : List Bool) :=
  cfgOf (AtLeastLoopCallback.callback a q).program
  ⟨none,((AtLeastLoopCallback.callback a q).initial,none),
    PrefixLoopMachine.blank n n (savedAt n a q saved n) output
      (countAt a count n) []⟩

private theorem run_add {L V : Type*}
    (P : L → TM2.Stmt (fun _ : PrefixLoopMachine.Stack => Bool) L V)
    {c c' : TM2.Cfg (fun _ : PrefixLoopMachine.Stack => Bool) L V}
    {x : Nat} (h : ((advance P)^[x]) c = c') (y : Nat) :
    ((advance P)^[x+y]) c = ((advance P)^[y]) c' := by
  rw [Nat.add_comm,Function.iterate_add_apply]
  exact congrArg ((advance P)^[y]) h

theorem tail_run (n a q k r : Nat) (saved output count : List Bool)
    (hk : k+r=n) :
    ∃ t ≤ tailCost n a q saved output count k r,
      ((advance (AtLeastLoopCallback.program a q))^[t])
        (checking n a q k r saved output count) =
        finished n a q saved output count := by
  induction r generalizing k with
  | zero =>
      have hkn : k=n := by omega
      subst k
      refine ⟨1,by simp [tailCost],?_⟩
      simpa only [checking,finished,Function.iterate_one] using
        (PrefixLoopMachine.check_done
          (AtLeastLoopCallback.callback a q).program
          (AtLeastLoopCallback.callback a q).start
          (AtLeastLoopCallback.callback a q).initial
          n n (savedAt n a q saved n) output (countAt a count n))
  | succ r ih =>
      have hlt : k<n := by omega
      have hnext : k+1+r=n := by omega
      let S := savedAt n a q saved k
      let C := countAt a count k
      let rest := List.replicate r true
      let v : Fin n := ⟨k,hlt⟩
      have hcheck :
          ((advance (AtLeastLoopCallback.program a q))^[1])
            (checking n a q k (r+1) saved output count) =
            ⟨some (.inl (AtLeastLoopCallback.callback a q).start),
              ((AtLeastLoopCallback.callback a q).initial,none),
              PrefixLoopMachine.blank n k S output C rest⟩ := by
        simpa only [checking,S,C,rest,List.replicate_succ,
          Function.iterate_one,AtLeastLoopCallback.program] using
          (PrefixLoopMachine.check_more
            (AtLeastLoopCallback.callback a q).program
            (AtLeastLoopCallback.callback a q).start
            (AtLeastLoopCallback.callback a q).initial
            n k S output C rest)
      obtain ⟨u,hu,hcallback⟩ := AtLeastLoopCallback.run (a := a) (q := q)
        v S output C rest
      have hcost : callCost n a q saved output count k =
          AtLeastClock.cost (a := a) (q := q) v S output C := by
        simp [callCost,hlt,v,S,C]
      have hnextSaved : savedAt n a q saved (k+1) = word n a q k ++ S := rfl
      have hchain : word n a q k =
          (clauseFields (chain (SourceGenericPrefix.base n a q v.val)
            (SourceGenericPrefix.atLeastPayload (a := a) v))).reverse := by
        exact word_of_lt n a q k hlt
      have hincrement :
          ((advance (AtLeastLoopCallback.program a q))^[1])
            ⟨some (.inr .increment),
              ((AtLeastLoopCallback.callback a q).initial,none),
              PrefixLoopMachine.blank n k (word n a q k ++ S)
                output (List.replicate (3*a+2) true ++ C) rest⟩ =
            checking n a q (k+1) r saved output count := by
        simpa only [checking,AtLeastLoopCallback.program,Function.iterate_one,
          hnextSaved,countAt_next,S,C,rest] using
          (PrefixLoopMachine.increment_step
            (AtLeastLoopCallback.callback a q).program
            (AtLeastLoopCallback.callback a q).start
            (AtLeastLoopCallback.callback a q).initial
            n k (word n a q k ++ S) output
            (List.replicate (3*a+2) true ++ C) rest)
      obtain ⟨z,hz,htail⟩ := ih (k+1) hnext
      have hcallback' :
          ((advance (AtLeastLoopCallback.program a q))^[u])
            ⟨some (.inl (AtLeastLoopCallback.callback a q).start),
              ((AtLeastLoopCallback.callback a q).initial,none),
              PrefixLoopMachine.blank n k S output C rest⟩ =
            ⟨some (.inr .increment),
              ((AtLeastLoopCallback.callback a q).initial,none),
              PrefixLoopMachine.blank n k (word n a q k ++ S)
                output (List.replicate (3*a+2) true ++ C) rest⟩ := by
        simpa only [v,Fin.val_mk,hchain] using hcallback
      have hfirst := run_add (AtLeastLoopCallback.program a q) hcheck u
      rw [hcallback'] at hfirst
      have hsecond := run_add (AtLeastLoopCallback.program a q) hfirst 1
      rw [hincrement] at hsecond
      have htotal := run_add (AtLeastLoopCallback.program a q) hsecond z
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
    ∃ t ≤ 2*n+2+tailCost n a q saved output count 0 n,
      ((advance (AtLeastLoopCallback.program a q))^[t])
        (⟨some (.inr .copyScan),
          ((AtLeastLoopCallback.callback a q).initial,none),
          PrefixLoopMachine.blank n 0 saved output count []⟩ :
          PrefixLoopMachine.Config _ _) =
        ⟨none,((AtLeastLoopCallback.callback a q).initial,none),
          PrefixLoopMachine.blank n n
            ((prefixFields n a q n).reverse ++ saved)
            output (List.replicate ((3*a+2)*n) true ++ count) []⟩ := by
  have hcopy := PrefixLoopMachine.copy_prep
    (AtLeastLoopCallback.callback a q).program
    (AtLeastLoopCallback.callback a q).start
    (AtLeastLoopCallback.callback a q).initial n saved output count
  obtain ⟨u,hu,htail⟩ := tail_run n a q 0 n saved output count (by omega)
  have hcombo := run_add (AtLeastLoopCallback.program a q) hcopy u
  change ((advance (AtLeastLoopCallback.program a q))^[2*n+2+u])
    (⟨some (.inr .copyScan),
      ((AtLeastLoopCallback.callback a q).initial,none),
      PrefixLoopMachine.blank n 0 saved output count []⟩ :
      PrefixLoopMachine.Config _ _) =
    ((advance (AtLeastLoopCallback.program a q))^[u])
      (checking n a q 0 n saved output count) at hcombo
  rw [htail] at hcombo
  refine ⟨2*n+2+u,by omega,?_⟩
  simpa only [finished,countAt,cfgOf,savedAt,savedAt_eq_prefix,
    List.replicate_zero,List.nil_append] using hcombo

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.AtLeastLoop
