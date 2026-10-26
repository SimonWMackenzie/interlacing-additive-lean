import EthInapproximability.CurrentPaper.SourceClausePrefixLoopCallback

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopIteration

open Turing BitMachineEncoding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

def word (n q k : ℕ) : List Bool :=
  if h : k < n then
    (clauseFields (chain (base n q (atLeastOrdinal (⟨k, h⟩ : Fin n)))
      (atLeastPayload (⟨k, h⟩ : Fin n)))).reverse
  else []

def savedAt (n q : ℕ) (saved : List Bool) : ℕ → List Bool
  | 0 => saved
  | k + 1 => word n q k ++ savedAt n q saved k

def countAt (count : List Bool) (k : ℕ) : List Bool :=
  List.replicate (8 * k) true ++ count

theorem word_of_lt (n q k : ℕ) (h : k < n) :
    word n q k =
      (clauseFields (chain (base n q (atLeastOrdinal (⟨k, h⟩ : Fin n)))
        (atLeastPayload (⟨k, h⟩ : Fin n)))).reverse := by
  simp [word, h]

theorem countAt_next (count : List Bool) (k : ℕ) :
    countAt count (k + 1) = List.replicate 8 true ++ countAt count k := by
  unfold countAt
  rw [show 8 * (k + 1) = 8 + 8 * k by omega,
    List.replicate_add, List.append_assoc]

noncomputable def callCost (n q : ℕ) (saved output count : List Bool)
    (k : ℕ) : ℕ :=
  if h : k < n then
    PrefixFullCallback.cost (q := q) (⟨k, h⟩ : Fin n)
      (savedAt n q saved k) output (countAt count k)
  else 0

noncomputable def tailCost (n q : ℕ) (saved output count : List Bool)
    (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 + callCost n q saved output count k +
      tailCost n q saved output count (k + 1) r

private def cfgOf {L V : Type*}
    (_ : L → TM2.Stmt (fun _ : PrefixLoopMachine.CoreStack => Bool) L V)
    (c : PrefixLoopMachine.Config L V) : PrefixLoopMachine.Config L V := c

noncomputable def checking (n q k r : ℕ) (saved output count : List Bool) :=
  cfgOf (PrefixFullCallback.program q)
  ⟨some (.inr .check), (PrefixLoopCallback.initial, none),
    PrefixLoopMachine.blank n k (savedAt n q saved k) output
      (countAt count k) (List.replicate r true)⟩

noncomputable def finished (n q : ℕ) (saved output count : List Bool) :=
  cfgOf (PrefixFullCallback.program q)
  ⟨none, (PrefixLoopCallback.initial, none),
    PrefixLoopMachine.blank n n (savedAt n q saved n) output
      (countAt count n) []⟩

private theorem run_add {L V : Type*}
    (P : L → TM2.Stmt (fun _ : PrefixLoopMachine.Stack => Bool) L V)
    {c c' : TM2.Cfg (fun _ : PrefixLoopMachine.Stack => Bool) L V}
    {a : ℕ} (h : ((advance P)^[a]) c = c') (b : ℕ) :
    ((advance P)^[a + b]) c = ((advance P)^[b]) c' := by
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact congrArg ((advance P)^[b]) h

theorem tail_run (n q k r : ℕ) (saved output count : List Bool)
    (hk : k + r = n) :
    ∃ t ≤ tailCost n q saved output count k r,
      ((advance (PrefixLoopCallback.program q))^[t])
        (checking n q k r saved output count) =
        finished n q saved output count := by
  induction r generalizing k with
  | zero =>
    have hkn : k = n := by omega
    subst k
    refine ⟨1, by simp [tailCost], ?_⟩
    simpa only [checking, finished, Function.iterate_one] using
      (PrefixLoopMachine.check_done (PrefixFullCallback.program q)
        (PrefixLoopCallback.start q) PrefixLoopCallback.initial
        n n (savedAt n q saved n) output (countAt count n))
  | succ r ih =>
    have hlt : k < n := by omega
    have hnext : k + 1 + r = n := by omega
    let S := savedAt n q saved k
    let C := countAt count k
    let rest := List.replicate r true
    let v : Fin n := ⟨k, hlt⟩
    have hcheck :
        ((advance (PrefixLoopCallback.program q))^[1])
          (checking n q k (r + 1) saved output count) =
          ⟨some (.inl (PrefixLoopCallback.start q)),
            (PrefixLoopCallback.initial, none),
            PrefixLoopMachine.blank n k S output C rest⟩ := by
      simpa only [checking, S, C, rest, List.replicate_succ,
        Function.iterate_one, PrefixLoopCallback.program] using
        (PrefixLoopMachine.check_more (PrefixFullCallback.program q)
          (PrefixLoopCallback.start q) PrefixLoopCallback.initial
          n k S output C rest)
    obtain ⟨a, ha, hcallback⟩ := PrefixLoopCallback.run (q := q)
      v S output C rest
    have hcost : callCost n q saved output count k =
        PrefixFullCallback.cost (q := q) v S output C := by
      simp [callCost, hlt, v, S, C]
    have hnextSaved : savedAt n q saved (k + 1) =
        word n q k ++ S := rfl
    have hchain : word n q k =
        (clauseFields (chain (base n q (atLeastOrdinal v))
          (atLeastPayload v))).reverse := by
      exact word_of_lt n q k hlt
    have hincrement :
        ((advance (PrefixLoopCallback.program q))^[1])
          ⟨some (.inr .increment), (PrefixLoopCallback.initial, none),
            PrefixLoopMachine.blank n k (word n q k ++ S)
              output (List.replicate 8 true ++ C) rest⟩ =
        checking n q (k + 1) r saved output count := by
      simpa only [checking, PrefixLoopCallback.program,
        Function.iterate_one, hnextSaved, countAt_next,
        S, C, rest] using
        (PrefixLoopMachine.increment_step (PrefixFullCallback.program q)
          (PrefixLoopCallback.start q) PrefixLoopCallback.initial
          n k (word n q k ++ S) output
          (List.replicate 8 true ++ C) rest)
    obtain ⟨b, hb, htail⟩ := ih (k + 1) hnext
    have hcallback' :
        ((advance (PrefixLoopCallback.program q))^[a])
          ⟨some (.inl (PrefixLoopCallback.start q)),
            (PrefixLoopCallback.initial, none),
            PrefixLoopMachine.blank n k S output C rest⟩ =
          ⟨some (.inr .increment), (PrefixLoopCallback.initial, none),
            PrefixLoopMachine.blank n k (word n q k ++ S)
              output (List.replicate 8 true ++ C) rest⟩ := by
      simpa only [v, Fin.val_mk, hchain] using hcallback
    have hfirst := run_add (PrefixLoopCallback.program q) hcheck a
    rw [hcallback'] at hfirst
    have hsecond := run_add (PrefixLoopCallback.program q) hfirst 1
    rw [hincrement] at hsecond
    have htotal := run_add (PrefixLoopCallback.program q) hsecond b
    rw [htail] at htotal
    refine ⟨1 + a + 1 + b, ?_, ?_⟩
    · simp only [tailCost]
      rw [hcost]
      omega
    · exact htotal

def prefixFields (n q k : ℕ) : List Bool :=
  (List.range k).flatMap (fun j => (word n q j).reverse)

theorem savedAt_eq_prefix (n q k : ℕ) (saved : List Bool) :
    savedAt n q saved k = (prefixFields n q k).reverse ++ saved := by
  induction k with
  | zero => simp [savedAt, prefixFields]
  | succ k ih =>
    rw [savedAt, ih]
    simp only [prefixFields, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.reverse_append, List.reverse_reverse]
    simp [List.append_assoc]

theorem prefixFields_source (n q : ℕ) :
    prefixFields n q n =
      (List.range n).flatMap (fun k =>
        if h : k < n then
          clauseFields (chain (base n q (atLeastOrdinal (⟨k, h⟩ : Fin n)))
            (atLeastPayload (⟨k, h⟩ : Fin n)))
        else []) := by
  simp only [prefixFields]
  congr 1
  funext k
  by_cases h : k < n <;> simp [word, h]

theorem prefixFields_production {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q) :
    prefixFields n q n =
      (List.range n).flatMap (fun k =>
        if h : k < n then
          clauseFields (SourceClauseWriter.slotClauses P hq
            ((formula P hq).clauses[atLeastIndex (m := m) (q := q)
              (⟨k, h⟩ : Fin n)],
              (atLeastIndex (m := m) (q := q)
                (⟨k, h⟩ : Fin n)).val))
        else []) := by
  rw [prefixFields_source]
  congr 1
  funext k
  split_ifs with h
  · rw [atLeast_source_chain P hq (⟨k, h⟩ : Fin n)]
  · rfl

/-- The loop itself adds exactly two charged transitions per callback and
one final zero-fuel test. This lemma deliberately does not assume a callback
clock bound: callers must prove one from the frozen physical callback. -/
theorem tailCost_le_uniform (n q k r B : ℕ)
    (saved output count : List Bool) (hkr : k + r = n)
    (hcost : ∀ j, k ≤ j → j < n →
      callCost n q saved output count j ≤ B) :
    tailCost n q saved output count k r ≤ 1 + r * (B + 2) := by
  induction r generalizing k with
  | zero => simp [tailCost]
  | succ r ih =>
    have hk : k < n := by omega
    have hnext : k + 1 + r = n := by omega
    have hsub : ∀ j, k + 1 ≤ j → j < n →
        callCost n q saved output count j ≤ B := by
      intro j hj hn
      exact hcost j (by omega) hn
    have hc := hcost k (by omega) hk
    have hi := ih (k + 1) hnext hsub
    simp only [tailCost, Nat.succ_mul]
    omega

theorem run (n q : ℕ) (saved output count : List Bool) :
    ∃ t ≤ 2 * n + 2 + tailCost n q saved output count 0 n,
      ((advance (PrefixLoopCallback.program q))^[t])
        (⟨some (.inr .copyScan), (PrefixLoopCallback.initial, none),
          PrefixLoopMachine.blank n 0 saved output count []⟩ :
          PrefixLoopMachine.Config _ _) =
        ⟨none, (PrefixLoopCallback.initial, none),
          PrefixLoopMachine.blank n n
            ((prefixFields n q n).reverse ++ saved)
            output (List.replicate (8 * n) true ++ count) []⟩ := by
  have hcopy := PrefixLoopMachine.copy_prep
    (PrefixFullCallback.program q) (PrefixLoopCallback.start q)
    PrefixLoopCallback.initial n saved output count
  obtain ⟨u, hu, htail⟩ := tail_run n q 0 n saved output count (by omega)
  have hcombo := run_add (PrefixLoopCallback.program q) hcopy u
  change ((advance (PrefixLoopCallback.program q))^[2 * n + 2 + u])
    (⟨some (.inr .copyScan), (PrefixLoopCallback.initial, none),
      PrefixLoopMachine.blank n 0 saved output count []⟩ :
      PrefixLoopMachine.Config _ _) =
    ((advance (PrefixLoopCallback.program q))^[u])
      (checking n q 0 n saved output count) at hcombo
  rw [htail] at hcombo
  · refine ⟨2 * n + 2 + u, by omega, ?_⟩
    simpa only [finished, countAt, cfgOf, savedAt,
      savedAt_eq_prefix, List.replicate_zero, List.nil_append] using hcombo

#print axioms run

#print axioms tail_run

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopIteration
