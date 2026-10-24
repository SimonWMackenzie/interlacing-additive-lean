import EthInapproximability.CurrentPaper.SourceClauseRowSchedule

/-!
# Fixed finite-control literal positions for one tuple slot

An accepting truth bit selects `q+1` positions: first one positive copy of
query zero, then the `q` negative query positions. A rejecting bit selects
exactly the `q` negatives. Tuple symbols are determined by the fixed ordinal
`k` and finite alphabet/arity; variable vertices still come from the physical
checked row bank. These are instructions, not a precomputed output clause.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowInstruction

open SourceBooleanEncoding SourceClauseRowSchedule EncodedCNF

def accepted {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q)) :
    Fin (q + 1) → Fin q × Fin a × Bool :=
  Fin.cons (⟨0, hq⟩, tuple a q k ⟨0, hq⟩, true)
    (fun t => (t, tuple a q k t, false))

def rejected {a q : ℕ} (k : Fin (a ^ q)) :
    Fin q → Fin q × Fin a × Bool :=
  fun t => (t, tuple a q k t, false)

def literal {a q : ℕ} (query : Fin q → ℕ)
    (i : Fin q × Fin a × Bool) : Literal :=
  ⟨query i.1 * a + i.2.1.val, i.2.2⟩

theorem accepted_exact {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) (query : Fin q → ℕ) :
    List.ofFn (fun p => literal query (accepted hq k p)) =
      tupleClause hq k query true := by
  simp [accepted, literal, tupleClause, tupleLiteral,
    List.ofFn_cons, SourceBooleanEncoding.positive,
    SourceBooleanEncoding.negative]

theorem rejected_exact {a q : ℕ}
    (hq : 0 < q) (k : Fin (a ^ q)) (query : Fin q → ℕ) :
    List.ofFn (fun p => literal query (rejected k p)) =
      tupleClause hq k query false := by
  simp [rejected, literal, tupleClause, tupleLiteral,
    SourceBooleanEncoding.negative]

theorem accepted_length {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) (query : Fin q → ℕ) :
    (tupleClause hq k query true).length = q + 1 := by
  rw [← accepted_exact hq k query]
  simp

theorem rejected_length {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) (query : Fin q → ℕ) :
    (tupleClause hq k query false).length = q := by
  rw [← rejected_exact hq k query]
  simp

end EthInapproximability.CurrentPaper.SourceClauseRowInstruction
