import EthInapproximability.CurrentPaper.SourceClauseDefinitions

/-!
# Indexed-clause interfaces for the Boolean source encoding

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
Clause occurrences keep their finite index even when their contents coincide.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseEncoding

open EncodedCNF
open scoped BigOperators

theorem fromIndexed_valid (nvars n : ℕ) (clause : Fin n → List Literal)
    (h : ∀ i, ∀ l ∈ clause i, l.variable < nvars) :
    (fromIndexed nvars n clause).Valid := by
  intro c hc l hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact h i l hl

theorem fromIndexed_width (nvars n K : ℕ) (clause : Fin n → List Literal)
    (h : ∀ i, (clause i).length ≤ K) :
    (fromIndexed nvars n clause).WidthAtMost K := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact h i

theorem fromIndexed_false_card (nvars n : ℕ) (clause : Fin n → List Literal)
    (assignment : List Bool) :
    (falseClauses (fromIndexed nvars n clause) assignment).card =
      ((Finset.univ : Finset (Fin n)).filter fun i => longClauseEval (clause i) assignment = false).card := by
  classical
  let e : Fin (fromIndexed nvars n clause).clauses.length ≃ Fin n :=
    finCongr (fromIndexed_length nvars n clause)
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simp only [falseClauses, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa only [fromIndexed, List.get_eq_getElem, List.getElem_ofFn] using hi
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simp only [falseClauses, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa only [fromIndexed, List.get_eq_getElem, List.getElem_ofFn] using hj

theorem fromIndexed_occurrenceCount (nvars n : ℕ) (clause : Fin n → List Literal) (v : ℕ) :
    occurrenceCount (fromIndexed nvars n clause) v =
      ∑ i : Fin n, ((clause i).map Literal.variable).count v := by
  simp only [occurrenceCount, fromIndexed, List.map_flatten, List.count_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

end EthInapproximability.CurrentPaper.SourceClauseEncoding
