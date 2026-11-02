import EthInapproximability.CurrentPaper.SourceClauseIndexed
import EthInapproximability.CurrentPaper.SourceCNFSemantics

/-!
# Soundness of the literal prefix-OR translation

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, the Boolean
encoding in the source composition. Every false old clause forces a false
new clause in its own occurrence block. No assumption about the auxiliary
bits is made, and equal clauses in different positions remain distinct.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseEncoding

open EncodedCNF
open scoped BigOperators

theorem chain_all_iff (base : ℕ) (c : List Literal) (a : List Bool) :
    ((chain base c).all fun d => d.eval a) = true ↔
      a.getD base false = false ∧
      a.getD (base + c.length) false = true ∧
      ∀ t : Fin c.length,
        a.getD (base + t.val + 1) false =
          (a.getD (base + t.val) false || (c.get t).eval a) := by
  have hneg : (!a.getD base false) = true ↔ a.getD base false = false := by
    cases a.getD base false <;> decide
  simp only [chain, List.all_append, Bool.and_eq_true, List.all_cons,
    List.all_nil, Bool.and_true, unit_eval, negative_eval, positive_eval,
    hneg, List.all_flatMap]
  simp only [List.all_eq_true]
  rw [List.forall_mem_zipIdx']
  constructor
  · rintro ⟨⟨hfirst, hgate⟩, hlast⟩
    refine ⟨hfirst, hlast, fun t => ?_⟩
    apply (orGate_eval (base + t.val) (c.get t) a).mp
    rw [List.all_eq_true]
    exact hgate t.val t.isLt
  · rintro ⟨hfirst, hlast, hgate⟩
    refine ⟨⟨hfirst, fun i hi => ?_⟩, hlast⟩
    exact List.all_eq_true.mp ((orGate_eval (base + i) (c.get ⟨i, hi⟩) a).mpr
      (hgate ⟨i, hi⟩))

/-- The intermediate bits of any satisfying gate chain have their literal
prefix-OR values, starting at the prescribed initial bit. -/
theorem chain_prefix_equation (base : ℕ) (c : List Literal) (a : List Bool)
    (hgate : ∀ t : Fin c.length,
      a.getD (base + t.val + 1) false =
        (a.getD (base + t.val) false || (c.get t).eval a))
    (t : ℕ) (ht : t ≤ c.length) :
    a.getD (base + t) false =
      (a.getD base false || longClauseEval (c.take t) a) := by
  induction t with
  | zero => simp [longClauseEval]
  | succ t ih =>
      have hlt : t < c.length := by omega
      have he := hgate ⟨t, hlt⟩
      rw [show base + (t + 1) = base + t + 1 by omega, he, ih (by omega)]
      simp only [longClauseEval, List.take_succ_eq_append_getElem hlt,
        List.any_append, List.any_cons, List.any_nil, Bool.or_false,
        List.get_eq_getElem, Bool.or_assoc]

/-- Soundness holds for every list assignment, even one whose length does
not cover all fresh variables. Such missing bits retain the total evaluator's
specified default. -/
theorem chain_sound (base : ℕ) (c : List Literal) (a : List Bool)
    (h : ((chain base c).all fun d => d.eval a) = true) :
    longClauseEval c a = true := by
  obtain ⟨hfirst, hlast, hgate⟩ := (chain_all_iff base c a).mp h
  have he := chain_prefix_equation base c a hgate c.length le_rfl
  rw [hfirst, hlast, Bool.false_or, List.take_length] at he
  exact he.symm

/-- A false old clause has a genuinely false generated clause. -/
theorem chain_unsatisfied (base : ℕ) (c : List Literal) (a : List Bool)
    (h : longClauseEval c a = false) :
    ∃ d ∈ chain base c, d.eval a = false := by
  by_contra hn
  push Not at hn
  have hall : ((chain base c).all fun d => d.eval a) = true := by
    rw [List.all_eq_true]
    intro d hd
    cases he : d.eval a
    · exact False.elim (hn d hd he)
    · rfl
  have hs := chain_sound base c a hall
  rw [h] at hs
  contradiction

private theorem countP_eq_sum_map {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]; omega

/-- Cardinalities of indexed false clauses coincide with the list count;
in particular this never quotients syntactically equal occurrences. -/
theorem indexed_filter_card_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    ((Finset.univ : Finset (Fin l.length)).filter fun i => p (l.get i)).card =
      l.countP p := by
  rw [countP_eq_sum_map]
  conv_rhs => rw [← List.ofFn_get l]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem falseClauses_card_eq_countP (f : LongFormula) (a : List Bool) :
    (falseClauses f a).card = f.clauses.countP fun c => !(longClauseEval c a) := by
  have h := indexed_filter_card_eq_countP f.clauses (fun c => !(longClauseEval c a))
  simpa only [falseClauses, Bool.not_eq_true'] using h

theorem translated_falseClauses_card_eq_countP (f : Formula) (a : List Bool) :
    (SourceCNFSemantics.falseClauses f a).card =
      f.clauses.countP fun c => !(c.eval a) := by
  have h := indexed_filter_card_eq_countP f.clauses (fun c => !(c.eval a))
  simpa only [SourceCNFSemantics.falseClauses, Bool.not_eq_true'] using h

private theorem countP_le_flatMap {α β : Type*} (xs : List α)
    (p : α → Bool) (q : β → Bool) (g : α → List β)
    (h : ∀ x ∈ xs, p x = true → 1 ≤ (g x).countP q) :
    xs.countP p ≤ (xs.flatMap g).countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hi := ih (fun y hy => h y (by simp [hy]))
      simp only [List.countP_cons, List.flatMap_cons, List.countP_append]
      cases hp : p x
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · have hx := h x (by simp) hp
        simp only [↓reduceIte]; omega

/-- Each false old clause forces a violation inside its own disjoint list
block, so simultaneous violations are counted without loss. -/
theorem falseClauses_le_translate (K : ℕ) (f : LongFormula) (a : List Bool) :
    (falseClauses f a).card ≤
      (SourceCNFSemantics.falseClauses (translate K f) a).card := by
  rw [falseClauses_card_eq_countP, translated_falseClauses_card_eq_countP]
  change f.clauses.countP (fun c => !(longClauseEval c a)) ≤
    (f.clauses.zipIdx.flatMap fun (c, j) =>
      chain (f.variables + j * (K + 1)) c).countP (fun c => !(c.eval a))
  have h := countP_le_flatMap f.clauses.zipIdx
    (fun x => !(longClauseEval x.1 a)) (fun c => !(c.eval a))
    (fun x => chain (f.variables + x.2 * (K + 1)) x.1) (by
      intro x hx hp
      obtain ⟨d, hd, he⟩ := chain_unsatisfied (f.variables + x.2 * (K + 1)) x.1 a
        (by simpa using hp)
      exact List.one_le_countP_iff.mpr ⟨d, hd, by simp [he]⟩)
  have hm : f.clauses.zipIdx.countP (fun x => !(longClauseEval x.1 a)) =
      f.clauses.countP (fun c => !(longClauseEval c a)) := by
    simpa only [List.zipIdx_map_fst, Function.comp_def] using
      (List.countP_map (l := f.clauses.zipIdx) (f := Prod.fst)
        (p := fun c => !(longClauseEval c a))).symm
  rwa [hm] at h

theorem literal_eval_take (l : Literal) (a : List Bool) (n : ℕ)
    (hl : l.variable < n) : l.eval (a.take n) = l.eval a := by
  simp only [Literal.eval, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hl]

theorem longClauseEval_take (c : List Literal) (a : List Bool) (n : ℕ)
    (hc : ∀ l ∈ c, l.variable < n) :
    longClauseEval c (a.take n) = longClauseEval c a := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
      have hl := literal_eval_take l a n (hc l (by simp))
      have hs := ih (fun d hd => hc d (by simp [hd]))
      simp only [longClauseEval, List.any_cons] at hs ⊢
      rw [hl, hs]

theorem falseClauses_take (f : LongFormula) (hf : f.Valid) (a : List Bool) :
    falseClauses f (a.take f.variables) = falseClauses f a := by
  ext i
  simp only [falseClauses, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [longClauseEval_take _ a f.variables (hf _ (List.get_mem _ _))]

/-- The projected assignment has exactly the old variables; false original
clause positions still inject into false translated clause occurrences. -/
theorem falseClauses_take_le_translate (K : ℕ) (f : LongFormula)
    (hf : f.Valid) (a : List Bool) :
    (falseClauses f (a.take f.variables)).card ≤
      (SourceCNFSemantics.falseClauses (translate K f) a).card := by
  rw [falseClauses_take f hf a]
  exact falseClauses_le_translate K f a

end EthInapproximability.CurrentPaper.SourceClauseEncoding
