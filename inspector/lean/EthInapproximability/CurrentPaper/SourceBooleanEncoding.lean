import EthInapproximability.CurrentPaper.SourceBooleanDefinitions
import EthInapproximability.CurrentPaper.SourceClauseIndexed

/-!
# Correctness and gap preservation of the Boolean alphabet encoding

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
Invalid Boolean blocks are charged to their own violated exact-one checks;
only incident constraints can be damaged by rounding such a block.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanEncoding

open EncodedCNF
open scoped BigOperators

variable {n m a q : ℕ}

@[simp] theorem positive_eval (v : ℕ) (A : List Bool) :
    (positive v).eval A = A.getD v false := rfl

@[simp] theorem negative_eval (v : ℕ) (A : List Bool) :
    (negative v).eval A = !(A.getD v false) := rfl

@[simp] theorem encodedBits_length (σ : Fin n → Fin a) :
    (encodedBits σ).length = n * a := by simp [encodedBits]

@[simp] theorem readBit_encoded (σ : Fin n → Fin a) (v : Fin n) (s : Fin a) :
    readBit (encodedBits σ) v s = decide (s = σ v) := by
  unfold readBit encodedBits
  rw [List.getD, List.getElem?_eq_getElem (by simpa using (bitIndex v s).isLt)]
  simp only [Option.getD_some, List.getElem_ofFn]
  change decide ((finProdFinEquiv.symm (bitIndex v s)).2 =
    σ (finProdFinEquiv.symm (bitIndex v s)).1) = _
  simp only [bitIndex, Equiv.symm_apply_apply]

theorem atLeast_eval (P : CSP n m a q) (hq : 0 < q) (A : List Bool) (v : Fin n) :
    (clause P hq (.inl v)).any (fun l => l.eval A) = true ↔
      ∃ s : Fin a, readBit A v s = true := by
  simp [clause, List.any_eq_true, List.mem_ofFn, readBit]

theorem pair_eval (P : CSP n m a q) (hq : 0 < q) (A : List Bool)
    (v : Fin n) (s t : Fin a) (hst : s ≠ t) :
    (clause P hq (.inr (.inl (v, s, t)))).any (fun l => l.eval A) = false ↔
      readBit A v s = true ∧ readBit A v t = true := by
  simp [clause, hst, readBit]

theorem accepted_clause (P : CSP n m a q) (hq : 0 < q) (A : List Bool)
    (j : Fin m) (τ : Fin q → Fin a) (h : P.accept j τ = true) :
    (clause P hq (.inr (.inr (j, τ)))).any (fun l => l.eval A) = true := by
  simp only [clause, h, if_true, List.any_cons]
  by_cases hbit : readBit A (P.query j ⟨0, hq⟩) (τ ⟨0, hq⟩) = true
  · have hb := hbit
    simp only [readBit] at hb
    simp only [positive_eval, hb, Bool.true_or]
  · apply Bool.or_eq_true_iff.mpr
    right
    apply List.any_eq_true.mpr
    refine ⟨negative (bitIndex (P.query j ⟨0, hq⟩) (τ ⟨0, hq⟩)), ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨⟨0, hq⟩, rfl⟩
    · change Bool.not (readBit A (P.query j ⟨0, hq⟩) (τ ⟨0, hq⟩)) = true
      simpa using hbit

theorem forbidden_clause (P : CSP n m a q) (hq : 0 < q) (A : List Bool)
    (j : Fin m) (τ : Fin q → Fin a) (h : P.accept j τ = false) :
    (clause P hq (.inr (.inr (j, τ)))).any (fun l => l.eval A) = false ↔
      ∀ t, readBit A (P.query j t) (τ t) = true := by
  simp [clause, h, List.any_eq_false, List.mem_ofFn, readBit]

/-- A bad block has a violated clause bearing that same vertex label. -/
theorem badBlock_witness (P : CSP n m a q) (hq : 0 < q) (A : List Bool)
    (v : Fin n) (hv : ¬ GoodBlock (a := a) A v) :
    (Sum.inl v ∈ failedLabels P hq A) ∨
      ∃ s t : Fin a, Sum.inr (Sum.inl (v, s, t)) ∈ failedLabels P hq A := by
  by_cases hex : ∃ s : Fin a, readBit A v s = true
  · obtain ⟨s, hs⟩ := hex
    have htwo : ∃ t : Fin a, readBit A v t = true ∧ t ≠ s := by
      by_contra hn
      apply hv
      refine ⟨s, hs, ?_⟩
      intro t ht
      by_contra hts
      exact hn ⟨t, ht, hts⟩
    obtain ⟨t, ht, hts⟩ := htwo
    right
    refine ⟨s, t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact (pair_eval P hq A v s t (Ne.symm hts)).mpr ⟨hs, ht⟩
  · left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Bool.eq_false_iff.mpr ?_⟩
    exact fun h => hex ((atLeast_eval P hq A v).mp h)

noncomputable def round (ha : 0 < a) (A : List Bool) (v : Fin n) : Fin a :=
  if h : ∃ s : Fin a, readBit A v s = true then Classical.choose h else ⟨0, ha⟩

theorem round_good (ha : 0 < a) (A : List Bool) (v : Fin n)
    (hv : GoodBlock (a := a) A v) : readBit A v (round ha A v) = true := by
  have hex : ∃ s : Fin a, readBit A v s = true := by obtain ⟨s, hs, _⟩ := hv; exact ⟨s, hs⟩
  simp only [round, dif_pos hex]
  exact Classical.choose_spec hex

def formula (P : CSP n m a q) (hq : 0 < q) : SourceClauseEncoding.LongFormula :=
  SourceClauseEncoding.fromIndexed (n * a) (clauseCount n m a q)
    (fun i => clause P hq ((labelEquiv n m a q).symm i))

theorem failed_card (P : CSP n m a q) (hq : 0 < q) (A : List Bool) :
    (SourceClauseEncoding.falseClauses (formula P hq) A).card =
      (failedLabels P hq A).card := by
  rw [formula, SourceClauseEncoding.fromIndexed_false_card]
  apply Finset.card_equiv (labelEquiv n m a q).symm
  intro i
  simp [failedLabels, SourceClauseEncoding.longClauseEval]

theorem clause_complete (P : CSP n m a q) (hq : 0 < q)
    (σ : Fin n → Fin a) (hσ : ∀ j, evalConstraint P σ j = true)
    (z : ClauseLabel n m a q) :
    (clause P hq z).any (fun l => l.eval (encodedBits σ)) = true := by
  rcases z with v | (⟨v, s, t⟩ | ⟨j, τ⟩)
  · exact (atLeast_eval P hq _ v).mpr ⟨σ v, by simp⟩
  · by_cases hst : s = t
    · subst t
      simp [clause]
    · by_contra hnot
      have hf := Bool.eq_false_iff.mpr hnot
      obtain ⟨hs, ht⟩ := (pair_eval P hq _ v s t hst).mp hf
      simp only [readBit_encoded, decide_eq_true_eq] at hs ht
      exact hst (hs.trans ht.symm)
  · cases haccept : P.accept j τ
    · by_contra hnot
      have hf := Bool.eq_false_iff.mpr hnot
      have hbits := (forbidden_clause P hq _ j τ haccept).mp hf
      have ht : τ = fun t => σ (P.query j t) := by
        funext t
        simpa using hbits t
      have hp := hσ j
      simp only [evalConstraint, ← ht, haccept] at hp
      contradiction
    · exact accepted_clause P hq _ j τ haccept

theorem complete (P : CSP n m a q) (hq : 0 < q) (h : Satisfiable P) :
    (formula P hq).Satisfiable := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨encodedBits σ, encodedBits_length σ, ?_⟩
  simp only [SourceClauseEncoding.LongFormula.eval, formula,
    SourceClauseEncoding.fromIndexed, List.all_eq_true, List.mem_ofFn]
  rintro c ⟨i, rfl⟩
  exact clause_complete P hq σ hσ _

theorem badBlocks_card (P : CSP n m a q) (hq : 0 < q) (A : List Bool) :
    (badBlocks (n := n) (a := a) A).card ≤ (failedLabels P hq A).card := by
  classical
  let owner : ClauseLabel n m a q → Option (Fin n)
    | .inl v => some v
    | .inr (.inl (v, _, _)) => some v
    | .inr (.inr _) => none
  have hex (v : ↥(badBlocks (n := n) (a := a) A)) :
      ∃ z : ↥(failedLabels P hq A), owner z.val = some v.val := by
    have hv := (Finset.mem_filter.mp v.property).2
    rcases badBlock_witness P hq A v.val hv with h | ⟨s, t, h⟩
    · exact ⟨⟨.inl v.val, h⟩, rfl⟩
    · exact ⟨⟨.inr (.inl (v.val, s, t)), h⟩, rfl⟩
  let f : ↥(badBlocks (n := n) (a := a) A) → ↥(failedLabels P hq A) :=
    fun v => Classical.choose (hex v)
  apply Finset.card_le_card_of_injective (f := f)
  intro u v huv
  apply Subtype.ext
  apply Option.some.inj
  calc
    some u.val = owner (f u).val := (Classical.choose_spec (hex u)).symm
    _ = owner (f v).val := congrArg (fun z => owner z.val) huv
    _ = some v.val := Classical.choose_spec (hex v)

def damaged (P : CSP n m a q) (A : List Bool) : Finset (Fin m) :=
  (badBlocks (n := n) (a := a) A).biUnion (incident P)

theorem damaged_card (P : CSP n m a q) (A : List Bool) (D : ℕ)
    (hD : BoundedOccurrence P D) :
    (damaged P A).card ≤ D * (badBlocks (n := n) (a := a) A).card := by
  calc
    (damaged P A).card ≤ ∑ v ∈ badBlocks (n := n) (a := a) A, (incident P v).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ badBlocks (n := n) (a := a) A, D :=
      Finset.sum_le_sum fun v _ => hD v
    _ = D * (badBlocks (n := n) (a := a) A).card := by simp [Nat.mul_comm]

theorem not_damaged_good (P : CSP n m a q) (A : List Bool) (j : Fin m)
    (hj : j ∉ damaged P A) (t : Fin q) : GoodBlock (a := a) A (P.query j t) := by
  by_contra hb
  apply hj
  apply Finset.mem_biUnion.mpr
  refine ⟨P.query j t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, rfl⟩

theorem clean_failure_label (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (A : List Bool) (j : Fin m) (hj : j ∈ falseConstraints P (round ha A))
    (hd : j ∉ damaged P A) :
    Sum.inr (Sum.inr (j, fun t => round ha A (P.query j t))) ∈ failedLabels P hq A := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (forbidden_clause P hq A j _ ((Finset.mem_filter.mp hj).2)).mpr
  intro t
  exact round_good ha A _ (not_damaged_good P A j hd t)

/-- Every failed rounded constraint is charged either to an incident bad
block, or directly to its own failed forbidden-pattern clause. -/
theorem rounding_bound (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (A : List Bool) (D : ℕ) (hD : BoundedOccurrence P D) :
    (falseConstraints P (round ha A)).card ≤ (D + 1) * (failedLabels P hq A).card := by
  classical
  let clean := (falseConstraints P (round ha A)).filter fun j => j ∉ damaged P A
  have hclean : clean.card ≤ (failedLabels P hq A).card := by
    apply Finset.card_le_card_of_injOn
      (fun j => Sum.inr (Sum.inr (j, fun t => round ha A (P.query j t))))
    · intro j hj
      exact clean_failure_label P ha hq A j (Finset.mem_filter.mp hj).1
        (Finset.mem_filter.mp hj).2
    · intro i _ j _ hij
      exact congrArg Prod.fst (Sum.inr.inj (Sum.inr.inj hij))
  have hcover : falseConstraints P (round ha A) ⊆ damaged P A ∪ clean := by
    intro j hj
    by_cases hd : j ∈ damaged P A
    · exact Finset.mem_union_left _ hd
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj, hd⟩)
  calc
    (falseConstraints P (round ha A)).card ≤ (damaged P A ∪ clean).card :=
      Finset.card_le_card hcover
    _ ≤ (damaged P A).card + clean.card := Finset.card_union_le _ _
    _ ≤ D * (badBlocks (n := n) (a := a) A).card + (failedLabels P hq A).card :=
      Nat.add_le_add (damaged_card P A D hD) hclean
    _ ≤ D * (failedLabels P hq A).card + (failedLabels P hq A).card :=
      Nat.add_le_add_right (Nat.mul_le_mul_left D (badBlocks_card P hq A)) _
    _ = (D + 1) * (failedLabels P hq A).card := by ring

theorem absolute_gap (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (D : ℕ) (ε : ℚ) (hD : BoundedOccurrence P D) (hgap : Gap P ε)
    (A : List Bool) :
    ε * m ≤ (D + 1 : ℚ) * (SourceClauseEncoding.falseClauses (formula P hq) A).card := by
  rw [failed_card]
  exact (hgap (round ha A)).trans (by exact_mod_cast rounding_bound P ha hq A D hD)

def sizeFactor (a q : ℕ) : ℕ := q * (1 + a * a) + a ^ q

@[simp] theorem formula_variables (P : CSP n m a q) (hq : 0 < q) :
    (formula P hq).variables = n * a := rfl

@[simp] theorem formula_length (P : CSP n m a q) (hq : 0 < q) :
    (formula P hq).clauses.length = clauseCount n m a q := by
  simp [formula, SourceClauseEncoding.fromIndexed]

theorem sizeFactor_pos (ha : 0 < a) : 0 < sizeFactor a q := by
  have hpow : 0 < a ^ q := pow_pos ha q
  unfold sizeFactor
  omega

theorem variables_le_queries (P : CSP n m a q)
    (hused : ∀ v : Fin n, ∃ j : Fin m, ∃ t : Fin q, P.query j t = v) : n ≤ q * m := by
  have hs : Function.Surjective (fun p : Fin m × Fin q => P.query p.1 p.2) := by
    intro v
    obtain ⟨j, t, h⟩ := hused v
    exact ⟨(j, t), h⟩
  have hc := Fintype.card_le_of_surjective _ hs
  simpa only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm] using hc

theorem formula_length_bound (P : CSP n m a q) (hq : 0 < q) (hn : n ≤ q * m) :
    (formula P hq).clauses.length ≤ sizeFactor a q * m := by
  rw [formula_length]
  unfold clauseCount sizeFactor
  calc
    n + (n * (a * a) + m * a ^ q) = n * (1 + a * a) + m * a ^ q := by ring
    _ ≤ (q * m) * (1 + a * a) + m * a ^ q :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _
    _ = (q * (1 + a * a) + a ^ q) * m := by ring

/-- The loss depends only on the fixed alphabet, query width, and degree.
The mild variable bound is supplied by discarding unused PCP variables. -/
theorem gap (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (D : ℕ) (ε : ℚ) (hε : 0 ≤ ε) (hn : n ≤ q * m)
    (hD : BoundedOccurrence P D) (hgap : Gap P ε) :
    SourceClauseEncoding.FormulaGap (formula P hq)
      (ε / ((D + 1 : ℚ) * sizeFactor a q)) := by
  intro A _hA
  have hs : (0 : ℚ) < sizeFactor a q := by exact_mod_cast sizeFactor_pos (q := q) ha
  have hd : (0 : ℚ) < (D + 1 : ℚ) * sizeFactor a q := mul_pos (by positivity) hs
  have hc : ((formula P hq).clauses.length : ℚ) ≤ (sizeFactor a q : ℚ) * m := by
    exact_mod_cast formula_length_bound P hq hn
  have habs := absolute_gap P ha hq D ε hD hgap A
  calc
    ε / ((D + 1 : ℚ) * sizeFactor a q) * (formula P hq).clauses.length =
        (ε * (formula P hq).clauses.length) / ((D + 1 : ℚ) * sizeFactor a q) := by ring
    _ ≤ (SourceClauseEncoding.falseClauses (formula P hq) A).card := by
      apply (div_le_iff₀ hd).mpr
      calc
        ε * (formula P hq).clauses.length ≤ ε * ((sizeFactor a q : ℚ) * m) :=
          mul_le_mul_of_nonneg_left hc hε
        _ = (sizeFactor a q : ℚ) * (ε * m) := by ring
        _ ≤ (sizeFactor a q : ℚ) * ((D + 1 : ℚ) *
            (SourceClauseEncoding.falseClauses (formula P hq) A).card) :=
          mul_le_mul_of_nonneg_left habs hs.le
        _ = (SourceClauseEncoding.falseClauses (formula P hq) A).card *
            ((D + 1 : ℚ) * sizeFactor a q) := by ring

end EthInapproximability.CurrentPaper.SourceBooleanEncoding
