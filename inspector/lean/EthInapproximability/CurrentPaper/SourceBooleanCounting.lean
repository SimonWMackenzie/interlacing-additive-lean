import EthInapproximability.CurrentPaper.SourceBooleanEncoding

/-!
# Size, validity and bounded occurrences of the Boolean source

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
The bounds count literal positions, not merely distinct variable names.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanEncoding

open EncodedCNF
open scoped BigOperators

variable {n m a q : ℕ}

def width (a q : ℕ) : ℕ := max a (max 2 (q + 1))

def touches (P : CSP n m a q) : ClauseLabel n m a q → Fin n → Prop
  | .inl w, v => w = v
  | .inr (.inl (w, _, _)), v => w = v
  | .inr (.inr (j, _)), v => ∃ t, P.query j t = v

instance (P : CSP n m a q) (z : ClauseLabel n m a q) (v : Fin n) :
    Decidable (touches P z v) := by
  rcases z with w | (⟨w, s, t⟩ | ⟨j, τ⟩) <;> unfold touches <;> infer_instance

theorem clause_support (P : CSP n m a q) (hq : 0 < q)
    (z : ClauseLabel n m a q) (l : Literal) (hl : l ∈ clause P hq z) :
    ∃ v : Fin n, ∃ s : Fin a, l.variable = (bitIndex v s).val ∧ touches P z v := by
  rcases z with v | (⟨v, s, t⟩ | ⟨j, τ⟩)
  · obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨v, s, rfl, rfl⟩
  · by_cases hst : s = t
    · subst t
      simp only [clause, if_true, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact ⟨v, s, rfl, rfl⟩
    · simp only [clause, hst, if_false, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact ⟨v, s, rfl, rfl⟩
      · exact ⟨v, t, rfl, rfl⟩
  · cases hp : P.accept j τ
    · simp only [clause, hp, Bool.false_eq_true, if_false] at hl
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
      exact ⟨P.query j t, τ t, rfl, t, rfl⟩
    · simp only [clause, hp, if_true, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨P.query j ⟨0, hq⟩, τ ⟨0, hq⟩, rfl, ⟨0, hq⟩, rfl⟩
      · obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hl
        exact ⟨P.query j t, τ t, rfl, t, rfl⟩

theorem valid (P : CSP n m a q) (hq : 0 < q) : (formula P hq).Valid := by
  apply SourceClauseEncoding.fromIndexed_valid
  intro i l hl
  obtain ⟨v, s, hs, _⟩ := clause_support P hq _ l hl
  rw [hs]
  exact (bitIndex v s).isLt

theorem clause_width (P : CSP n m a q) (hq : 0 < q)
    (z : ClauseLabel n m a q) : (clause P hq z).length ≤ width a q := by
  rcases z with v | (⟨v, s, t⟩ | ⟨j, τ⟩)
  · simp [clause, width]
  · by_cases hst : s = t <;> simp [clause, hst, width]
  · cases hp : P.accept j τ <;> simp [clause, hp, width]

theorem width_bound (P : CSP n m a q) (hq : 0 < q) :
    (formula P hq).WidthAtMost (width a q) := by
  apply SourceClauseEncoding.fromIndexed_width
  intro i
  exact clause_width P hq _

theorem occurrence_label_sum (P : CSP n m a q) (hq : 0 < q) (x : ℕ) :
    SourceClauseEncoding.occurrenceCount (formula P hq) x =
      ∑ z : ClauseLabel n m a q, ((clause P hq z).map Literal.variable).count x := by
  rw [formula, SourceClauseEncoding.fromIndexed_occurrenceCount]
  symm
  convert (labelEquiv n m a q).sum_comp (fun i =>
    ((clause P hq ((labelEquiv n m a q).symm i)).map Literal.variable).count x) using 1
  simp only [Equiv.symm_apply_apply]

theorem local_occurrence_bound (P : CSP n m a q) (hq : 0 < q)
    (z : ClauseLabel n m a q) (v : Fin n) (s : Fin a) :
    ((clause P hq z).map Literal.variable).count (bitIndex v s).val ≤
      if touches P z v then width a q else 0 := by
  by_cases ht : touches P z v
  · rw [if_pos ht]
    exact List.count_le_length.trans (by simpa using clause_width P hq z)
  · rw [if_neg ht]
    apply Nat.le_zero.mpr
    apply List.count_eq_zero.mpr
    intro hx
    obtain ⟨l, hl, hx⟩ := List.mem_map.mp hx
    obtain ⟨w, t, hidx, hw⟩ := clause_support P hq z l hl
    have heq : bitIndex w t = bitIndex v s := Fin.ext (hidx.symm.trans hx)
    have hpair : (w, t) = (v, s) := finProdFinEquiv.injective heq
    have hwv : w = v := congrArg Prod.fst hpair
    exact ht (hwv ▸ hw)

theorem touching_label_count (P : CSP n m a q) (v : Fin n) :
    ((Finset.univ : Finset (ClauseLabel n m a q)).filter fun z => touches P z v).card =
      1 + a * a + (incident P v).card * a ^ q := by
  classical
  have hb := Finset.sum_boole (R := ℕ) (fun z => touches P z v) Finset.univ
  simp only [Nat.cast_id] at hb
  rw [← hb]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, touches]
  change (∑ w : Fin n, if w = v then 1 else 0) +
    ((∑ w : Fin n, ∑ _s : Fin a, ∑ _t : Fin a, if w = v then 1 else 0) +
      ∑ j : Fin m, ∑ _τ : Fin q → Fin a, if ∃ t, P.query j t = v then 1 else 0) = _
  simp
  have hj : (∑ j : Fin m, if ∃ t, P.query j t = v then a ^ q else 0) =
      (incident P v).card * a ^ q := by
    calc
      _ = (∑ j : Fin m, if ∃ t, P.query j t = v then 1 else 0) * a ^ q := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        split <;> simp_all
      _ = (incident P v).card * a ^ q := by
        have hi := Finset.sum_boole (R := ℕ) (fun j => ∃ t, P.query j t = v) Finset.univ
        simpa only [Nat.cast_id, incident] using congrArg (fun k => k * a ^ q) hi
  rw [hj]
  omega

def occurrenceBound (a q D : ℕ) : ℕ := width a q * (1 + a * a + D * a ^ q)

theorem bounded_occurrence (P : CSP n m a q) (hq : 0 < q)
    (D : ℕ) (hD : BoundedOccurrence P D) :
    SourceClauseEncoding.BoundedOccurrence (formula P hq) (occurrenceBound a q D) := by
  intro x hx
  let p := finProdFinEquiv.symm (⟨x, hx⟩ : Fin (n * a))
  have hp : (bitIndex p.1 p.2).val = x := by
    exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨x, hx⟩ : Fin (n * a)))
  rw [← hp, occurrence_label_sum]
  calc
    (∑ z : ClauseLabel n m a q, ((clause P hq z).map Literal.variable).count
        (bitIndex p.1 p.2).val) ≤ ∑ z : ClauseLabel n m a q,
          if touches P z p.1 then width a q else 0 :=
      Finset.sum_le_sum fun z _ => local_occurrence_bound P hq z p.1 p.2
    _ = width a q * ((Finset.univ : Finset (ClauseLabel n m a q)).filter
        fun z => touches P z p.1).card := by
      have hb := Finset.sum_boole (R := ℕ) (fun z => touches P z p.1) Finset.univ
      simp only [Nat.cast_id] at hb
      rw [← hb]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      split <;> simp_all
    _ = width a q * (1 + a * a + (incident P p.1).card * a ^ q) := by
      rw [touching_label_count]
    _ ≤ occurrenceBound a q D := by
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (hD p.1)) _)

end EthInapproximability.CurrentPaper.SourceBooleanEncoding
