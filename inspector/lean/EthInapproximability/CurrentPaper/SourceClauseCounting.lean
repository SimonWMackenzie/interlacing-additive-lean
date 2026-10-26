import EthInapproximability.CurrentPaper.SourceClauseDefinitions
import EthInapproximability.CurrentPaper.SourceCNFSemantics

/-!
# Size, validity and occurrence counts for the literal clause translation

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`, the Boolean
encoding between the finite-alphabet constraints and bounded-degree
three-colouring. These are structural properties of the actual prefix-OR
translation; no satisfiability or gap conclusion is assumed here.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseEncoding

open EncodedCNF

theorem gates_length (base : ℕ) (xs : List (Literal × ℕ)) :
    (xs.flatMap fun (l, t) => orGate (base + t) l).length = 3 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, orGate_length,
      List.length_cons, ih]; omega

@[simp] theorem chain_length (base : ℕ) (c : List Literal) :
    (chain base c).length = 3 * c.length + 2 := by
  simp only [chain, List.length_append, List.length_singleton, gates_length,
    List.length_zipIdx]
  omega

@[simp] theorem translate_variables (K : ℕ) (f : LongFormula) :
    (translate K f).variables = f.variables + (K + 1) * f.clauses.length := rfl

theorem flatMap_length_le {α β : Type*} (xs : List α) (g : α → List β) (B : ℕ)
    (h : ∀ x ∈ xs, (g x).length ≤ B) :
    (xs.flatMap g).length ≤ B * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add,
        Nat.mul_one]
      omega

theorem zipIdx_mem {α : Type*} {xs : List α} {x : α} {j : ℕ}
    (h : (x, j) ∈ xs.zipIdx) : x ∈ xs ∧ j < xs.length := by
  have hh := List.mem_zipIdx h
  have hj : j < xs.length := by omega
  have he : x = xs[j] := by simpa only [Nat.sub_zero] using hh.2.2
  exact ⟨he ▸ List.getElem_mem hj, hj⟩

theorem translate_length_le (K : ℕ) (f : LongFormula) (hK : f.WidthAtMost K) :
    (translate K f).clauses.length ≤ (3 * K + 2) * f.clauses.length := by
  have h := flatMap_length_le f.clauses.zipIdx
    (fun (c, j) => chain (f.variables + j * (K + 1)) c) (3 * K + 2) (by
      rintro ⟨c, j⟩ hc
      rw [chain_length]
      have := hK c (zipIdx_mem hc).1
      omega)
  simpa only [translate, List.length_zipIdx] using h

theorem flatMap_length_lower {α β : Type*} (xs : List α) (g : α → List β) (B : ℕ)
    (h : ∀ x ∈ xs, B ≤ (g x).length) :
    B * xs.length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add,
        Nat.mul_one]
      omega

theorem translate_length_lower (K : ℕ) (f : LongFormula) :
    2 * f.clauses.length ≤ (translate K f).clauses.length := by
  have h := flatMap_length_lower f.clauses.zipIdx
    (fun (c, j) => chain (f.variables + j * (K + 1)) c) 2 (by
      rintro ⟨c, j⟩ _
      rw [chain_length]
      omega)
  simpa only [translate, List.length_zipIdx] using h

theorem unit_valid (l : Literal) (n : ℕ) (h : l.variable < n) :
    (unit l).Valid n := ⟨h, h, h⟩

theorem orGate_valid (p n : ℕ) (l : Literal)
    (hp : p + 1 < n) (hl : l.variable < n) :
    ∀ d ∈ orGate p l, d.Valid n := by
  intro d hd
  simp only [orGate, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;>
    simp only [Clause.Valid, negate, positive, negative] <;> omega

theorem chain_valid (base n : ℕ) (c : List Literal)
    (hbase : base + c.length < n) (hc : ∀ l ∈ c, l.variable < n) :
    ∀ d ∈ chain base c, d.Valid n := by
  intro d hd
  simp only [chain, List.mem_append, List.mem_singleton, List.mem_flatMap] at hd
  rcases hd with (rfl | ⟨⟨l, t⟩, hlt, hd⟩) | rfl
  · exact unit_valid _ _ (by change base < n; omega)
  · have hm := zipIdx_mem hlt
    exact orGate_valid (base + t) n l (by omega) (hc l hm.1) d hd
  · exact unit_valid _ _ hbase

theorem translate_valid (K : ℕ) (f : LongFormula)
    (hf : f.Valid) (hK : f.WidthAtMost K) : (translate K f).Valid := by
  intro d hd
  obtain ⟨⟨c, j⟩, hcj, hd⟩ := List.mem_flatMap.mp hd
  have hm := zipIdx_mem hcj
  have hlen := hK c hm.1
  apply chain_valid (f.variables + j * (K + 1)) _ c ?_ ?_ d hd
  · change f.variables + j * (K + 1) + c.length <
      f.variables + (K + 1) * f.clauses.length
    have hmul := Nat.mul_le_mul_left (K + 1) (show j + 1 ≤ f.clauses.length by omega)
    nlinarith
  · intro l hl
    have h := hf c hm.1 l hl
    change l.variable < f.variables + (K + 1) * f.clauses.length
    omega

def clauseVariables (c : Clause) : List ℕ :=
  [c.first.variable, c.second.variable, c.third.variable]

theorem unit_count (l : Literal) (v : ℕ) :
    (clauseVariables (unit l)).count v = 3 * (if l.variable = v then 1 else 0) := by
  by_cases h : l.variable = v <;> simp [clauseVariables, unit, h]

theorem orGate_count (p v : ℕ) (l : Literal) :
    ((orGate p l).flatMap clauseVariables).count v =
      2 * (if l.variable = v then 1 else 0) +
      2 * (if p = v then 1 else 0) + 5 * (if p + 1 = v then 1 else 0) := by
  by_cases hl : l.variable = v <;> by_cases hp : p = v <;>
    by_cases hp' : p + 1 = v <;>
    simp [orGate, clauseVariables, negate, positive, negative, hl, hp, hp']

theorem interval_indicator_step (p t v : ℕ) :
    (if p = v then 1 else 0) + (if p + 1 ≤ v ∧ v < p + 1 + t then 1 else 0) =
      (if p ≤ v ∧ v < p + (t + 1) then 1 else 0) := by
  split_ifs <;> omega

theorem interval_indicator_step' (p t v : ℕ) :
    (if p + 1 = v then 1 else 0) + (if p + 1 < v ∧ v ≤ p + 1 + t then 1 else 0) =
      (if p < v ∧ v ≤ p + (t + 1) then 1 else 0) := by
  split_ifs <;> omega

theorem gates_count (base start v : ℕ) (c : List Literal) :
    (((c.zipIdx start).flatMap fun (l, t) => orGate (base + t) l).flatMap
      clauseVariables).count v =
      2 * (c.map Literal.variable).count v +
      2 * (if base + start ≤ v ∧ v < base + start + c.length then 1 else 0) +
      5 * (if base + start < v ∧ v ≤ base + start + c.length then 1 else 0) := by
  induction c generalizing start with
  | nil => simp; split_ifs <;> omega
  | cons l c ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_append, List.count_append,
        orGate_count, ih]
      have h₁ := interval_indicator_step (base + start) c.length v
      have h₂ := interval_indicator_step' (base + start) c.length v
      simp only [List.map_cons, List.length_cons]
      have hcount : (l.variable :: c.map Literal.variable).count v =
          (c.map Literal.variable).count v + (if l.variable = v then 1 else 0) := by
        by_cases hl : l.variable = v <;> simp [hl]
      rw [hcount]
      simp only [Nat.add_assoc, Nat.add_comm 1 c.length] at h₁ h₂ ⊢
      omega

theorem chain_count (base v : ℕ) (c : List Literal) :
    ((chain base c).flatMap clauseVariables).count v =
      2 * (c.map Literal.variable).count v +
      3 * (if base = v then 1 else 0) +
      3 * (if base + c.length = v then 1 else 0) +
      2 * (if base ≤ v ∧ v < base + c.length then 1 else 0) +
      5 * (if base < v ∧ v ≤ base + c.length then 1 else 0) := by
  simp only [chain, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.count_append, unit_count, gates_count, negative, positive,
    Nat.add_zero]
  omega

theorem chain_original_count (base v : ℕ) (c : List Literal) (hv : v < base) :
    ((chain base c).flatMap clauseVariables).count v =
      2 * (c.map Literal.variable).count v := by
  rw [chain_count]
  have hb : ¬base = v := by omega
  have he : ¬base + c.length = v := by omega
  simp [hb, he, show ¬base ≤ v by omega, show ¬base < v by omega]

theorem chains_original_count (n K start v : ℕ) (cs : List (List Literal)) (hv : v < n) :
    (((cs.zipIdx start).flatMap fun (c, j) => chain (n + j * (K + 1)) c).flatMap
      clauseVariables).count v = 2 * (cs.flatten.map Literal.variable).count v := by
  induction cs generalizing start with
  | nil => simp
  | cons c cs ih =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_append, List.count_append,
        chain_original_count _ _ _ (by omega), ih]
      simp only [List.flatten_cons, List.map_append, List.count_append]
      omega

theorem original_occurrence_eq (K : ℕ) (f : LongFormula) (v : ℕ)
    (hv : v < f.variables) :
    SourceCNFSemantics.occurrenceCount (translate K f) v = 2 * occurrenceCount f v :=
  chains_original_count f.variables K 0 v f.clauses hv

theorem chain_fresh_count (base v : ℕ) (c : List Literal)
    (hc : ∀ l ∈ c, l.variable ≠ v) :
    ((chain base c).flatMap clauseVariables).count v ≤ 8 ∧
      (v < base ∨ base + c.length < v →
        ((chain base c).flatMap clauseVariables).count v = 0) := by
  have hz : (c.map Literal.variable).count v = 0 := by
    apply List.count_eq_zero.mpr
    intro hv
    obtain ⟨l, hl, he⟩ := List.mem_map.mp hv
    exact hc l hl he
  rw [chain_count, hz]
  constructor
  · split_ifs <;> omega
  · intro h
    split_ifs <;> omega

theorem chains_fresh_count (n K start v : ℕ) (cs : List (List Literal))
    (hv : n ≤ v) (hvars : ∀ c ∈ cs, ∀ l ∈ c, l.variable < n)
    (hwidth : ∀ c ∈ cs, c.length ≤ K) :
    (((cs.zipIdx start).flatMap fun (c, j) => chain (n + j * (K + 1)) c).flatMap
      clauseVariables).count v ≤ 8 ∧
      (v < n + start * (K + 1) →
        (((cs.zipIdx start).flatMap fun (c, j) => chain (n + j * (K + 1)) c).flatMap
          clauseVariables).count v = 0) := by
  induction cs generalizing start with
  | nil => simp
  | cons c cs ih =>
      have hc := chain_fresh_count (n + start * (K + 1)) v c (by
        intro l hl
        have h := hvars c (by simp) l hl
        omega)
      have hlen := hwidth c (by simp)
      have ht := ih (start + 1)
        (fun d hd => hvars d (by simp [hd]))
        (fun d hd => hwidth d (by simp [hd]))
      rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_append, List.count_append]
      constructor
      · by_cases hn : v < n + (start + 1) * (K + 1)
        · rw [ht.2 hn, Nat.add_zero]
          exact hc.1
        · have hz := hc.2 (Or.inr (by nlinarith))
          rw [hz, Nat.zero_add]
          exact ht.1
      · intro hn
        rw [hc.2 (Or.inl hn), ht.2 (by nlinarith)]

theorem fresh_occurrence_le (K : ℕ) (f : LongFormula) (v : ℕ)
    (hf : f.Valid) (hK : f.WidthAtMost K) (hv : f.variables ≤ v) :
    SourceCNFSemantics.occurrenceCount (translate K f) v ≤ 8 :=
  (chains_fresh_count f.variables K 0 v f.clauses hv hf hK).1

theorem translate_boundedOccurrence (K d : ℕ) (f : LongFormula)
    (hf : f.Valid) (hK : f.WidthAtMost K) (hd : BoundedOccurrence f d) :
    SourceCNFSemantics.BoundedOccurrence (translate K f) (max (2 * d) 8) := by
  intro v _
  by_cases hv : v < f.variables
  · rw [original_occurrence_eq K f v hv]
    exact (Nat.mul_le_mul_left 2 (hd v hv)).trans (Nat.le_max_left _ _)
  · exact (fresh_occurrence_le K f v hf hK (by omega)).trans (Nat.le_max_right _ _)

end EthInapproximability.CurrentPaper.SourceClauseEncoding
