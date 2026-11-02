import EthInapproximability.CurrentPaper.SourceClauseSoundness
import EthInapproximability.CurrentPaper.SourceClauseCounting

/-!
# Explicit completion of the bounded-width Boolean source encoding

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
The auxiliary variables store the OR of each original clause prefix.
This gives an actual assignment, not a satisfiability oracle or certificate.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseEncoding

open EncodedCNF

/-- Keep all original bits, then fill each clause's private block with the
truth values of its prefixes. Slots beyond a short clause are harmless. -/
def extension (K : ℕ) (f : LongFormula) (a : List Bool) : List Bool :=
  List.ofFn fun v : Fin (translate K f).variables =>
    if v.val < f.variables then a.getD v.val false
    else longClauseEval
      ((f.clauses.getD ((v.val - f.variables) / (K + 1)) []).take
        ((v.val - f.variables) % (K + 1))) a

@[simp] theorem extension_length (K : ℕ) (f : LongFormula) (a : List Bool) :
    (extension K f a).length = (translate K f).variables := List.length_ofFn

theorem extension_getD (K : ℕ) (f : LongFormula) (a : List Bool)
    (v : ℕ) (hv : v < (translate K f).variables) :
    (extension K f a).getD v false =
      if v < f.variables then a.getD v false
      else longClauseEval
        ((f.clauses.getD ((v - f.variables) / (K + 1)) []).take
          ((v - f.variables) % (K + 1))) a := by
  change v < f.variables + (K + 1) * f.clauses.length at hv
  simp [extension, List.getD_eq_getElem?_getD, hv]

theorem extension_original (K : ℕ) (f : LongFormula) (a : List Bool)
    (v : ℕ) (hv : v < f.variables) :
    (extension K f a).getD v false = a.getD v false := by
  rw [extension_getD K f a v (by simp only [translate]; omega), if_pos hv]

theorem extension_aux (K : ℕ) (f : LongFormula) (a : List Bool)
    (j t : ℕ) (hj : j < f.clauses.length) (ht : t < K + 1) :
    (extension K f a).getD (f.variables + j * (K + 1) + t) false =
      longClauseEval ((f.clauses.getD j []).take t) a := by
  have hb : f.variables + j * (K + 1) + t < (translate K f).variables := by
    simp only [translate]
    have hm := Nat.mul_le_mul_right (K + 1) (show j + 1 ≤ f.clauses.length by omega)
    nlinarith
  rw [extension_getD K f a _ hb, if_neg (by omega)]
  rw [show f.variables + j * (K + 1) + t - f.variables = j * (K + 1) + t by omega]
  have hd : (j * (K + 1) + t) / (K + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht]
    omega
  rw [hd, Nat.mul_add_mod_of_lt ht]

theorem extension_literal (K : ℕ) (f : LongFormula) (a : List Bool)
    (l : Literal) (hl : l.variable < f.variables) :
    l.eval (extension K f a) = l.eval a := by
  simp only [Literal.eval, extension_original K f a l.variable hl]

theorem extension_clause (K : ℕ) (f : LongFormula) (a : List Bool)
    (c : List Literal) (hc : ∀ l ∈ c, l.variable < f.variables) :
    longClauseEval c (extension K f a) = longClauseEval c a := by
  induction c with
  | nil => rfl
  | cons l c ih =>
      simp only [longClauseEval, List.any_cons]
      rw [extension_literal K f a l (hc l (by simp))]
      exact congrArg (fun b => l.eval a || b) (ih (fun x hx => hc x (by simp [hx])))

theorem extension_chain (K : ℕ) (f : LongFormula) (a : List Bool)
    (hf : f.Valid) (hK : f.WidthAtMost K) (j : Fin f.clauses.length)
    (hs : longClauseEval (f.clauses.get j) a = true) :
    ((chain (f.variables + j.val * (K + 1)) (f.clauses.get j)).all
      fun c => c.eval (extension K f a)) = true := by
  have hc : f.clauses.get j ∈ f.clauses := List.get_mem _ _
  have hlen := hK _ hc
  have hj : f.clauses.getD j.val [] = f.clauses.get j := by
    simp [List.getD_eq_getElem?_getD, j.isLt]
  apply (chain_all_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · simpa [longClauseEval] using extension_aux K f a j.val 0 j.isLt (by omega)
  · rw [extension_aux K f a j.val (f.clauses.get j).length j.isLt (by omega), hj,
      List.take_length]
    exact hs
  · intro t
    have ht : t.val + 1 < K + 1 := by omega
    rw [show f.variables + j.val * (K + 1) + t.val + 1 =
      f.variables + j.val * (K + 1) + (t.val + 1) by omega]
    rw [extension_aux K f a j.val (t.val + 1) j.isLt ht,
      extension_aux K f a j.val t.val j.isLt (by omega), hj]
    rw [extension_literal K f a _ (hf _ hc _ (List.get_mem _ _))]
    change longClauseEval ((f.clauses.get j).take (t.val + 1)) a =
      (longClauseEval ((f.clauses.get j).take t.val) a ||
        ((f.clauses.get j).get t).eval a)
    rw [List.take_succ_eq_append_getElem t.isLt]
    simp only [longClauseEval, List.any_append, List.any_cons, List.any_nil,
      Bool.or_false, List.get_eq_getElem]

/-- A satisfying original assignment is extended explicitly to every
generated clause, preserving the original variable prefix. -/
theorem translate_complete (K : ℕ) (f : LongFormula)
    (hf : f.Valid) (hK : f.WidthAtMost K) (a : List Bool)
    (hs : f.eval a = true) : (translate K f).eval (extension K f a) = true := by
  rw [Formula.eval, translate, List.all_flatMap, List.all_eq_true]
  rw [List.forall_mem_zipIdx']
  intro j hj
  apply extension_chain K f a hf hK ⟨j, hj⟩
  exact List.all_eq_true.mp hs _ (List.get_mem _ _)

theorem translate_satisfiable (K : ℕ) (f : LongFormula)
    (hf : f.Valid) (hK : f.WidthAtMost K) (hs : f.Satisfiable) :
    EncodedCNF.Satisfiable (translate K f) := by
  obtain ⟨a, _, ha⟩ := hs
  exact ⟨extension K f a, extension_length K f a, translate_complete K f hf hK a ha⟩

/-- No assignment to the fresh bits can make a false original clause true. -/
theorem translate_sound (K : ℕ) (f : LongFormula) (a : List Bool)
    (hs : (translate K f).eval a = true) : f.eval a = true := by
  change (f.clauses.zipIdx.flatMap fun (c, j) =>
    chain (f.variables + j * (K + 1)) c).all (fun c => c.eval a) = true at hs
  rw [List.all_flatMap, List.all_eq_true] at hs
  rw [List.forall_mem_zipIdx'] at hs
  rw [LongFormula.eval, List.all_eq_true]
  intro c hc
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hc
  exact chain_sound _ _ a (hs j.val j.isLt)

theorem translate_satisfiable_iff (K : ℕ) (f : LongFormula)
    (hf : f.Valid) (hK : f.WidthAtMost K) :
    EncodedCNF.Satisfiable (translate K f) ↔ f.Satisfiable := by
  constructor
  · rintro ⟨a, ha, hs⟩
    refine ⟨a.take f.variables, ?_, ?_⟩
    · rw [List.length_take, ha]
      apply min_eq_left
      simp only [translate]
      omega
    · have hh := translate_sound K f a hs
      rw [LongFormula.eval, List.all_eq_true] at hh ⊢
      intro c hc
      rw [longClauseEval_take c a f.variables (hf c hc)]
      exact hh c hc
  · exact translate_satisfiable K f hf hK

/-- Every old violation survives, and the number of clauses grows by at
most `3*K+2`. The soundness loss is therefore an explicit constant. -/
theorem translate_gap (K : ℕ) (f : LongFormula) (ρ : ℚ)
    (hf : f.Valid) (hK : f.WidthAtMost K) (hρ : 0 ≤ ρ)
    (hgap : FormulaGap f ρ) :
    SourceCNFSemantics.FormulaGap (translate K f) (ρ / (3 * K + 2)) := by
  intro a ha
  have hlen : (a.take f.variables).length = f.variables := by
    rw [List.length_take, ha, translate_variables]
    apply min_eq_left
    omega
  have hsource := hgap (a.take f.variables) hlen
  have hcount : ((falseClauses f (a.take f.variables)).card : ℚ) ≤
      ((SourceCNFSemantics.falseClauses (translate K f) a).card : ℚ) := by
    exact_mod_cast falseClauses_take_le_translate K f hf a
  have hsize : ((translate K f).clauses.length : ℚ) ≤
      (3 * K + 2) * (f.clauses.length : ℚ) := by
    exact_mod_cast translate_length_le K f hK
  have hden : (0 : ℚ) < 3 * K + 2 := by positivity
  calc
    ρ / (3 * K + 2) * (translate K f).clauses.length ≤
        ρ / (3 * K + 2) * ((3 * K + 2) * f.clauses.length) :=
      mul_le_mul_of_nonneg_left hsize (div_nonneg hρ (le_of_lt hden))
    _ = ρ * f.clauses.length := by field_simp
    _ ≤ (falseClauses f (a.take f.variables)).card := hsource
    _ ≤ (SourceCNFSemantics.falseClauses (translate K f) a).card := hcount

/-- A known linear bound on old variables remains a known linear bound
on new variables. Unused padding bits do not require a trimming oracle. -/
theorem translate_variable_ratio (K V : ℕ) (f : LongFormula)
    (hV : f.variables ≤ V * f.clauses.length) :
    (translate K f).variables ≤ (V + K + 1) * (translate K f).clauses.length := by
  have hm : f.clauses.length ≤ (translate K f).clauses.length := by
    have h := translate_length_lower K f
    omega
  calc
    (translate K f).variables = f.variables + (K + 1) * f.clauses.length := rfl
    _ ≤ V * f.clauses.length + (K + 1) * f.clauses.length :=
      Nat.add_le_add_right hV _
    _ = (V + K + 1) * f.clauses.length := by ring
    _ ≤ (V + K + 1) * (translate K f).clauses.length := Nat.mul_le_mul_left _ hm

/-- The complete bounded-width to ordered-three-CNF interface. Every
property refers to the same literal, promise-independent translation. -/
theorem translate_specification (K d V : ℕ) (f : LongFormula) (ρ : ℚ)
    (hf : f.Valid) (hK : f.WidthAtMost K) (hd : BoundedOccurrence f d)
    (hV : f.variables ≤ V * f.clauses.length) (hρ : 0 ≤ ρ) :
    (translate K f).Valid ∧
    (EncodedCNF.Satisfiable (translate K f) ↔ f.Satisfiable) ∧
    (FormulaGap f ρ → SourceCNFSemantics.FormulaGap (translate K f) (ρ / (3 * K + 2))) ∧
    SourceCNFSemantics.BoundedOccurrence (translate K f) (max (2 * d) 8) ∧
    (translate K f).variables = f.variables + (K + 1) * f.clauses.length ∧
    (translate K f).clauses.length ≤ (3 * K + 2) * f.clauses.length ∧
    2 * f.clauses.length ≤ (translate K f).clauses.length ∧
    (translate K f).variables ≤ (V + K + 1) * (translate K f).clauses.length := by
  exact ⟨translate_valid K f hf hK, translate_satisfiable_iff K f hf hK,
    translate_gap K f ρ hf hK hρ, translate_boundedOccurrence K d f hf hK hd,
    rfl, translate_length_le K f hK, translate_length_lower K f,
    translate_variable_ratio K V f hV⟩

end EthInapproximability.CurrentPaper.SourceClauseEncoding
