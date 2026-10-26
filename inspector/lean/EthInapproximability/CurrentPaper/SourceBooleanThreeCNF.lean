import EthInapproximability.CurrentPaper.SourceBooleanCounting
import EthInapproximability.CurrentPaper.SourceClauseEncoding

/-!
# The concrete finite-alphabet to ordered-three-CNF adapter

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
This composes the proved exact-one clauses with the proved prefix-OR chains.
No source-hardness assertion or running-time conclusion is assumed here.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanEncoding

open EncodedCNF
variable {n m a q : ℕ}

def threeCNF (P : CSP n m a q) (hq : 0 < q) : Formula :=
  SourceClauseEncoding.translate (width a q) (formula P hq)

def threeOccurrence (a q D : ℕ) : ℕ := max (2 * occurrenceBound a q D) 8

def variableRatio (a q : ℕ) : ℕ := a * q + width a q + 1

def threeGap (a q D : ℕ) (ε : ℚ) : ℚ :=
  (ε / ((D + 1 : ℚ) * sizeFactor a q)) / (3 * width a q + 2)

def threeSizeFactor (a q : ℕ) : ℕ :=
  a * q + (4 * width a q + 3) * sizeFactor a q

theorem threeCNF_valid (P : CSP n m a q) (hq : 0 < q) : (threeCNF P hq).Valid :=
  SourceClauseEncoding.translate_valid _ _ (valid P hq) (width_bound P hq)

theorem threeCNF_complete (P : CSP n m a q) (hq : 0 < q) (h : Satisfiable P) :
    EncodedCNF.Satisfiable (threeCNF P hq) :=
  SourceClauseEncoding.translate_satisfiable _ _ (valid P hq) (width_bound P hq)
    (complete P hq h)

theorem threeCNF_occurrence (P : CSP n m a q) (hq : 0 < q)
    (D : ℕ) (hD : BoundedOccurrence P D) :
    SourceCNFSemantics.BoundedOccurrence (threeCNF P hq) (threeOccurrence a q D) :=
  SourceClauseEncoding.translate_boundedOccurrence _ _ _ (valid P hq) (width_bound P hq)
    (bounded_occurrence P hq D hD)

theorem threeCNF_gap (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (D : ℕ) (ε : ℚ) (hε : 0 ≤ ε) (hn : n ≤ q * m)
    (hD : BoundedOccurrence P D) (hgap : Gap P ε) :
    SourceCNFSemantics.FormulaGap (threeCNF P hq) (threeGap a q D ε) := by
  apply SourceClauseEncoding.translate_gap _ _ _ (valid P hq) (width_bound P hq)
  · exact div_nonneg hε (mul_nonneg (by positivity) (by positivity))
  · exact gap P ha hq D ε hε hn hD hgap

theorem threeGap_pos (ha : 0 < a) {D : ℕ} {ε : ℚ} (hε : 0 < ε) :
    0 < threeGap a q D ε := by
  have hs : (0 : ℚ) < sizeFactor a q := by exact_mod_cast sizeFactor_pos (q := q) ha
  exact div_pos (div_pos hε (mul_pos (by positivity) hs)) (by positivity)

theorem constraints_le_length (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q) :
    m ≤ (formula P hq).clauses.length := by
  have hp : 1 ≤ a ^ q := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero q (by omega))
  have hm := Nat.mul_le_mul_left m hp
  rw [formula_length]
  unfold clauseCount
  omega

theorem source_variable_ratio (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (hn : n ≤ q * m) :
    (formula P hq).variables ≤ (a * q) * (formula P hq).clauses.length := by
  calc
    (formula P hq).variables = n * a := rfl
    _ ≤ (q * m) * a := Nat.mul_le_mul_right a hn
    _ = (a * q) * m := by ring
    _ ≤ (a * q) * (formula P hq).clauses.length :=
      Nat.mul_le_mul_left _ (constraints_le_length P ha hq)

theorem variableRatio_pos : 1 ≤ variableRatio a q := by unfold variableRatio; omega

theorem threeCNF_variable_ratio (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (hn : n ≤ q * m) :
    (threeCNF P hq).variables ≤ variableRatio a q * (threeCNF P hq).clauses.length :=
  SourceClauseEncoding.translate_variable_ratio _ _ _ (source_variable_ratio P ha hq hn)

theorem threeCNF_nonempty (P : CSP n m a q) (ha : 0 < a) (hq : 0 < q)
    (hm : 0 < m) : 0 < (threeCNF P hq).clauses.length := by
  have hc := constraints_le_length P ha hq
  have ht := SourceClauseEncoding.translate_length_lower (width a q) (formula P hq)
  change 0 < (SourceClauseEncoding.translate (width a q) (formula P hq)).clauses.length
  omega

theorem threeCNF_size (P : CSP n m a q) (hq : 0 < q) (hn : n ≤ q * m) :
    (threeCNF P hq).variables + (threeCNF P hq).clauses.length ≤
      threeSizeFactor a q * m := by
  have hc := formula_length_bound P hq hn
  have ht := SourceClauseEncoding.translate_length_le (width a q) (formula P hq) (width_bound P hq)
  have hv := Nat.mul_le_mul_right a hn
  unfold threeCNF
  rw [SourceClauseEncoding.translate_variables, formula_variables]
  calc
    n * a + (width a q + 1) * (formula P hq).clauses.length +
        (SourceClauseEncoding.translate (width a q) (formula P hq)).clauses.length ≤
      n * a + (width a q + 1) * (formula P hq).clauses.length +
        (3 * width a q + 2) * (formula P hq).clauses.length :=
      Nat.add_le_add_left ht _
    _ = n * a + (4 * width a q + 3) * (formula P hq).clauses.length := by ring
    _ ≤ (q * m) * a + (4 * width a q + 3) * (sizeFactor a q * m) :=
      Nat.add_le_add hv (Nat.mul_le_mul_left _ hc)
    _ = threeSizeFactor a q * m := by unfold threeSizeFactor; ring

end EthInapproximability.CurrentPaper.SourceBooleanEncoding
