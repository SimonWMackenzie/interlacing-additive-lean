import EthInapproximability.CurrentPaper.EncodedCNF

/-!
# Clause occurrences and the source gap

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
The clauses below have their existing OR semantics. Exact-one blocks are
an encoding device for alphabet symbols, not an alternative clause semantics.
-/

namespace EthInapproximability.CurrentPaper.SourceCNFSemantics

open EncodedCNF

def falseClauses (f : Formula) (assignment : List Bool) : Finset (Fin f.clauses.length) :=
  Finset.univ.filter fun i => (f.clauses.get i).eval assignment = false

/-- Clause occurrences are counted separately, even when syntactically equal. -/
def FormulaGap (f : Formula) (ρ : ℚ) : Prop :=
  ∀ assignment : List Bool, assignment.length = f.variables →
    ρ * f.clauses.length ≤ ((falseClauses f assignment).card : ℚ)

def occurrenceCount (f : Formula) (v : ℕ) : ℕ :=
  (f.clauses.flatMap fun c =>
    [c.first.variable, c.second.variable, c.third.variable]).count v

def BoundedOccurrence (f : Formula) (k : ℕ) : Prop :=
  ∀ v < f.variables, occurrenceCount f v ≤ k

theorem FormulaGap.le_one {f : Formula} {ρ : ℚ} (h : FormulaGap f ρ)
    (hm : 0 < f.clauses.length) : ρ ≤ 1 := by
  have hgap := h (List.replicate f.variables false) (List.length_replicate ..)
  have hc : (falseClauses f (List.replicate f.variables false)).card ≤ f.clauses.length := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ
      (falseClauses f (List.replicate f.variables false))
  have hcQ : ((falseClauses f (List.replicate f.variables false)).card : ℚ) ≤
      f.clauses.length := by exact_mod_cast hc
  have hmQ : (0 : ℚ) < f.clauses.length := by exact_mod_cast hm
  nlinarith

theorem not_satisfiable_clauses_pos (f : Formula) (h : ¬ Satisfiable f) :
    0 < f.clauses.length := by
  cases f with
  | mk n cs =>
      cases cs with
      | nil => exact False.elim (h (EncodedCNF.empty_satisfiable n))
      | cons c cs => simp

end EthInapproximability.CurrentPaper.SourceCNFSemantics
