import EthInapproximability.CurrentPaper.EncodedCNF

/-!
# Fixed canonical rejecting ordered three-CNF

Malformed CSP bitstrings map to one ordinary unsatisfiable ordered three-CNF:
one variable with contradictory repeated-literal unit clauses. This fixed
formula is valid under the three-literal record convention.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRejectFormula

open EncodedCNF

def positive : Literal := ⟨0, true⟩
def negative : Literal := ⟨0, false⟩
def formula : Formula :=
  ⟨1, [⟨positive, positive, positive⟩,
    ⟨negative, negative, negative⟩]⟩

def bits : List Bool := EncodedCNF.encode formula

theorem valid : formula.Valid := by decide

theorem decoded : EncodedCNF.decode bits = some formula :=
  EncodedCNF.decode_encode formula valid

theorem unsatisfiable : ¬ EncodedCNF.Satisfiable formula := by
  rintro ⟨assignment, hlen, heval⟩
  cases assignment with
  | nil => simp [formula] at hlen
  | cons b tail =>
      cases tail with
      | cons c rest => simp [formula] at hlen
      | nil => cases b <;> simp [formula, Formula.eval,
          Clause.eval, Literal.eval, positive, negative] at heval

theorem bits_not_language : bits ∉ EncodedCNF.Language := by
  rw [EncodedCNF.language_iff_decoded decoded]
  exact unsatisfiable

end EthInapproximability.CurrentPaper.SourceCSPRejectFormula
