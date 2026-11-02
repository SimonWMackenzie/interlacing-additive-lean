import EthInapproximability.CurrentPaper.EncodedComplexity
import EthInapproximability.CurrentPaper.EncodedCNF
import EthInapproximability.CurrentPaper.CNFValidatorRuntime

/-! Literal CNF NP-membership boundary. The declared variable count is
unary, so an ordinary complete assignment is a linear-size certificate.
The semantic witness equivalence is proved here without an NP-membership
assumption. The remaining runtime theorem is explicitly conditional. -/

namespace CurrentAdditive.V39CNFWitnessBoundary

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication (readField readField_append)
open EthInapproximability.CurrentPaper.EncodedComplexity

def verifier (code : List Bool) : Bool :=
  match readField code with
  | none => false
  | some (input, assignment) => EncodedCNF.verifyEncoded input assignment

theorem verifier_pair (input assignment : List Bool) :
    verifier (pair input assignment) = EncodedCNF.verifyEncoded input assignment := by
  simp only [verifier, pair, readField_append]

theorem verifier_malformed_outer (code : List Bool) (h : readField code = none) :
    verifier code = false := by simp only [verifier, h]

theorem verifier_malformed_formula (input assignment : List Bool)
    (h : EncodedCNF.decode input = none) :
    verifier (pair input assignment) = false := by
  simp only [verifier_pair, EncodedCNF.verifyEncoded, h]

theorem verifier_wrong_assignment_length (input assignment : List Bool)
    (f : EncodedCNF.Formula) (h : EncodedCNF.decode input = some f)
    (hlen : assignment.length ≠ f.variables) :
    verifier (pair input assignment) = false := by
  simp only [verifier_pair, EncodedCNF.verifyEncoded, h, hlen, decide_false, Bool.false_and]

theorem literal_assignment_certificate (input : List Bool) :
    input ∈ EncodedCNF.Language ↔ ∃ assignment,
      assignment.length ≤ input.length ∧ verifier (pair input assignment) = true := by
  simpa only [verifier_pair] using EncodedCNF.language_iff_short_assignment input

theorem literal_assignment_polynomial_certificate (input : List Bool) :
    input ∈ EncodedCNF.Language ↔ ∃ assignment,
      assignment.length ≤ 1 * (input.length + 1) ^ 1 ∧
      verifier (pair input assignment) = true := by
  constructor
  · intro h
    obtain ⟨assignment, hlen, hv⟩ := (literal_assignment_certificate input).mp h
    exact ⟨assignment, by simp only [one_mul, pow_one]; omega, hv⟩
  · rintro ⟨assignment, _, hv⟩
    exact (EncodedCNF.language_iff_assignment input).mpr
      ⟨assignment, by simpa only [verifier_pair] using hv⟩

/-- This identifies the exact missing machine theorem. It is not a proved
membership result: physical all-input polynomial evaluation remains its
explicit premise, and must not be promoted to an assumption of the source. -/
theorem inNP_of_verifier_runtime
    (hphysical : BitMachine.Polytime (fun code => [verifier code])) :
    InNP EncodedCNF.Language := by
  exact ⟨verifier, hphysical, 1, 1, literal_assignment_polynomial_certificate⟩

#print axioms literal_assignment_certificate
#print axioms literal_assignment_polynomial_certificate
#print axioms inNP_of_verifier_runtime

end CurrentAdditive.V39CNFWitnessBoundary
