import CurrentAdditive.V39CNFWitnessBoundary
import CurrentAdditive.V39SignedAssignmentLookup
import CurrentAdditive.SmallBiasPClassInclusion

/-! Closed physical preprocessing and literal-query costs. The syntax
machine has an all-input polynomial clock. The query sum below counts
only executed signed lookups, not parsing, conversion or loop assembly;
it is deliberately not claimed as the full verifier runtime. -/

namespace CurrentAdditive.V39CNFPhysicalFront

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.SmallBias (firstPairField firstPairField_pair firstPairField_polytime)

def validateFramed (code : List Bool) : List Bool :=
  CNFValidator.result (firstPairField code)

theorem validateFramed_polytime : BitMachine.Polytime validateFramed :=
  BitMachineComposition.polytime_comp firstPairField_polytime CNFValidator.Runtime.polytime

theorem validateFramed_pair (input assignment : List Bool) :
    validateFramed (pair input assignment) = CNFValidator.result input := by
  simp only [validateFramed, firstPairField_pair]

theorem validateFramed_malformed (input assignment : List Bool)
    (h : EncodedCNF.decode input = none) :
    validateFramed (pair input assignment) = [false] := by
  rw [validateFramed_pair]
  simp only [CNFValidator.result, h, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

theorem validateFramed_valid (input assignment : List Bool) (f : EncodedCNF.Formula)
    (h : EncodedCNF.decode input = some f) :
    validateFramed (pair input assignment) = true :: input := by
  rw [validateFramed_pair]
  simp only [CNFValidator.result, h, Option.isSome_some, ↓reduceIte]

def literalClock (l : EncodedCNF.Literal) (assignment : List Bool) : ℕ :=
  2 * (l.positive :: ProtocolBitLookup.encodeInput l.variable assignment).length + 3

def clauseClock (c : EncodedCNF.Clause) (assignment : List Bool) : ℕ :=
  literalClock c.first assignment + literalClock c.second assignment +
    literalClock c.third assignment

def lookupClock (f : EncodedCNF.Formula) (assignment : List Bool) : ℕ :=
  (f.clauses.map fun c => clauseClock c assignment).sum

theorem literal_clock_bound (l : EncodedCNF.Literal) (assignment : List Bool)
    (n L : ℕ) (hl : l.variable < n) (ha : assignment.length = n) (hn : n ≤ L) :
    literalClock l assignment ≤ 4 * L + 7 := by
  simp only [literalClock, ProtocolBitLookup.encodeInput, List.length_cons,
    List.length_append, List.length_replicate]
  omega

/-- Each summand is the transition bound of the actual same finite machine,
with the exact encoded assignment and sign and the declared variable index. -/
theorem physical_literal (l : EncodedCNF.Literal) (assignment : List Bool) :
    V39SignedAssignmentLookup.machine.OutputsWithin
      (l.positive :: ProtocolBitLookup.encodeInput l.variable assignment)
      [l.eval assignment] (literalClock l assignment) :=
  V39SignedAssignmentLookup.outputs_literal l assignment

private theorem sum_clause_clock (cs : List EncodedCNF.Clause) (assignment : List Bool)
    (n L : ℕ) (ha : assignment.length = n) (hn : n ≤ L)
    (hv : ∀ c ∈ cs, c.Valid n) :
    (cs.map fun c => clauseClock c assignment).sum ≤ cs.length * (3 * (4 * L + 7)) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := hv c (by simp)
    have h1 := literal_clock_bound c.first assignment n L hc.1 ha hn
    have h2 := literal_clock_bound c.second assignment n L hc.2.1 ha hn
    have h3 := literal_clock_bound c.third assignment n L hc.2.2 ha hn
    have hs := ih (fun d hd => hv d (by simp [hd]))
    unfold clauseClock at hs
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    unfold clauseClock
    nlinarith

/-- The sum of all literal-lookup calls is quadratic in the literal CNF
input length. This does not charge yet-unbuilt binary-index conversion,
assignment copying, clause conjunction or controller dispatch. -/
theorem lookup_clock_bound (input assignment : List Bool) (f : EncodedCNF.Formula)
    (hdecode : EncodedCNF.decode input = some f) (ha : assignment.length = f.variables) :
    lookupClock f assignment ≤ 11 * (input.length + 1) ^ 2 := by
  have hn := EncodedCNF.decoded_variables_bound hdecode
  have hm := EncodedCNF.decoded_occurrences_bound hdecode
  have hs := sum_clause_clock f.clauses assignment f.variables input.length ha hn
    (EncodedCNF.decode_valid hdecode)
  change 3 * f.clauses.length ≤ input.length at hm
  unfold lookupClock
  nlinarith [Nat.mul_le_mul_right (4 * input.length + 7) hm]

#print axioms validateFramed_polytime
#print axioms physical_literal
#print axioms lookup_clock_bound

end CurrentAdditive.V39CNFPhysicalFront
