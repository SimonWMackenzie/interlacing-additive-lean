import CurrentAdditive.V39CNFGuard
import CurrentAdditive.V39CNFStrip
import CurrentAdditive.V39CNFPhysicalFront
import CurrentAdditive.V39CNFAssignmentLength

/-! Total physical CNF preprocessing. The gates are the actual syntax and
assignment-length machines, with a charged physical source-preserving copy.
No validity premise or callback runtime is assumed. -/
namespace CurrentAdditive.V39CNFPrepare

open EthInapproximability.CurrentPaper
open EncodedCommunication EncodedComplexity

def result (code : List Bool) : List Bool :=
  match readField code with
  | none => [false]
  | some (input, assignment) =>
    match EncodedCNF.decode input with
    | none => [false]
    | some f => if assignment.length = f.variables then
        true :: pair (EncodedCNF.clauseFields f.clauses) assignment else [false]

def pipeline (code : List Bool) : List Bool :=
  V39CNFStrip.result (V39CNFGuard.result V39CNFPhysicalFront.validateFramed
    (V39CNFGuard.result (fun code => [V39CNFAssignmentLength.result code]) code))

theorem syntax_false : V39CNFGuard.result V39CNFPhysicalFront.validateFramed [false] = [false] := by
  have h : ([false] : List Bool) = pair [] [] := rfl
  rw [h]
  unfold V39CNFGuard.result
  rw [V39CNFPhysicalFront.validateFramed_malformed [] [] (by rfl)]
  rfl

theorem result_pair_formula (f : EncodedCNF.Formula) (assignment : List Bool)
    (hf : f.Valid) :
    result (pair (EncodedCNF.encode f) assignment) =
      if assignment.length = f.variables then
        true :: pair (EncodedCNF.clauseFields f.clauses) assignment else [false] := by
  simp only [result, pair, readField_append, EncodedCNF.decode_encode f hf]

theorem result_wrong_length (input assignment : List Bool) (f : EncodedCNF.Formula)
    (hd : EncodedCNF.decode input = some f) (hl : assignment.length ≠ f.variables) :
    result (pair input assignment) = [false] := by
  simp only [result, pair, readField_append, hd, hl, ↓reduceIte]

theorem result_pair_valid (input assignment : List Bool) (f : EncodedCNF.Formula)
    (hd : EncodedCNF.decode input = some f) (hl : assignment.length = f.variables) :
    result (pair input assignment) =
      true :: pair (EncodedCNF.clauseFields f.clauses) assignment := by
  simp only [result, pair, readField_append, hd, hl, ↓reduceIte]

theorem result_malformed_outer (code : List Bool) (h : readField code = none) :
    result code = [false] := by simp only [result, h]

theorem result_malformed_formula (input assignment : List Bool)
    (h : EncodedCNF.decode input = none) :
    result (pair input assignment) = [false] := by
  simp only [result, pair, readField_append, h]

theorem pipeline_pair_formula (input assignment : List Bool) :
    pipeline (pair input assignment) = result (pair input assignment) := by
  cases hd : EncodedCNF.decode input with
  | none =>
    unfold pipeline
    by_cases hl : V39CNFAssignmentLength.result (pair input assignment) = true
    · have he : V39CNFGuard.result (fun code => [V39CNFAssignmentLength.result code])
          (pair input assignment) = pair input assignment := by
        simp only [V39CNFGuard.result, List.headD_cons]
        exact if_pos hl
      rw [he]
      unfold V39CNFGuard.result
      rw [V39CNFPhysicalFront.validateFramed_malformed input assignment hd]
      change V39CNFStrip.result [false] = _
      rw [V39CNFStrip.result_false]
      simp only [result, pair, readField_append, hd]
    · have he : V39CNFGuard.result (fun code => [V39CNFAssignmentLength.result code])
          (pair input assignment) = [false] := by
        simp only [V39CNFGuard.result, List.headD_cons]
        exact if_neg hl
      rw [he, syntax_false, V39CNFStrip.result_false]
      simp only [result, pair, readField_append, hd]
  | some f =>
    have hi : EncodedCNF.encode f = input := EncodedCNF.decode_sound hd
    subst input
    unfold pipeline
    rw [show V39CNFGuard.result (fun code => [V39CNFAssignmentLength.result code])
        (pair (EncodedCNF.encode f) assignment) =
        if assignment.length = f.variables then pair (EncodedCNF.encode f) assignment
        else [false] by
      simp only [V39CNFGuard.result, V39CNFAssignmentLength.result_pair_formula,
        List.headD_cons, decide_eq_true_eq]]
    by_cases hl : assignment.length = f.variables
    · rw [if_pos hl]
      unfold V39CNFGuard.result
      rw [V39CNFPhysicalFront.validateFramed_valid _ assignment f hd]
      simp only [List.headD_cons, ↓reduceIte, V39CNFStrip.result_pair_formula,
        result_pair_formula f assignment (EncodedCNF.decode_valid hd), hl]
    · rw [if_neg hl, syntax_false, V39CNFStrip.result_false]
      simp only [result_pair_formula f assignment (EncodedCNF.decode_valid hd), hl, ↓reduceIte]

theorem pipeline_correct (code : List Bool) : pipeline code = result code := by
  cases hd : readField code with
  | none =>
    have hl : V39CNFAssignmentLength.result code = false := by
      simp only [V39CNFAssignmentLength.result, hd]
    simp only [pipeline, V39CNFGuard.result, hl, List.headD_cons, Bool.false_eq_true,
      ↓reduceIte]
    change V39CNFStrip.result (V39CNFGuard.result V39CNFPhysicalFront.validateFramed [false]) = _
    rw [syntax_false, V39CNFStrip.result_false]
    simp only [result, hd]
  | some p =>
    obtain ⟨input, assignment⟩ := p
    have he : pair input assignment = code := readField_sound hd
    rw [← he]
    exact pipeline_pair_formula input assignment

theorem polytime : BitMachine.Polytime result := by
  have hlength := V39CNFGuard.polytime (fun code => [V39CNFAssignmentLength.result code])
    V39CNFAssignmentLength.polytime
  have hsyntax := V39CNFGuard.polytime V39CNFPhysicalFront.validateFramed
    V39CNFPhysicalFront.validateFramed_polytime
  have h := BitMachineComposition.polytime_comp
    (BitMachineComposition.polytime_comp hlength hsyntax) V39CNFStrip.polytime
  change BitMachine.Polytime pipeline at h
  have he : pipeline = result := funext pipeline_correct
  rwa [he] at h

/- The machine and its two fixed polynomial constants are extracted from the
explicit physical construction above. No runtime or validity hypothesis is
an argument of any of these definitions or the all-input output theorem. -/
noncomputable def machine : BitMachine.Machine := Classical.choose polytime
noncomputable def coefficient : ℕ := Classical.choose (Classical.choose_spec polytime)
noncomputable def degree : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec polytime))
noncomputable def clock (n : ℕ) : ℕ := coefficient * (n + 1) ^ degree

theorem outputs (code : List Bool) : machine.OutputsWithin code (result code) (clock code.length) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec polytime)) code

theorem result_length (code : List Bool) : (result code).length ≤ code.length + 1 := by
  cases hd : readField code with
  | none => simp only [result, hd, List.length_singleton]; omega
  | some p =>
    obtain ⟨input, assignment⟩ := p
    have he := congrArg List.length (readField_sound hd)
    simp only [List.length_append, field_length] at he
    cases hf : EncodedCNF.decode input with
    | none => simp only [result, hd, hf, List.length_singleton]; omega
    | some f =>
      have hi := congrArg List.length (EncodedCNF.decode_sound hf)
      simp only [EncodedCNF.encode, List.length_append] at hi
      simp only [result, hd, hf]
      split
      · simp only [List.length_cons, pair, List.length_append, field_length]
        omega
      · simp only [List.length_singleton]; omega

#print axioms pipeline_correct
#print axioms polytime
#print axioms outputs
#print axioms result_length

end CurrentAdditive.V39CNFPrepare
