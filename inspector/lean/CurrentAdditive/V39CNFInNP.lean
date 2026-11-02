import CurrentAdditive.V39CNFWitnessBoundary
import CurrentAdditive.V39CNFPrepare
import CurrentAdditive.V39CNFPreparedWrapper
import CurrentAdditive.V39DomainClockTotalization

/-! Literal encoded three-CNF is in NP in the actual finite-stack bit-machine
model. Preparation rejects malformed encodings and wrong assignment lengths;
the physical clause loop evaluates the remaining canonical literal stream.
The charged unary-fuel simulation makes the evaluator total on every word.
No source-language identity, verifier callback, or runtime premise is used. -/

noncomputable section

namespace CurrentAdditive.V39CNFInNP

open EthInapproximability.CurrentPaper
open EncodedCommunication EncodedComplexity

def answer (word : List Bool) : Bool :=
  (GeneralPolynomialClock.result (410 + 4) V39CNFPreparedWrapper.machine word).headD false

theorem answer_polytime : BitMachine.Polytime (fun word => [answer word]) :=
  BitMachineComposition.polytime_comp
    (GeneralPolynomialClock.polytime (410 + 4) V39CNFPreparedWrapper.machine)
    V39DomainClockTotalization.DefaultBit.polytime

theorem answer_of_run (word : List Bool) (bit : Bool)
    (h : V39CNFPreparedWrapper.machine.OutputsWithin word [bit]
      (410 * (word.length + 1) ^ 4)) : answer word = bit := by
  have hb : 410 * (word.length + 1) ^ 4 ≤
      GeneralPolynomialFuelPrefix.clockLength (degree := 410 + 4) word :=
    V39DomainClockTotalization.polynomial_le_written_fuel 410 4 word.length
  have he := GeneralPolynomialClock.outputs_valid (410 + 4) V39CNFPreparedWrapper.machine
    word [bit] (BitMachine.outputsWithin_mono _ h hb)
  have hu := BitMachine.outputsWithin_unique
    (GeneralPolynomialClock.machine (410 + 4) V39CNFPreparedWrapper.machine)
    (GeneralPolynomialClock.outputs_all (410 + 4) V39CNFPreparedWrapper.machine word) he
  simp only [answer, hu, List.headD_cons]

theorem answer_false : answer [false] = false := by
  apply answer_of_run
  exact BitMachine.outputsWithin_mono _ V39CNFPreparedWrapper.outputs_false (by norm_num)

theorem answer_clauses (cs : List EncodedCNF.Clause) (assignment : List Bool)
    (hv : ∀ c ∈ cs, c.Valid assignment.length) :
    answer (true :: pair (EncodedCNF.clauseFields cs) assignment) =
      cs.all (fun c => c.eval assignment) := by
  apply answer_of_run
  exact V39CNFPreparedWrapper.outputs_clauses cs assignment hv

theorem prepared_answer (code : List Bool) :
    answer (V39CNFPrepare.result code) = V39CNFWitnessBoundary.verifier code := by
  cases hd : readField code with
  | none => simp only [V39CNFPrepare.result, V39CNFWitnessBoundary.verifier, hd, answer_false]
  | some p =>
    obtain ⟨input, assignment⟩ := p
    cases hf : EncodedCNF.decode input with
    | none =>
      simp only [V39CNFPrepare.result, V39CNFWitnessBoundary.verifier, hd,
        EncodedCNF.verifyEncoded, hf, answer_false]
    | some f =>
      by_cases hl : assignment.length = f.variables
      · have hv : ∀ c ∈ f.clauses, c.Valid assignment.length := by
          simpa only [hl] using EncodedCNF.decode_valid hf
        simp only [V39CNFPrepare.result, V39CNFWitnessBoundary.verifier, hd,
          EncodedCNF.verifyEncoded, hf, hl, ↓reduceIte, decide_true, Bool.true_and]
        exact answer_clauses f.clauses assignment hv
      · simp only [V39CNFPrepare.result, V39CNFWitnessBoundary.verifier, hd,
          EncodedCNF.verifyEncoded, hf, hl, ↓reduceIte, decide_false,
          Bool.false_and, answer_false]

theorem verifier_polytime :
    BitMachine.Polytime (fun code => [V39CNFWitnessBoundary.verifier code]) := by
  have hp := BitMachineComposition.polytime_comp V39CNFPrepare.polytime answer_polytime
  change BitMachine.Polytime (fun code => [answer (V39CNFPrepare.result code)]) at hp
  have he : (fun code => [answer (V39CNFPrepare.result code)]) =
      (fun code => [V39CNFWitnessBoundary.verifier code]) := by
    funext code
    rw [prepared_answer]
  rwa [he] at hp

def verifierMachine : BitMachine.Machine := Classical.choose verifier_polytime
def verifierCoefficient : ℕ := Classical.choose (Classical.choose_spec verifier_polytime)
def verifierDegree : ℕ := Classical.choose (Classical.choose_spec
  (Classical.choose_spec verifier_polytime))

theorem verifier_outputs (code : List Bool) :
    verifierMachine.OutputsWithin code [V39CNFWitnessBoundary.verifier code]
      (verifierCoefficient * (code.length + 1) ^ verifierDegree) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec verifier_polytime)) code

theorem literal_cnf_inNP : InNP EncodedCNF.Language :=
  V39CNFWitnessBoundary.inNP_of_verifier_runtime verifier_polytime

theorem literal_cnf_reduces_to_nphard (L : BinaryLanguage) (hard : NPHard L) :
    Reduces EncodedCNF.Language L := hard EncodedCNF.Language literal_cnf_inNP

#print axioms answer_polytime
#print axioms answer_of_run
#print axioms prepared_answer
#print axioms verifier_polytime
#print axioms verifier_outputs
#print axioms literal_cnf_inNP
#print axioms literal_cnf_reduces_to_nphard

end CurrentAdditive.V39CNFInNP
