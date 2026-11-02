import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Encoded NP and polynomial reductions in the fixed bit-machine model

Source: v8 `thm:exact-main`. This file fixes the language-level targets and
connects the actual encoded certificate theorem to the remaining operational
verifier obligation. It does not assert that obligation or NP-completeness.
All polynomial-time predicates refer to finite Boolean-stack programs.
-/

namespace EthInapproximability.CurrentPaper.EncodedComplexity

open BitMachine EncodedCommunication

abbrev BinaryLanguage := Set (List Bool)

def pair (input witness : List Bool) : List Bool := field input ++ witness

theorem pair_length (input witness : List Bool) :
    (pair input witness).length = 2 * input.length + 1 + witness.length := by
  simp [pair, field_length]

/-- Polynomially bounded certificates checked by one fixed deterministic
finite Boolean-stack machine on every possible input string. -/
def InNP (L : BinaryLanguage) : Prop :=
  ∃ verify : List Bool → Bool, Polytime (fun code => [verify code]) ∧
    ∃ c d : ℕ, ∀ input,
      input ∈ L ↔ ∃ witness, witness.length ≤ c * (input.length + 1) ^ d ∧
        verify (pair input witness) = true

def Reduces (L K : BinaryLanguage) : Prop :=
  ∃ f : List Bool → List Bool, Polytime f ∧ ∀ input, input ∈ L ↔ f input ∈ K

def NPHard (K : BinaryLanguage) : Prop := ∀ L, InNP L → Reduces L K

def NPComplete (K : BinaryLanguage) : Prop := InNP K ∧ NPHard K

/-- One encoded input, not a host-language pair carrying uncharged data. -/
def communicationVerifier (code : List Bool) : Bool :=
  match readField code with
  | none => false
  | some (input, witness) => verifyEncoded input witness

theorem communicationVerifier_pair (input witness : List Bool) :
    communicationVerifier (pair input witness) = verifyEncoded input witness := by
  simp [communicationVerifier, pair, readField_append]

/-- This is the precise pending verifier-runtime implication. Its premise
names the concrete total parser/verifier, not an unspecified verifier. -/
theorem communication_inNP_of_runtime
    (hruntime : Polytime (fun code => [communicationVerifier code])) :
    InNP EncodedCommunication.Language := by
  refine ⟨communicationVerifier, hruntime, 6, 2, ?_⟩
  intro input
  constructor
  · intro h
    obtain ⟨w, hw, hb⟩ := verifyEncoded_complete_polynomial input h
    refine ⟨w, hb.trans ?_, ?_⟩
    · nlinarith [sq_nonneg (input.length : ℤ)]
    · simpa only [communicationVerifier_pair] using hw
  · rintro ⟨w, _, hw⟩
    exact verifyEncoded_sound input w (by simpa only [communicationVerifier_pair] using hw)

end EthInapproximability.CurrentPaper.EncodedComplexity
