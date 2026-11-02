import EthInapproximability.CurrentPaper.EncodedComplexity
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Composition of the encoded complexity statements

Source: locked v8 `thm:exact-main` and the source-composition argument.
These are language-level closure theorems for the actual finite Boolean-stack
model. They do not supply the paper-specific reduction or verifier runtime.
-/

namespace EthInapproximability.CurrentPaper.ComplexityReductionClosure

open BitMachine EncodedComplexity

/-- The identity program halts immediately with its input stack unchanged. -/
def identityMachine : Machine where
  stackCount := 1
  labelCount := 1
  controlCount := 1
  input := 0
  output := 0
  start := 0
  initial := 0
  program _ := .halt

theorem polytime_id : Polytime (id : List Bool → List Bool) := by
  refine ⟨identityMachine, 1, 0, ?_⟩
  intro input
  refine ⟨1, by simp, ?_, ?_⟩ <;>
    simp [Machine.run, Machine.step, Machine.init, identityMachine,
      Turing.TM2.step, Turing.TM2.stepAux]

/-- A polynomial-time machine cannot emit an uncharged long output. -/
theorem polytime_output_length {f : List Bool → List Bool} (hf : Polytime f) :
    ∃ c d : ℕ, ∀ input, (f input).length ≤ c * (input.length + 1) ^ d := by
  obtain ⟨M, c, d, h⟩ := hf
  refine ⟨1 + c * M.pushBound, d + 1, ?_⟩
  intro input
  have hb := output_length_bound M (h input)
  have hp : 1 ≤ (input.length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hn : input.length ≤ (input.length + 1) ^ (d + 1) := by
    rw [pow_succ]
    nlinarith
  have hd : (input.length + 1) ^ d ≤ (input.length + 1) ^ (d + 1) := by
    rw [pow_succ]
    nlinarith
  have hmul := Nat.mul_le_mul_right (c * M.pushBound) hd
  nlinarith

theorem reduces_refl (L : BinaryLanguage) : Reduces L L :=
  ⟨id, polytime_id, fun _ => Iff.rfl⟩

theorem reduces_trans {L K J : BinaryLanguage}
    (hLK : Reduces L K) (hKJ : Reduces K J) : Reduces L J := by
  obtain ⟨f, hf, hfc⟩ := hLK
  obtain ⟨g, hg, hgc⟩ := hKJ
  exact ⟨g ∘ f, BitMachineComposition.polytime_comp hf hg,
    fun input => (hfc input).trans (hgc (f input))⟩

/-- This transfers a cited source-hardness theorem only after an actual
polynomial-time encoded reduction has been provided. -/
theorem npHard_of_reduces {source target : BinaryLanguage}
    (hs : NPHard source) (hred : Reduces source target) : NPHard target := by
  intro L hL
  exact reduces_trans (hs L hL) hred

theorem npComplete_of_source {source target : BinaryLanguage}
    (hs : NPHard source) (hred : Reduces source target) (ht : InNP target) :
    NPComplete target :=
  ⟨ht, npHard_of_reduces hs hred⟩

/-- A total Boolean decision algorithm with its literal output bit charged. -/
def InP (L : BinaryLanguage) : Prop :=
  ∃ decide : List Bool → Bool, Polytime (fun input => [decide input]) ∧
    ∀ input, input ∈ L ↔ decide input = true

theorem inP_of_reduces {L K : BinaryLanguage}
    (hred : Reduces L K) (hK : InP K) : InP L := by
  obtain ⟨f, hf, hc⟩ := hred
  obtain ⟨decide, hd, hdc⟩ := hK
  exact ⟨fun input => decide (f input), BitMachineComposition.polytime_comp hf hd,
    fun input => (hc input).trans (hdc (f input))⟩

theorem npHard_inP_implies_np_subset_p {K : BinaryLanguage}
    (hhard : NPHard K) (hK : InP K) : ∀ L, InNP L → InP L := by
  intro L hL
  exact inP_of_reduces (hhard L hL) hK

end EthInapproximability.CurrentPaper.ComplexityReductionClosure
