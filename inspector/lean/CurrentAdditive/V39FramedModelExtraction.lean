import CurrentAdditive.V39FramedNumericalEndpoint
import CurrentAdditive.V39DomainClockTotalization

/-! The source clocks are polynomial in TABLE ENTRY COUNT T on valid
inputs, exactly as v39 specifies. The actual comparator input preserves
the whole table and threshold frame. Fixed timeouts then give all-word
physical clocks without a valid-input or numerical-range membership test. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39FramedModelExtraction

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)
open CurrentAdditive.V39FramedNumerical
open CurrentAdditive.V39FramedNumericalEndpoint
open CurrentAdditive.V39DomainClockTotalization

def TableDomain (word : List Bool) : Prop :=
  ∃ d, Paper2.AModel.targetD word = some d

/-- A table payload is part of its literal canonical word; malformed words
have entry count zero. This bounds entry-count clocks by word-length clocks. -/
theorem entries_le_word_length (word : List Bool) :
    CurrentAdditive.Eventual.entries word ≤ word.length := by
  unfold CurrentAdditive.Eventual.entries
  cases hd : Paper2.AModel.decodeMatrix word with
  | none => simp
  | some value =>
    rcases value with ⟨r, c, table⟩
    obtain ⟨hw, hv⟩ := Paper2.AModel.decodeMatrix_sound hd
    rw [← hw]
    simp only [Paper2.AModel.matrixWord, List.length_append]
    have hl := hv.2.2
    omega

theorem entries_le_frame_length (word out : List Bool) (m : ℕ) :
    CurrentAdditive.Eventual.entries word ≤
      (pair (natField m ++ word) out).length := by
  have hh := entries_le_word_length word
  simp only [EncodedComplexity.pair_length, List.length_append]
  omega

/-- Only requested rational comparisons on actual outputs of valid tables.
The requests can encode the midpoint image and its source-prescribed rational
length restriction; no unrequested rational is assumed correct or fast. -/
def ComparisonDomain (Requests : List Bool → ℕ → Prop)
    (sourceOutput : List Bool → List Bool) (input : List Bool) : Prop :=
  ∃ word d m, Paper2.AModel.targetD word = some d ∧ Requests word m ∧
    input = pair (natField m ++ word) (sourceOutput word)

/-- Extract a total physical carrier from the literal source-domain clocks.
The estimator and requested comparison clocks are both measured in T.
Full-frame physical timeouts preserve every requested valid numerical result;
no clock or semantic assertion is imposed on malformed or unreachable words. -/
theorem extract_estimator
    (Requests : List Bool → ℕ → Prop)
    (sourceOutput : List Bool → List Bool) (value : List Bool → ℝ)
    (Mest : BitMachine.Machine) (ce de : ℕ)
    (hest : ∀ word d, Paper2.AModel.targetD word = some d →
      Mest.OutputsWithin word (sourceOutput word)
        (ce*(CurrentAdditive.Eventual.entries word+1)^de))
    (compare : List Bool → Bool) (Mcompare : BitMachine.Machine) (cc dc : ℕ)
    (hclock : ∀ word d, Paper2.AModel.targetD word = some d → ∀ m,
      Requests word m →
      Mcompare.OutputsWithin (pair (natField m ++ word) (sourceOutput word))
        [compare (pair (natField m ++ word) (sourceOutput word))]
        (cc*(CurrentAdditive.Eventual.entries word+1)^dc))
    (hcorrect : ∀ word d, Paper2.AModel.targetD word = some d → ∀ m,
      Requests word m →
      compare (pair (natField m ++ word) (sourceOutput word)) =
        decide (value (sourceOutput word) < (m:ℝ)/2)) :
    ∃ E : Estimator, E.value = value ∧ ComparableRequests E Requests ∧
      ∀ word d, Paper2.AModel.targetD word = some d → E.output word = sourceOutput word := by
  obtain ⟨totalOutput, hpolyOutput, hOutput⟩ := totalize_on_domain
    TableDomain sourceOutput Mest ce de (by
      intro word hw
      obtain ⟨d, hd⟩ := hw
      exact BitMachine.outputsWithin_mono Mest (hest word d hd)
        (Nat.mul_le_mul_left ce (Nat.pow_le_pow_left
          (Nat.add_le_add_right (entries_le_word_length word) 1) de)))
  obtain ⟨totalCompare, hpolyCompare, hCompare⟩ := totalize_boolean_on_domain
    (ComparisonDomain Requests sourceOutput) compare Mcompare cc dc (by
      intro input hinput
      obtain ⟨word, d, m, hd, hr, rfl⟩ := hinput
      exact BitMachine.outputsWithin_mono Mcompare (hclock word d hd m hr)
        (Nat.mul_le_mul_left cc (Nat.pow_le_pow_left
          (Nat.add_le_add_right (entries_le_frame_length word (sourceOutput word) m) 1) dc)))
  let E : Estimator := {
    output := totalOutput
    physical := hpolyOutput
    value := value
    comparator := { output := totalCompare, physical := hpolyCompare }
  }
  refine ⟨E, rfl, ?_, ?_⟩
  · intro word d m hd hr
    change totalCompare (pair (natField m ++ word) (totalOutput word)) =
      decide (value (totalOutput word) < (m:ℝ)/2)
    rw [hOutput word ⟨d, hd⟩]
    rw [hCompare _ ⟨word, d, m, hd, hr, rfl⟩]
    exact hcorrect word d hd m hr
  · intro word d hd
    exact hOutput word ⟨d, hd⟩

#print axioms entries_le_word_length
#print axioms entries_le_frame_length
#print axioms extract_estimator

end CurrentAdditive.V39FramedModelExtraction
