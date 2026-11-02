import CurrentAdditive.V39RawRationalAdapter
import CurrentAdditive.EventualDomain

/-! The numerical convention of selected v39, main.tex:398--415.
Every running-time and comparison promise is restricted to valid explicit
tables, actual estimator outputs, and polynomial-length binary rationals.
The source midpoint bound is proved by each constructor; there is no new
uninterpreted request predicate or stronger output-comparison oracle. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedNumericalExtraction

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39RawRationalAdapter
open CurrentAdditive.V39RandomEstimatorNormalization
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open CurrentAdditive.Eventual (entries)
open Paper2

def ValidTable (word : List Bool) : Prop := AModel.decodeMatrix word ≠ none

theorem valid_of_target {target : (ℕ × ℕ × List Bool) → ℕ}
    {word : List Bool} {D : ℕ}
    (h : (AModel.decodeMatrix word).map target = some D) : ValidTable word := by
  intro hn
  rw [hn] at h
  contradiction

theorem valid_matrix (i : Instance) (hi : i.Valid) :
    ValidTable (AModel.matrixWord i.rows i.cols i.table) := by
  rw [ValidTable, AModel.decodeMatrix_matrixWord hi]
  simp

theorem table_entries_le_length (word : List Bool) : entries word ≤ word.length := by
  unfold entries
  cases hd : AModel.decodeMatrix word with
  | none => simp
  | some p =>
    rcases p with ⟨r, c, table⟩
    obtain ⟨hw, hv⟩ := AModel.decodeMatrix_sound hd
    rw [← hw]
    simp only [AModel.matrixWord, List.length_append]
    have ht := hv.2.2
    omega

/-- The actual midpoint code represents (2B+k)/2=B+k/2. Its length is
exactly one more bit than the physical public numerator header. -/
theorem fixed_midpoint_value (B k : ℕ) :
    ((2 * B + k : ℕ) : ℝ) / 2 = (B : ℝ) + (k : ℝ) / 2 := by
  push_cast
  ring

theorem fixed_midpoint_code_length (m : ℕ) :
    (rationalCode (m : ℤ) 1).length = (natField m).length + 1 := by
  simp only [rationalCode_half, List.length_cons]

/-- A constructor's explicit polynomial header bound discharges the
polynomial binary-rational length condition. The exponent is not a
dyadic denominator parameter, and is not identified with input length. -/
theorem code_length_of_header_bound (m T c d : ℕ)
    (h : (natField m).length ≤ c * (T + 1) ^ d) :
    (rationalCode (m : ℤ) 1).length ≤ (c + 1) * (T + 1) ^ d := by
  rw [fixed_midpoint_code_length]
  have hp : 1 ≤ (T + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- A polynomial bound on the source's actual numerator also suffices;
the code contains its binary digits, together with the fixed half tag. -/
theorem code_length_of_numerator_bound (m T c d : ℕ)
    (h : m ≤ c * (T + 1) ^ d) :
    (rationalCode (m : ℤ) 1).length ≤ (2 * c + 2) * (T + 1) ^ d := by
  rw [rationalCode_half_length]
  have hb := UnaryBinaryEncoding.bits_length_le m
  have hp : 1 ≤ (T + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- A restriction of the manuscript's permitted numerical-estimator
convention to the positive half-integer rationals actually used here.
The single comparison machine and single estimator machine are uniform.
Clock coefficients may depend on the fixed polynomial rational-length
bound, but not on the table, midpoint, output, or estimator tape. -/
structure PermittedEstimator where
  raw : RawEstimator
  value : List Bool → ℝ
  ce : ℕ
  de : ℕ
  estimator_clock : ∀ word, ValidTable word →
    ∀ tape : Fin (raw.tapeLength word) → Bool,
      raw.machine.OutputsWithin (pair word (List.ofFn tape))
        (raw.output word (List.ofFn tape)) (ce * (entries word + 1) ^ de)
  compare : List Bool → Bool
  comparator_machine : BitMachine.Machine
  cc : ℕ → ℕ → ℕ
  dc : ℕ → ℕ → ℕ
  comparator_clock : ∀ c d word, ValidTable word → ∀ m : ℕ,
    (rationalCode (m : ℤ) 1).length ≤ c * (entries word + 1) ^ d →
    ∀ tape : Fin (raw.tapeLength word) → Bool,
      comparator_machine.OutputsWithin
        (rationalRequest m (raw.output word (List.ofFn tape)))
        [compare (rationalRequest m (raw.output word (List.ofFn tape)))]
        (cc c d * (entries word + 1) ^ dc c d)
  comparator_correct : ∀ c d word, ValidTable word → ∀ m : ℕ,
    (rationalCode (m : ℤ) 1).length ≤ c * (entries word + 1) ^ d →
    ∀ tape : Fin (raw.tapeLength word) → Bool,
      compare (rationalRequest m (raw.output word (List.ofFn tape))) =
        decide (value (raw.output word (List.ofFn tape)) < (m : ℝ) / 2)

/-- Fully discharge the raw-machine and numerical prerequisites for the
actual-output majority interface, at a family of proved valid tables and
proved polynomial-length midpoints. No request-domain premise remains. -/
theorem extract_family (A : PermittedEstimator) {ι : Type*}
    (word : ι → List Bool) (m : ι → ℕ) (c d : ℕ)
    (hvalid : ∀ x, ValidTable (word x))
    (hmid : ∀ x, (rationalCode (m x : ℤ) 1).length ≤
      c * (entries (word x) + 1) ^ d) :
    ∃ E : ActualEstimator,
      E.estimator = A.raw.normalize A.ce A.de ∧ E.value = A.value ∧
      (∀ x, E.actualComparison (word x) (m x)) ∧
      (∀ word, ValidTable word → ∀ P : List Bool → Prop,
        E.estimator.prob word P = A.raw.prob word P) := by
  obtain ⟨R, hcompare, _⟩ := actualEstimator_of_raw_rational_requests
    A.raw A.value word m (fun x => entries (word x))
    (fun x => table_entries_le_length (word x)) A.ce A.de
    (fun x => A.estimator_clock (word x) (hvalid x))
    A.compare A.comparator_machine (A.cc c d) (A.dc c d)
    (fun x => A.comparator_clock c d (word x) (hvalid x) (m x) (hmid x))
    (fun x => A.comparator_correct c d (word x) (hvalid x) (m x) (hmid x))
  let E : ActualEstimator := {
    estimator := A.raw.normalize A.ce A.de
    value := A.value
    comparator := R }
  refine ⟨E, rfl, rfl, hcompare, ?_⟩
  intro word hv P
  exact A.raw.normalize_prob_valid A.ce A.de word (entries word)
    (table_entries_le_length word) (A.estimator_clock word hv) P

#print axioms valid_of_target
#print axioms valid_matrix
#print axioms table_entries_le_length
#print axioms fixed_midpoint_value
#print axioms fixed_midpoint_code_length
#print axioms code_length_of_header_bound
#print axioms code_length_of_numerator_bound
#print axioms extract_family

end CurrentAdditive.V39PermittedNumericalExtraction
