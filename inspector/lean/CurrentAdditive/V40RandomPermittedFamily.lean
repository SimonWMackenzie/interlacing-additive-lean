import CurrentAdditive.V39PermittedNumericalExtraction
import CurrentAdditive.V39PublicSchedule
import Paper2.AFrontProjection
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-! One permitted numerical estimator and comparator for every actual sampled
table size and every payload. The encoded-instance projection preserves the
literal payload; no square padding or replacement table is used. -/

noncomputable section

namespace CurrentAdditive.V40RandomPermittedFamily

open Paper2
open EthInapproximability.CurrentPaper
open EncodedCommunication
open V39PublicSchedule
open CurrentAdditive.V39PermittedNumericalExtraction
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.Eventual
open CurrentAdditive.ModelEndpointReview.RationalEndpoint

def instanceWord (L k : ℕ) (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    Instance := ⟨sampleSide L k, sampleSide L k, B L k, MatrixMaterialization.rowMajor f⟩

def matrixWord (L k : ℕ) (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    List Bool := AModel.matrixWord (sampleSide L k) (sampleSide L k)
      (MatrixMaterialization.rowMajor f)

def numerator (L k : ℕ) : ℕ := 2 * B L k + k

theorem side_pos (L k : ℕ) : 0 < sampleSide L k :=
  lt_of_lt_of_le (by positivity : 0 < 2 ^ H L k) (sampleSide_lower L k)

theorem matrix_valid (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    AModel.MatrixValid (sampleSide L k) (sampleSide L k) (MatrixMaterialization.rowMajor f) :=
  ⟨side_pos L k, side_pos L k, MatrixMaterialization.rowMajor_length f⟩

theorem valid_table (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    ValidTable (matrixWord L k f) := by
  exact valid_matrix (instanceWord L k f) (matrix_valid L k f)

theorem table_entries (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    entries (matrixWord L k f) = sampleSide L k ^ 2 := by
  simpa only [matrixWord, pow_two] using entries_matrixWord _ _ _ (matrix_valid L k f)

theorem numerator_le_entries (L k : ℕ) : numerator L k ≤ 2 * sampleSide L k ^ 2 := by
  have hh : H L k ≤ sampleSide L k :=
    (Nat.le_of_lt (Nat.lt_two_pow_self : H L k < 2 ^ H L k)).trans (sampleSide_lower L k)
  have hm := side_pos L k
  unfold numerator H at *
  nlinarith

theorem midpoint_code_bound (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (rationalCode (numerator L k : ℤ) 1).length ≤
      6 * (entries (matrixWord L k f) + 1) ^ 1 := by
  apply code_length_of_numerator_bound (numerator L k) _ 2 1
  rw [table_entries]
  have h := numerator_le_entries L k
  simpa only [pow_one] using h.trans (by omega)

theorem midpoint_value (L k : ℕ) :
    (numerator L k : ℝ) / 2 = (B L k : ℝ) + (k : ℝ) / 2 :=
  fixed_midpoint_value _ _

theorem projection_outputs (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    AFront.Projection.matrixMachine.OutputsWithin (encodeInstance (instanceWord L k f))
      (matrixWord L k f) (3 * ((encodeInstance (instanceWord L k f)).length + 1)) :=
  AFront.Projection.matrixMachine_encodeInstance (instanceWord L k f)

theorem projection_all_words (word : List Bool) :
    AFront.Projection.matrixMachine.OutputsWithin word (AFront.Projection.matrixPart word)
      (3 * (word.length + 1)) := AFront.Projection.matrixMachine_outputs word

structure Sample where
  L : ℕ
  k : ℕ
  table : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool

/-- The existential estimator precedes every graph, round and reduction
tape through the unrestricted sampled payload. All valid raw estimator
outputs, including inaccurate ones, retain their original tape and event law. -/
theorem extract_all (A : PermittedEstimator) :
    ∃ E : ActualEstimator,
      E.estimator = A.raw.normalize A.ce A.de ∧ E.value = A.value ∧
      (∀ L k (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool),
        E.actualComparison (matrixWord L k f) (numerator L k)) ∧
      (∀ word, E.estimator.tapeLength word = A.raw.tapeLength word) ∧
      (∀ word, ValidTable word → ∀ tape : Fin (A.raw.tapeLength word) → Bool,
        E.estimator.output word (List.ofFn tape) = A.raw.output word (List.ofFn tape)) ∧
      (∀ word, ValidTable word → ∀ P : List Bool → Prop,
        E.estimator.prob word P = A.raw.prob word P) := by
  obtain ⟨E, he, hv, hc, hp⟩ := extract_family A
    (fun x : Sample => matrixWord x.L x.k x.table)
    (fun x : Sample => numerator x.L x.k) 6 1
    (fun x => valid_table x.L x.k x.table)
    (fun x => midpoint_code_bound x.L x.k x.table)
  refine ⟨E, he, hv, ?_, ?_, ?_, hp⟩
  · intro L k f
    exact hc ⟨L, k, f⟩
  · intro word
    rw [he]
    rfl
  · intro word hword tape
    rw [he]
    exact A.raw.normalize_output_valid A.ce A.de word (entries word)
      (table_entries_le_length word) tape (A.estimator_clock word hword tape)

#print axioms midpoint_code_bound
#print axioms projection_outputs
#print axioms extract_all

end CurrentAdditive.V40RandomPermittedFamily
