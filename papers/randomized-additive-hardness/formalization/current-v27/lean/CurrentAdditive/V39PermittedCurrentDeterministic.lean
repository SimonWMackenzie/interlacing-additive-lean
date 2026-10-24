import CurrentAdditive.V39PermittedDeterministicExtraction
import CurrentAdditive.V39PublicHeaderBound

/-! Discharge numerical-request validity for the actual current
deterministic graph constructor. Its midpoint's code has at most
64(T+1)^2 bits, where T is the entry count of the same padded table. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedCurrentDeterministic

open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39PermittedNumericalExtraction
open CurrentAdditive.V39PermittedDeterministicExtraction
open CurrentAdditive.V39FramedNumerical
open CurrentAdditive.Eventual (entries)
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open CurrentAdditive.LiteralEdgeEncoder

theorem actual_entries (R : StoredMatrix) :
    entries R.squareWord = (Paper2.SquarePadding.side R.rows R.cols) ^ 2 := by
  unfold entries
  rw [R.squareWord_decodes]
  simp only [pow_two]

theorem actual_midpoint_code_length (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    (rationalCode ((2 * publicGraphThreshold p n m hn hlow hdegree k + k : ℕ) : ℤ) 1).length ≤
      64 * (entries (publicGraphWord p hn hlow hdegree edge k) + 1) ^ 2 := by
  have hb := (publicGraphRun_header_bounds p hn hlow hdegree edge k).2.2
  have hentries : entries (publicGraphWord p hn hlow hdegree edge k) =
      (Paper2.SquarePadding.side
        (publicGraphRun p hn hlow hdegree edge k).rows
        (publicGraphRun p hn hlow hdegree edge k).cols) ^ 2 :=
    actual_entries _
  have hm : 2 * publicGraphThreshold p n m hn hlow hdegree k + k ≤
      31 * (entries (publicGraphWord p hn hlow hdegree edge k) + 1) ^ 2 := by
    rw [hentries]
    exact hb.trans (Nat.mul_le_mul_left 31
      (Nat.pow_le_pow_left (by omega) 2))
  exact code_length_of_numerator_bound _ _ 31 2 hm

/-- One uniform physical estimator/comparator pair is sufficient for all
iterations of this actual table constructor. The actual numerical comparison
is derived from the paper's permitted comparison convention, with no
source-specific request assumption and no NO/cost premise. -/
theorem extract_actual_constructor (A : PermittedDeterministicEstimator)
    (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n)
    (edge : Fin m → Bool → Fin n) :
    ∃ E : Estimator, E.value = A.value ∧
      (∀ word, ValidTable word → E.output word = A.output word) ∧
      (∀ k, ComparisonAt E (publicGraphWord p hn hlow hdegree edge k)
        (2 * publicGraphThreshold p n m hn hlow hdegree k + k)) := by
  exact V39PermittedDeterministicExtraction.extract_family A
    (publicGraphWord p hn hlow hdegree edge)
    (fun k => 2 * publicGraphThreshold p n m hn hlow hdegree k + k) 64 2
    (fun k => valid_of_target (publicGraphWord_target p hn hlow hdegree edge k))
    (actual_midpoint_code_length p hn hlow hdegree edge)

/-- Concrete inputs of the current constructor. This packages only the
already required graph-size conditions; it contains no promise, protocol,
profile, success certificate or numerical-comparison premise. -/
structure CurrentGraphInput where
  constants : SourceConstants
  vertices : ℕ
  edges : ℕ
  nonempty : 0 < vertices
  lower : vertices ≤ 2 * edges
  degree : 2 * edges ≤ constants.degree * vertices
  edge : Fin edges → Bool → Fin vertices
  rounds : ℕ

def CurrentGraphInput.word (x : CurrentGraphInput) : List Bool :=
  publicGraphWord x.constants x.nonempty x.lower x.degree x.edge x.rounds

def CurrentGraphInput.midpoint (x : CurrentGraphInput) : ℕ :=
  2 * publicGraphThreshold x.constants x.vertices x.edges x.nonempty
    x.lower x.degree x.rounds + x.rounds

/-- Quantifiers matter: one physical estimator/comparator pair serves all
graphs, sizes, constants and iteration counts in the actual constructor.
Its uniform clock is independent of these inputs. -/
theorem extract_all_actual_constructors (A : PermittedDeterministicEstimator) :
    ∃ E : Estimator, E.value = A.value ∧
      (∀ word, ValidTable word → E.output word = A.output word) ∧
      ∀ x : CurrentGraphInput, ComparisonAt E x.word x.midpoint := by
  exact V39PermittedDeterministicExtraction.extract_family A
    CurrentGraphInput.word CurrentGraphInput.midpoint 64 2
    (fun x => valid_of_target (publicGraphWord_target x.constants
      x.nonempty x.lower x.degree x.edge x.rounds))
    (fun x => actual_midpoint_code_length x.constants
      x.nonempty x.lower x.degree x.edge x.rounds)

#print axioms actual_entries
#print axioms actual_midpoint_code_length
#print axioms extract_actual_constructor
#print axioms extract_all_actual_constructors

end CurrentAdditive.V39PermittedCurrentDeterministic
