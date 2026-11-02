import Paper2.BindMachine
import Paper2.A4PolyIn

/-!
# Uniform monomial clock for the physical two-stage bind

Every intermediate word is bounded from A's actual selected-tape run, the
fixed outer tape, and B's selected tape envelope. The split, pair-map,
truncation, B run, and three composition transfers are all included.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace Paper2.SelectedTape.Bind

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2.Unit4Shell.Poly

def inputSize (A B : Algorithm) (n : ℕ) : ℕ :=
  2 * n + 1 + outerLength A B n
def firstPairSize (A B : Algorithm) (n : ℕ) : ℕ :=
  2 * n + 1 + outerLength A B n
def mid1Size (A B : Algorithm) (n : ℕ) : ℕ :=
  2 * firstPairSize A B n + 1 + outerLength A B n
def mid2Size (A B : Algorithm) (n : ℕ) : ℕ :=
  2 * sourceBound A n + 1 + outerLength A B n
def mid3Size (A B : Algorithm) (n : ℕ) : ℕ :=
  2 * sourceBound A n + 1 + classifierBlock A B n
def stage1Bound (A B : Algorithm) (n : ℕ) : ℕ :=
  Retain.timeBound A.cR A.dR idC idD idMachine.pushBound (inputSize A B n)
def stage2Bound (A B : Algorithm) (n : ℕ) : ℕ :=
  2 * firstPairSize A B n + A.cT * (n + 1) ^ A.dT +
    2 * sourceBound A n + 6
def stage3Bound (A B : Algorithm) (n : ℕ) : ℕ :=
  NPOwner1.Trunc.timeBound B.cR B.dR idC idD idMachine.pushBound (mid2Size A B n)
def stage4Bound (A B : Algorithm) (n : ℕ) : ℕ :=
  B.cT * (sourceBound A n + 1) ^ B.dT
def fullBound (A B : Algorithm) (n : ℕ) : ℕ :=
  stage1Bound A B n + 2 * mid1Size A B n + 2 +
    (stage2Bound A B n + 2 * mid2Size A B n + 2 +
      (stage3Bound A B n + 2 * mid3Size A B n + 2 +
        stage4Bound A B n))

private theorem truncTime_mono (c d cf df pb : ℕ) {m n : ℕ} (h : m ≤ n) :
    NPOwner1.Trunc.timeBound c d cf df pb m ≤
      NPOwner1.Trunc.timeBound c d cf df pb n := by
  unfold NPOwner1.Trunc.timeBound
  gcongr

private theorem sourceWord_le (A B : Algorithm) (x : List Bool)
    (t : Fin (outerLength A B x.length) → Bool) :
    (sourceWord A x (List.ofFn t)).length ≤ sourceBound A x.length := by
  let outer := List.ofFn t
  have hlen : A.tapeLength x ≤ outer.length := by
    have h := needed_le_outer A B x.length
    simp [outer, Algorithm.tapeLength] at *
    omega
  let first := prefixFn outer (A.tapeLength x) hlen
  have heq : List.ofFn first = firstWord A x outer :=
    ofFn_prefixFn outer (A.tapeLength x) hlen
  have h := source_output_length A x first
  simpa [sourceWord, heq] using h

theorem clock_le_fullBound (A B : Algorithm) (x : List Bool)
    (t : Fin (outerLength A B x.length) → Bool) :
    clock A B x (List.ofFn t) ≤ fullBound A B x.length := by
  let outer := List.ofFn t
  have houter : outer.length = outerLength A B x.length := List.length_ofFn
  have hfirst : (firstWord A x outer).length ≤ outerLength A B x.length := by
    simp [firstWord, List.length_take, houter]
  have hrest : (restWord A x outer).length ≤ outerLength A B x.length := by
    simp [restWord, List.length_drop, houter]
  have hy : (sourceWord A x outer).length ≤ sourceBound A x.length :=
    sourceWord_le A B x t
  have hsecond : (secondWord A B x outer).length ≤ classifierBlock A B x.length := by
    have h1 : (secondWord A B x outer).length ≤
        B.tapeLength (sourceWord A x outer) := by
      simp [secondWord, List.length_take]
    have h2 : B.tapeLength (sourceWord A x outer) ≤ classifierBlock A B x.length := by
      change B.cR * ((sourceWord A x outer).length + 1) ^ B.dR ≤
        B.cR * (sourceBound A x.length + 1) ^ B.dR
      gcongr
    exact h1.trans h2
  have hmid1 : (mid1 A x outer).length ≤ mid1Size A B x.length := by
    simp [mid1, mid1Size, firstPairSize, pair_length]
    omega
  have hmid2 : (mid2 A x outer).length ≤ mid2Size A B x.length := by
    simp [mid2, mid2Size, pair_length]
    omega
  have hmid3 : (mid3 A B x outer).length ≤ mid3Size A B x.length := by
    simp [mid3, mid3Size, pair_length]
    omega
  have hstage1 : splitClock A (pair x outer) = stage1Bound A B x.length := by
    simp [splitClock, stage1Bound, inputSize, pair_length, houter]
  have hstage2 : stage2Clock A x outer ≤ stage2Bound A B x.length := by
    simp [stage2Clock, stage2Bound, firstPairSize, pair_length]
    omega
  have hstage3 : stage3Clock A B x outer ≤ stage3Bound A B x.length :=
    truncTime_mono B.cR B.dR idC idD idMachine.pushBound hmid2
  have hstage4 : stage4Clock A B x outer ≤ stage4Bound A B x.length := by
    unfold stage4Clock stage4Bound
    gcongr
  change clock A B x outer ≤ fullBound A B x.length
  unfold clock fullBound
  omega

private theorem expression_poly (A B : Algorithm) : PolyIn id (inputSize A B) ∧
    PolyIn id (firstPairSize A B) ∧ PolyIn id (mid1Size A B) ∧
    PolyIn id (mid2Size A B) ∧ PolyIn id (mid3Size A B) := by
  have houter : PolyIn id (outerLength A B) := by
    unfold outerLength
    exact mul (const _) (pow (add self (const 1)) (outerD A B))
  have hsource := sourceBound_poly A
  have hclass := classifierBlock_poly A B
  constructor
  · unfold inputSize
    exact add (add (mul (const 2) self) (const 1)) houter
  constructor
  · unfold firstPairSize
    exact add (add (mul (const 2) self) (const 1)) houter
  constructor
  · unfold mid1Size firstPairSize
    exact add (add (mul (const 2)
      (add (add (mul (const 2) self) (const 1)) houter)) (const 1)) houter
  constructor
  · unfold mid2Size
    exact add (add (mul (const 2) hsource) (const 1)) houter
  · unfold mid3Size
    exact add (add (mul (const 2) hsource) (const 1)) hclass

theorem fullBound_poly (A B : Algorithm) : PolyIn id (fullBound A B) := by
  obtain ⟨hinput, hfirst, hmid1, hmid2, hmid3⟩ := expression_poly A B
  have hretRaw : PolyIn id (fun N =>
      Retain.timeBound A.cR A.dR idC idD idMachine.pushBound N) :=
    split_clock_poly A
  have htruncRaw : PolyIn id (fun N =>
      NPOwner1.Trunc.timeBound B.cR B.dR idC idD idMachine.pushBound N) := by
    unfold NPOwner1.Trunc.timeBound
    repeat (first
      | exact self
      | exact const _
      | apply add
      | apply mul
      | apply pow)
  have hstage1 : PolyIn id (stage1Bound A B) := by
    exact transfer hinput ⟨_, _, fun n => (Classical.choose_spec
      (Classical.choose_spec hretRaw)) (inputSize A B n)⟩
  have hstage3 : PolyIn id (stage3Bound A B) := by
    exact transfer hmid2 ⟨_, _, fun n => (Classical.choose_spec
      (Classical.choose_spec htruncRaw)) (mid2Size A B n)⟩
  unfold fullBound stage2Bound stage4Bound
  repeat (first
    | exact hstage1
    | exact hstage3
    | exact hfirst
    | exact hmid1
    | exact hmid2
    | exact hmid3
    | exact sourceBound_poly A
    | exact self
    | exact const _
    | apply add
    | apply mul
    | apply pow)

#print axioms clock_le_fullBound
#print axioms fullBound_poly

end Paper2.SelectedTape.Bind
