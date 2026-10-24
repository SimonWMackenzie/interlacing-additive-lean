import CurrentAdditive.GeneralRationalEndpoint

/-!
Raw physical comparison adapter, with NO numerical correctness requirement.
Runtime is total on all words. A numerical consumer must prove correctness
only for the actual estimator outputs that it uses, including inaccurate
runs. This generalizes the physical part of the stronger frozen interface;
the full matrix/threshold frame is retained. The existing medAlgJudge
machine already supplies exactly pair(full word,out). No table stripping
or new physical majority program is used.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39FramedComparator

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open Paper2.AModel (PrefixAlgorithm)

/-- The physical part of a permitted comparator. No numerical value map,
output validity test, or correctness on unreachable words is assumed. -/
structure FramedComparator where
  output : List Bool → Bool
  physical : BitMachine.Polytime (fun input => [output input])

def FramedComparator.judge (R : FramedComparator)
    (word out : List Bool) : Bool := R.output (pair word out)

/-- The original matrix and threshold frame is retained, so the comparator
clock may use time polynomial in the full table even for short outputs. -/
theorem FramedComparator.judge_pair (R : FramedComparator)
    (word out : List Bool) : R.judge word out = R.output (pair word out) := rfl

private theorem composedPoly (R : FramedComparator) :
    BitMachine.Polytime (fun input => [R.output input]) := R.physical

def comparisonMachine (R : FramedComparator) : Machine :=
  Classical.choose (composedPoly R)

private def cmpC (R : FramedComparator) : ℕ :=
  Classical.choose (Classical.choose_spec (composedPoly R))
private def cmpD (R : FramedComparator) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (composedPoly R)))

theorem comparisonRun (R : FramedComparator) (input : List Bool) :
    (comparisonMachine R).OutputsWithin input [R.output input]
      (cmpC R * (input.length + 1) ^ cmpD R) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (composedPoly R))) input

private def estC (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ := Classical.choose hA
private def estD (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ :=
  Classical.choose (Classical.choose_spec hA)
private theorem estBounds (A : PrefixAlgorithm) (hA : A.Polynomial) (word : List Bool) :
    A.tapeLength word.length ≤ estC A hA * (word.length + 1) ^ estD A hA ∧
      A.time word ≤ estC A hA * (word.length + 1) ^ estD A hA :=
  Classical.choose_spec (Classical.choose_spec hA) word

private def clockK (A : PrefixAlgorithm) (hA : A.Polynomial) : ℕ :=
  5 + estC A hA + estC A hA * A.machine.pushBound

def compareClock (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : FramedComparator) (word : List Bool) : ℕ :=
  cmpC R * (clockK A hA * (word.length + 1) ^ (estD A hA + 1)) ^ cmpD R

theorem compareClock_poly (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : FramedComparator) :
    ∃ c d : ℕ, ∀ word : List Bool,
      compareClock A hA R word ≤ c * (word.length + 1) ^ d := by
  refine ⟨cmpC R * (clockK A hA) ^ cmpD R, (estD A hA + 1) * cmpD R, ?_⟩
  intro word
  simp only [compareClock]
  rw [mul_pow]
  simp only [← pow_mul, Nat.mul_assoc]
  exact le_rfl

private theorem clock_covers (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : FramedComparator) (word out : List Bool)
    (hout : out.length ≤ Paper2.MedianOwner.Med.outBound A.machine word.length
      (A.tapeLength word.length) (A.time word)) :
    cmpC R * ((pair word out).length + 1) ^ cmpD R ≤ compareClock A hA R word := by
  let N := word.length + 1
  let X := N ^ (estD A hA + 1)
  have hN : 1 ≤ N := by omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hN
  have hpow : N ^ estD A hA ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hwplus : word.length + 1 ≤ X := by
    calc word.length + 1 = N := rfl
      _ = N ^ 1 := (pow_one N).symm
      _ ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hs := (estBounds A hA word).1
  have ht := (estBounds A hA word).2
  have hsX : A.tapeLength word.length ≤ estC A hA * X :=
    hs.trans (Nat.mul_le_mul_left _ hpow)
  have htX : A.time word ≤ estC A hA * X :=
    ht.trans (Nat.mul_le_mul_left _ hpow)
  have hpush := Nat.mul_le_mul_right A.machine.pushBound htX
  have hlength : (pair word out).length + 1 ≤ clockK A hA * X := by
    rw [pair_length]
    unfold Paper2.MedianOwner.Med.outBound at hout
    have he : clockK A hA * X =
        5 * X + estC A hA * X + estC A hA * X * A.machine.pushBound := by
      unfold clockK
      ring
    rw [he]
    omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlength (cmpD R))

/-- The all-word physical specification needed by the existing medAlgJudge.
Its output is just R's supplied bit on the full framed input. There is no
assumed numerical meaning for arbitrary estimator output words. -/
theorem comparisonSpec (A : PrefixAlgorithm) (hA : A.Polynomial)
    (R : FramedComparator) :
    CmpSpecJudge A (comparisonMachine R) R.judge (compareClock A hA R) := by
  intro word out hout
  exact outputsWithin_mono _ (comparisonRun R (pair word out))
    (clock_covers A hA R word out hout)

#print axioms FramedComparator.judge_pair
#print axioms comparisonRun
#print axioms compareClock_poly
#print axioms comparisonSpec

end CurrentAdditive.V39FramedComparator
