import CurrentAdditive.V39ActualOutputMajority
import CurrentAdditive.V39DomainClockTotalization

/-!
Valid-table randomized estimators can use the same charged physical timeout
as the comparator. The fixed input-dependent tape count is preserved exactly;
the timeout is deterministic and reads no additional random bits. Valid-input
outputs, including inaccurate outputs, and all their event probabilities are
preserved. There is no assumed behavior on invalid input words.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39RandomEstimatorNormalization

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39DomainClockTotalization
open Paper2

/-- A finite randomized estimator with a fixed monomial tape schedule. Its
run guarantee is supplied only on valid tables below. -/
structure RawEstimator where
  cR : ℕ
  dR : ℕ
  machine : BitMachine.Machine
  output : List Bool → List Bool → List Bool

def RawEstimator.tapeLength (A : RawEstimator) (word : List Bool) : ℕ :=
  A.cR * (word.length + 1) ^ A.dR

def RawEstimator.prob (A : RawEstimator) (word : List Bool)
    (P : List Bool → Prop) : ℝ :=
  (Unit4Shell.Definitions.uniformTape (A.tapeLength word)).prob
    (fun tape => P (A.output word (List.ofFn tape)))

theorem RawEstimator.pair_length_bound (A : RawEstimator) (word : List Bool)
    (tape : Fin (A.tapeLength word) → Bool) :
    (pair word (List.ofFn tape)).length + 1 ≤
      (A.cR + 4) * (word.length + 1) ^ (A.dR + 1) := by
  let N := word.length + 1
  let X := N ^ (A.dR + 1)
  have hN : 1 ≤ N := by omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hN
  have hpow : N ^ A.dR ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hn : N ≤ X := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ X := Nat.pow_le_pow_right hN (by omega)
  have hr := Nat.mul_le_mul_left A.cR hpow
  rw [pair_length, List.length_ofFn]
  change 2 * word.length + 1 + A.cR * N ^ A.dR + 1 ≤ (A.cR + 4) * X
  have he : (A.cR + 4) * X = A.cR * X + 4 * X := by ring
  rw [he]
  omega

/-- One all-input physically clocked estimator, using the original random
tape schedule and the existing charged timeout machine. -/
def RawEstimator.normalize (A : RawEstimator) (c d : ℕ) : SelectedTape.Algorithm :=
  let degree := c + d
  let a := GeneralPolynomialClock.timeCoefficient degree A.machine
  let b := GeneralPolynomialClock.exponent degree
  { cR := A.cR
    dR := A.dR
    cT := a * (A.cR + 4) ^ b
    dT := (A.dR + 1) * b
    machine := GeneralPolynomialClock.machine degree A.machine
    output := fun word tape =>
      GeneralPolynomialClock.result degree A.machine (pair word tape)
    runs := by
      intro word tape
      apply BitMachine.outputsWithin_mono _
        (GeneralPolynomialClock.outputs_all degree A.machine (pair word (List.ofFn tape)))
      have ht := GeneralPolynomialClock.time_le degree A.machine
        (pair word (List.ofFn tape))
      refine ht.trans ?_
      have hl := Nat.mul_le_mul_left a
        (Nat.pow_le_pow_left (A.pair_length_bound word tape) b)
      simpa only [mul_pow, ← pow_mul, Nat.mul_assoc] using hl }

theorem RawEstimator.normalize_tapeLength (A : RawEstimator) (c d : ℕ)
    (word : List Bool) : (A.normalize c d).tapeLength word = A.tapeLength word := rfl

/-- A table-size bound on valid runs is enough: the full table is contained
in the physical pair input. Inaccurate valid runs are preserved as well. -/
theorem RawEstimator.normalize_output_valid (A : RawEstimator) (c d : ℕ)
    (word : List Bool) (T : ℕ) (hsize : T ≤ word.length)
    (tape : Fin (A.tapeLength word) → Bool)
    (hrun : A.machine.OutputsWithin (pair word (List.ofFn tape))
      (A.output word (List.ofFn tape)) (c * (T + 1) ^ d)) :
    (A.normalize c d).output word (List.ofFn tape) = A.output word (List.ofFn tape) := by
  have hlen : T ≤ (pair word (List.ofFn tape)).length := by
    rw [pair_length]
    omega
  have hbound : c * (T + 1) ^ d ≤
      GeneralPolynomialFuelPrefix.clockLength (degree := c + d)
        (pair word (List.ofFn tape)) :=
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_left
      (Nat.add_le_add_right hlen 1) d)).trans
        (polynomial_le_written_fuel c d (pair word (List.ofFn tape)).length)
  have hs := GeneralPolynomialClock.outputs_valid (c + d) A.machine
    (pair word (List.ofFn tape)) (A.output word (List.ofFn tape))
      (BitMachine.outputsWithin_mono _ hrun hbound)
  exact BitMachine.outputsWithin_unique (GeneralPolynomialClock.machine (c + d) A.machine)
    (GeneralPolynomialClock.outputs_all (c + d) A.machine (pair word (List.ofFn tape))) hs

/-- Exact preservation of every output event at each valid word. No loss in
success probability, tape padding, or additional independent randomness. -/
theorem RawEstimator.normalize_prob_valid (A : RawEstimator) (c d : ℕ)
    (word : List Bool) (T : ℕ) (hsize : T ≤ word.length)
    (hrun : ∀ tape : Fin (A.tapeLength word) → Bool,
      A.machine.OutputsWithin (pair word (List.ofFn tape))
        (A.output word (List.ofFn tape)) (c * (T + 1) ^ d))
    (P : List Bool → Prop) :
    (A.normalize c d).prob word P = A.prob word P := by
  change (Unit4Shell.Definitions.uniformTape (A.tapeLength word)).prob
      (fun tape => P ((A.normalize c d).output word (List.ofFn tape))) = _
  have he : (fun tape : Fin (A.tapeLength word) → Bool =>
      P ((A.normalize c d).output word (List.ofFn tape))) =
      (fun tape => P (A.output word (List.ofFn tape))) := by
    funext tape
    rw [A.normalize_output_valid c d word T hsize tape (hrun tape)]
  rw [he]
  rfl

#print axioms RawEstimator.normalize
#print axioms RawEstimator.normalize_tapeLength
#print axioms RawEstimator.normalize_output_valid
#print axioms RawEstimator.normalize_prob_valid

end CurrentAdditive.V39RandomEstimatorNormalization
