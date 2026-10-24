import CurrentAdditive.CanonicalAmbientDimensionsFull
import CurrentAdditive.CanonicalAmbientThresholdFull

noncomputable section
namespace CurrentAdditive.V39ScalarSetup

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open Paper2.YaoMachine

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def selectorWords (t H : ℕ) : Fin 12 → List Bool :=
  Function.update (CanonicalSelectorBankPower.initial H) 1
    (List.replicate (H ^ (2 ^ (t - 1))) true)

def squareWords (d : ℕ) : Fin 9 → List Bool :=
  Function.update (Function.update (CanonicalFieldSquare.initial d) 2
    (List.replicate 4 true)) 3 (List.replicate ((2 ^ d) ^ 2) true)

def dimensionWords (t v H d : ℕ) : Fin 11 → List Bool :=
  Function.update (Function.update (Function.update
    (CanonicalDimensionsMultiply.initial v (H ^ (2 ^ (t - 1))) H
      ((2 ^ d) ^ 2) (2 ^ (t - 1))) 5
      (List.replicate (v * H ^ (2 ^ (t - 1))) true)) 6
      (List.replicate (2 ^ (t - 1) * H) true)) 7
      (List.replicate (2 ^ (t - 1) * H * (2 ^ d) ^ 2) true)

def thresholdWords (t b : ℕ) : Fin 3 → List Bool :=
  Function.update (CanonicalThreshold.initial b) 1
    (List.replicate (2 * b + 4 * t + 2) true)

def afterSelector (t H : ℕ) (S : Cell t 16 → List Bool) : Cell t 16 → List Bool
  | .selector i => selectorWords t H i
  | k => S k

def afterSquare (t d : ℕ) (S : Cell t 16 → List Bool) : Cell t 16 → List Bool
  | .square i => squareWords d i
  | k => S k

def afterDimensions (t v H d : ℕ) (S : Cell t 16 → List Bool) : Cell t 16 → List Bool
  | .dimensions i => dimensionWords t v H d i
  | k => S k

def afterThreshold (t b : ℕ) (S : Cell t 16 → List Bool) : Cell t 16 → List Bool
  | .threshold i => thresholdWords t b i
  | k => S k

def scalarOutput (t v b H d : ℕ) (S : Cell t 16 → List Bool) :=
  afterThreshold t b (afterDimensions t v H d
    (afterSquare t d (afterSelector t H S)))

theorem selector_bank_eq (t H : ℕ) (S : Cell t 16 → List Bool) :
    bank (selectorEmbed t 16) (selectorInputBank t 16 H S) (selectorWords t H) =
      afterSelector t H S := by
  funext k
  cases k <;> first
    | exact bank_at _ _ _ _
    | rw [bank_outside _ _ _ _ (by simp [selectorEmbed])]
      simp [selectorInputBank, afterSelector]

theorem square_bank_eq (t d : ℕ) (S : Cell t 16 → List Bool) :
    bank (squareEmbed t 16) (squareInputBank t 16 d S) (squareWords d) =
      afterSquare t d S := by
  funext k
  cases k <;> first
    | exact bank_at _ _ _ _
    | rw [bank_outside _ _ _ _ (by simp [squareEmbed])]
      simp [squareInputBank, afterSquare]

theorem dimensions_bank_eq (t v H d : ℕ) (S : Cell t 16 → List Bool) :
    bank (dimensionsEmbed t 16)
      (dimensionPrepared t v (H ^ (2 ^ (t - 1))) H ((2 ^ d) ^ 2) S)
      (dimensionWords t v H d) = afterDimensions t v H d S := by
  funext k
  cases k <;> first
    | exact bank_at _ _ _ _
    | rw [bank_outside _ _ _ _ (by simp [dimensionsEmbed])]
      simp [dimensionPrepared, CopyFill.fill, dimensionJobs, afterDimensions]

theorem threshold_bank_eq (t b : ℕ) (S : Cell t 16 → List Bool) :
    bank (thresholdEmbed t 16) (thresholdInputBank t 16 b S) (thresholdWords t b) =
      afterThreshold t b S := by
  funext k
  cases k <;> first
    | exact bank_at _ _ _ _
    | rw [bank_outside _ _ _ _ (by simp [thresholdEmbed])]
      simp [thresholdInputBank, afterThreshold]

theorem scalarOutput_values (t v b H d : ℕ) (S : Cell t 16 → List Bool) :
    scalarOutput t v b H d S (.selector 1) = List.replicate (H ^ (2 ^ (t - 1))) true ∧
    scalarOutput t v b H d S (.square 3) = List.replicate ((2 ^ d) ^ 2) true ∧
    scalarOutput t v b H d S (.dimensions 5) =
      List.replicate (v * H ^ (2 ^ (t - 1))) true ∧
    scalarOutput t v b H d S (.dimensions 7) =
      List.replicate (2 ^ (t - 1) * H * (2 ^ d) ^ 2) true ∧
    scalarOutput t v b H d S (.threshold 1) =
      List.replicate (2 * b + 4 * t + 2) true := by
  simp [scalarOutput, afterSelector, afterSquare, afterDimensions,
    afterThreshold, selectorWords, squareWords, dimensionWords, thresholdWords]

theorem scalarOutput_foreign (t v b H d : ℕ) (S : Cell t 16 → List Bool)
    (k : Cell t 16)
    (hsel : ∀ i, k ≠ .selector i) (hsq : ∀ i, k ≠ .square i)
    (hdim : ∀ i, k ≠ .dimensions i) (hthr : ∀ i, k ≠ .threshold i) :
    scalarOutput t v b H d S k = S k := by
  cases k <;> simp_all [scalarOutput, afterThreshold, afterDimensions,
    afterSquare, afterSelector]

#print axioms selector_bank_eq
#print axioms square_bank_eq
#print axioms dimensions_bank_eq
#print axioms threshold_bank_eq
#print axioms scalarOutput_values
#print axioms scalarOutput_foreign

end CurrentAdditive.V39ScalarSetup
