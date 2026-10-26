import CurrentAdditive.V39ScalarBank

noncomputable section
namespace CurrentAdditive.V39ScalarSetup

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open Paper2.YaoMachine

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def selectorControl : Option Bool × (Unit × (Option Bool × (Bool × Bool))) :=
  (none, ((), (none, (false, false))))
def squareControl : Option Bool × (Option Bool × (Unit × (Unit × (Bool × Bool)))) :=
  (none, (none, ((), ((), (false, false)))))
def dimensionsControl := ((MultiMove.initial, ()), (false, (false, false)))
def thresholdControl : Option Bool × (Option Bool × (Option Bool × Unit)) :=
  (none, (none, (none, ())))

def selectorSquareProgram (t : ℕ) :=
  BitMachineRawSequence.program (selectorFullProgram t 16)
    (squareFullProgram t 16 (by decide))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    selectorControl squareControl

def selectorSquareDimensionsProgram (t : ℕ) :=
  BitMachineRawSequence.program (selectorSquareProgram t) (dimensionsFullProgram t)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob))))
    (selectorControl, squareControl) dimensionsControl

/-- One fixed raw program. Only t determines its instruction table and finite
control; v,b,H,d occur in the input words and in its proved clock. -/
def scalarProgram (t : ℕ) :=
  BitMachineRawSequence.program (selectorSquareDimensionsProgram t)
    (thresholdFullProgram t 16)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((selectorControl, squareControl), dimensionsControl) thresholdControl

def selectorBudget (t H : ℕ) : ℕ :=
  (2 * H + 2) + ((2 ^ (t - 1) + 1) +
    (MatrixWeightedPower.powerBound H (2 ^ (t - 1)) + 2) + 1) + 1

def squareBudget (d : ℕ) : ℕ :=
  (2 * d + 2) + ((2 * d + 2) + 5 + 2 +
    MatrixWeightedPower.powerBound 4 d + 3) + 1

def dimensionCopyBudget (v cap H R2 : ℕ) : ℕ :=
  (2 * v + 2) + (2 * cap + 2) + (2 * H + 2) + (2 * R2 + 2)

def dimensionsBudget (t v H d : ℕ) : ℕ :=
  dimensionCopyBudget v (H ^ (2 ^ (t - 1))) H ((2 ^ d) ^ 2) + 1 +
    (2 ^ (t - 1) + 1) + 1 +
    (MatrixAddressMachine.exactTime v (H ^ (2 ^ (t - 1))) 0 +
      MatrixAddressMachine.exactTime (2 ^ (t - 1)) H 0 +
      MatrixAddressMachine.exactTime (2 ^ (t - 1) * H) ((2 ^ d) ^ 2) 0 + 2) + 1

def thresholdBudget (t b : ℕ) : ℕ :=
  (2 * b + 2) + (2 * (2 * b + 2) + (4 * t + 3) + 2) + 1

def scalarBudget (t v b H d : ℕ) : ℕ :=
  selectorBudget t H + squareBudget d + dimensionsBudget t v H d +
    thresholdBudget t b + 3

theorem dimension_fill_cost (t v H d : ℕ) (S : Cell t 16 → List Bool)
    (hv : S (.source (sN 3)) = List.replicate v true)
    (hH : S (.source (sN 6)) = List.replicate H true) :
    CopyFill.fillCost (dimensionJobs t)
      (afterSquare t d (afterSelector t H S)) =
      dimensionCopyBudget v (H ^ (2 ^ (t - 1))) H ((2 ^ d) ^ 2) := by
  simp [CopyFill.fillCost, dimensionJobs, afterSquare, afterSelector,
    selectorWords, squareWords, hv, hH, dimensionCopyBudget] <;> ring

/-- Actual scalar setup from arbitrary prepared input stacks. All four local
scratch summands must be empty, and the shared copy temporary is empty.
Every other bank, including source, degree, both widths, field, writer and
header, is preserved by the complete output-bank equality. -/
theorem physical_scalar_setup (t v b H d : ℕ) (S : Cell t 16 → List Bool)
    (hv : S (.source (sN 3)) = List.replicate v true)
    (hb : S (.source (sN 5)) = List.replicate b true)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hd : S (.degree 3) = List.replicate d true)
    (hselector : ∀ i, S (.selector i) = [])
    (hsquare : ∀ i, S (.square i) = [])
    (hdimensions : ∀ i, S (.dimensions i) = [])
    (hthreshold : ∀ i, S (.threshold i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ scalarBudget t v b H d,
      ((advance (scalarProgram t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
            BitMachineCopy.Label.scan)))),
          (((selectorControl, squareControl), dimensionsControl), thresholdControl), S⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (((selectorControl, squareControl), dimensionsControl), thresholdControl),
          scalarOutput t v b H d S⟩ := by
  obtain ⟨u, hu, hsel⟩ := physical_selector_full t 16 H S hH hselector hscratch
  have hsel' : ((advance (selectorFullProgram t 16))^[u])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        selectorControl, S⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, selectorControl, afterSelector t H S⟩ := by
    rw [← selector_bank_eq]
    exact hsel
  obtain ⟨w, hw, hsq⟩ := physical_square_full t 16 d (by decide)
    (afterSelector t H S)
    (by simpa [afterSelector] using hd)
    (by intro i; simpa [afterSelector] using hsquare i)
    (by simpa [afterSelector] using hscratch)
  have hsq' : ((advance (squareFullProgram t 16 (by decide)))^[w])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        squareControl, afterSelector t H S⟩ : TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, squareControl, afterSquare t d (afterSelector t H S)⟩ := by
    rw [← square_bank_eq]
    exact hsq
  obtain ⟨a, ha, hpair⟩ := BitMachineRawSequence.runs
    (selectorFullProgram t 16) (squareFullProgram t 16 (by decide))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    selectorControl selectorControl squareControl squareControl
    S (afterSelector t H S) _ u w hsel' hsq'
  obtain ⟨z, hz, hdim⟩ := physical_dimensions_full t v (H ^ (2 ^ (t - 1))) H
    ((2 ^ d) ^ 2) (afterSquare t d (afterSelector t H S))
    (by intro i; simpa [afterSquare, afterSelector] using hdimensions i)
    (by simpa [afterSquare, afterSelector] using hscratch)
    (by simpa [afterSquare, afterSelector] using hv)
    (by simp [afterSquare, afterSelector, selectorWords])
    (by simpa [afterSquare, afterSelector] using hH)
    (by simp [afterSquare, squareWords])
  have hdim' : ((advance (dimensionsFullProgram t))^[z])
      (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob)))),
        dimensionsControl, afterSquare t d (afterSelector t H S)⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, dimensionsControl,
        afterDimensions t v H d (afterSquare t d (afterSelector t H S))⟩ := by
    rw [← dimensions_bank_eq]
    exact hdim
  obtain ⟨c, hc, htriple⟩ := BitMachineRawSequence.runs
    (selectorSquareProgram t) (dimensionsFullProgram t)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob))))
    (selectorControl, squareControl) (selectorControl, squareControl)
    dimensionsControl dimensionsControl
    S (afterSquare t d (afterSelector t H S)) _ a z hpair hdim'
  obtain ⟨r, hr, hthr⟩ := physical_threshold_full t 16 b
    (afterDimensions t v H d (afterSquare t d (afterSelector t H S)))
    (by simpa [afterDimensions, afterSquare, afterSelector] using hb)
    (by intro i; simpa [afterDimensions, afterSquare, afterSelector] using hthreshold i)
    (by simpa [afterDimensions, afterSquare, afterSelector] using hscratch)
  have hthr' : ((advance (thresholdFullProgram t 16))^[r])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        thresholdControl,
        afterDimensions t v H d (afterSquare t d (afterSelector t H S))⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, thresholdControl, scalarOutput t v b H d S⟩ := by
    rw [scalarOutput, ← threshold_bank_eq]
    exact hthr
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (selectorSquareDimensionsProgram t) (thresholdFullProgram t 16)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((selectorControl, squareControl), dimensionsControl)
    ((selectorControl, squareControl), dimensionsControl)
    thresholdControl thresholdControl
    S (afterDimensions t v H d (afterSquare t d (afterSelector t H S))) _ c r htriple hthr'
  change u ≤ selectorBudget t H at hu
  change w ≤ squareBudget d at hw
  change r ≤ thresholdBudget t b at hr
  rw [dimension_fill_cost t v H d S hv hH] at hz
  change z ≤ dimensionsBudget t v H d at hz
  exact ⟨steps, by unfold scalarBudget; omega, hrun⟩

#print axioms dimension_fill_cost
#print axioms physical_scalar_setup

end CurrentAdditive.V39ScalarSetup
