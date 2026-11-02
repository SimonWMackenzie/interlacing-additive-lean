import CurrentAdditive.V39RecursiveTable
import CurrentAdditive.V39RoundedSample

/-! The exact final encoded sample on the actual fixed blocks of fair bits.
The semantic fixed-bit generator is total on every tape.  This file joins
its law to the exact current recursive evaluator, row-major table and
header, but does not claim an encoded-machine implementation or clock. -/

namespace CurrentAdditive.V39RoundedPrintedTable

open Paper2
open CurrentAdditive.V39RecursiveGenerator CurrentAdditive.V39RecursiveTable
open CurrentAdditive.V38OneStep
open EthInapproximability.CurrentPaper.EncodedCommunication

variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

abbrev Tape (k m : ℕ) := CurrentAdditive.RoundedDraw.BitBlocks
  (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
  (sampleDrawBudget p₀ q₁ q₂ s w Q k m)

def printedWord
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m B : ℕ) (bits : Tape n p₀ q₁ q₂ s w Q k m) :
    List Bool :=
  outputWord activity k m B (roundedLabels n p₀ q₁ q₂ s w Q hs hq₁ k m bits)

theorem printedWord_event_error_200
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m B : ℕ) (P : List Bool → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)).prob
        (fun bits => P (printedWord n p₀ q₁ q₂ s w Q activity hs hq₁ k m B bits)) -
      (sampleLaw n p₀ q₁ q₂ s w Q k m).toFiniteLaw.prob
        (fun labels => P (outputWord activity k m B labels))| ≤ (1 : ℝ) / 200 :=
  rounded_map_event_error_200 n p₀ q₁ q₂ s w Q hs hq₁ k m
    (outputWord activity k m B) P

/-- Every raw tape produces a valid square table with the announced
threshold, and each decoded entry is the exact current matrix value at the
same indexed sampled labels. Duplicate values retain their sample index. -/
theorem every_tape_exact
    (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m B : ℕ) (hm : 0 < m)
    (bits : Tape n p₀ q₁ q₂ s w Q k m) :
    let labels := roundedLabels n p₀ q₁ q₂ s w Q hs hq₁ k m bits
    let out := tableInstance activity k m B labels
    decodeInstance (printedWord n p₀ q₁ q₂ s w Q activity hs hq₁ k m B bits) = some out ∧
      out.rows = m ∧ out.cols = m ∧ out.threshold = B ∧
      out.table.length = m * m ∧
      (∀ i j : Fin m, (sampledTable activity k m labels).matrix i j =
        matrix activity k (labels.1 i) (labels.2 j)) := by
  intro labels out
  exact ⟨decode_outputWord activity k m B hm labels, rfl, rfl, rfl,
    (sampledTable activity k m labels).length, sampledTable_entry activity k m labels⟩

#print axioms printedWord_event_error_200
#print axioms every_tape_exact

end CurrentAdditive.V39RoundedPrintedTable
