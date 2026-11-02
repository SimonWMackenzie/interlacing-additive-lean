import CurrentAdditive.V39RoundedSample
import CurrentAdditive.V39DrawGrowth

namespace CurrentAdditive.V39RecursiveGenerator

open Paper2
open CurrentAdditive.V38OneStep

section Table
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

/-- All intersections of the same two stored ordered samples. This includes
every repeated label as its own row or column index. -/
def evaluateTable (k m : ℕ)
    (M : Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k → Bool)
    (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) : Fin m → Fin m → Bool :=
  fun i j => M (z.1 i) (z.2 j)

def roundedTable (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ)
    (M : Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k → Bool)
    (bits : CurrentAdditive.RoundedDraw.BitBlocks
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)) : Fin m → Fin m → Bool :=
  evaluateTable n p₀ q₁ q₂ s w Q k m M
    (roundedLabels n p₀ q₁ q₂ s w Q hs hq₁ k m bits)

/-- Whole-table events inherit the common fixed-tape error bound. There is
one error budget for the complete table, without an additional m² factor. -/
theorem roundedTable_event_error_200
    (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ)
    (M : Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k → Bool)
    (P : (Fin m → Fin m → Bool) → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)).prob
        (fun bits => P (roundedTable n p₀ q₁ q₂ s w Q hs hq₁ k m M bits)) -
      (sampleLaw n p₀ q₁ q₂ s w Q k m).toFiniteLaw.prob
        (fun z => P (evaluateTable n p₀ q₁ q₂ s w Q k m M z))| ≤ (1 : ℝ) / 200 :=
  rounded_map_event_error_200 n p₀ q₁ q₂ s w Q hs hq₁ k m
    (evaluateTable n p₀ q₁ q₂ s w Q k m M) P

theorem roundedTable_event_error_lt_100
    (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ)
    (M : Row n p₀ q₁ q₂ s w Q k → Column n p₀ q₁ q₂ s w Q k → Bool)
    (P : (Fin m → Fin m → Bool) → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)).prob
        (fun bits => P (roundedTable n p₀ q₁ q₂ s w Q hs hq₁ k m M bits)) -
      (sampleLaw n p₀ q₁ q₂ s w Q k m).toFiniteLaw.prob
        (fun z => P (evaluateTable n p₀ q₁ q₂ s w Q k m M z))| < (1 : ℝ) / 100 :=
  lt_of_le_of_lt (roundedTable_event_error_200 n p₀ q₁ q₂ s w Q hs hq₁ k m M P)
    (by norm_num)

#print axioms roundedTable_event_error_lt_100

end Table
end CurrentAdditive.V39RecursiveGenerator
