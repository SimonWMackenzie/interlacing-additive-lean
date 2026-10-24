import CurrentAdditive.GaussControlTrace
import CurrentAdditive.GaussRawZeroCheck
import EthInapproximability.CurrentPaper.EntryUnaryCompare

/-!
The exact bridge from the physical RawRat zero-test bit to the pivot predicate
used by `pivotTyped`.  A matrix getter followed by `GaussRawZeroCheck.machine`
can use this theorem for each scanned row without changing the selected pivot.
-/

namespace CurrentAdditive.GaussPivotPredicate

open CurrentAdditive.GaussPhysical
open CurrentAdditive.SequentialTotality

/-- The existing literal unary comparator's three verdict bits implement
the row-threshold check used in pivot search. -/
theorem threshold_verdict (r i : Nat) :
    EthInapproximability.CurrentPaper.EntryUnaryCompare.verdict
      true true false r i = decide (r ≤ i) := by
  by_cases hlt : r < i
  · have hle : r ≤ i := Nat.le_of_lt hlt
    simp [EthInapproximability.CurrentPaper.EntryUnaryCompare.verdict, hlt, hle]
  · by_cases heq : r = i
    · simp [EthInapproximability.CurrentPaper.EntryUnaryCompare.verdict, heq]
    · have hgt : ¬ r ≤ i := by omega
      simp [EthInapproximability.CurrentPaper.EntryUnaryCompare.verdict,
        hlt, heq, hgt]

theorem zero_flag_matrix_cell {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (c : Fin k) :
    CurrentAdditive.GaussRawZeroCheck.result
        (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat (B i c))) = [true] ↔
      B i c = 0 := by
  rw [CurrentAdditive.GaussRawZeroCheck.zero_flag_iff_value
    _ (rawOfRat_valid (B i c)), rawOfRat_value]

def physicalCandidate {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Nat) (c : Fin k) (i : Fin m) : Bool :=
  decide (r ≤ i.val) &&
    !decide (CurrentAdditive.GaussRawZeroCheck.result
      (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat (B i c))) = [true])

theorem physicalCandidate_eq {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Nat) (c : Fin k) (i : Fin m) :
    physicalCandidate B r c i = decide (r ≤ i.val ∧ B i c ≠ 0) := by
  unfold physicalCandidate
  by_cases hr : r ≤ i.val
  · by_cases hz : B i c = 0
    · have hf := (zero_flag_matrix_cell B i c).2 hz
      have hf0 : CurrentAdditive.GaussRawZeroCheck.result
          (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat 0)) = [true] := by
        simpa [hz] using hf
      simp [hr, hz, hf0]
    · have hf : CurrentAdditive.GaussRawZeroCheck.result
          (CurrentAdditive.CodeDCodec.encodeRawRat (rawOfRat (B i c))) ≠
          [true] := fun hflag => hz ((zero_flag_matrix_cell B i c).1 hflag)
      simp [hr, hz, hf]
  · simp [hr]

theorem physicalPivot_eq {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Nat) (c : Fin k) :
    (List.finRange m).find? (physicalCandidate B r c) =
      pivotTyped B r c := by
  unfold pivotTyped
  congr 1
  funext i
  exact physicalCandidate_eq B r c i

#print axioms zero_flag_matrix_cell
#print axioms threshold_verdict
#print axioms physicalPivot_eq

end CurrentAdditive.GaussPivotPredicate
