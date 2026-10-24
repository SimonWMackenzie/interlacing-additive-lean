import Paper2.CodeGeneratorComplete
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Charge the concrete compiler's entire temporary bank during reentry,
including accumulated intermediate syntax words. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeGeneratorReentryBound

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CodeRecursiveColumn Paper2.CodeRecursiveReentry

def maxLength (S : Stack → List Bool) : Nat :=
  Finset.univ.sup (fun i : Stack => (S i).length)

theorem length_le_max (S : Stack → List Bool) (i : Stack) :
    (S i).length ≤ maxLength S :=
  Finset.le_sup (f := fun j : Stack => (S j).length)
    (Finset.mem_univ i)

theorem cleanedBefore_length_le (S : Stack → List Bool) (i : Stack) :
    (cleanedBefore S i).length ≤ maxLength S := by
  by_cases hi : i ∈ keepBefore
  · change (SourceClauseClearExcept.result keepBefore S i).length ≤ _
    rw [SourceClauseClearExcept.retained keepBefore S i hi]
    exact length_le_max S i
  · change (SourceClauseClearExcept.result keepBefore S i).length ≤ _
    rw [SourceClauseClearExcept.emptied keepBefore S i hi]
    simp

theorem withColumn_length_le (S : Stack → List Bool) (i : Stack) :
    (withColumn S i).length ≤ maxLength S := by
  by_cases h33 : i = 33
  · subst i
    simp only [withColumn, Function.update_self]
    exact length_le_max S 37
  · by_cases h2 : i = 2
    · subst i
      simp only [withColumn,
        Function.update_of_ne (by decide : (2 : Stack) ≠ 33),
        withRow, Function.update_self]
      exact length_le_max S 52
    · simp only [withColumn, Function.update_of_ne h33,
        withRow, Function.update_of_ne h2]
      exact cleanedBefore_length_le S i

theorem beforeTime_le (S : Stack → List Bool) :
    beforeTime S ≤
      SourceClauseClearExcept.workCount keepBefore * maxLength S +
        SourceClauseClearExcept.workCount keepBefore + 2 := by
  unfold beforeTime
  have hsum :
      (∑ i : Fin (SourceClauseClearExcept.workCount keepBefore),
        (S (SourceClauseClearExcept.workBank keepBefore i)).length) ≤
      ∑ _ : Fin (SourceClauseClearExcept.workCount keepBefore),
        maxLength S := by
    apply Finset.sum_le_sum
    intro i _
    exact length_le_max S _
  simpa using Nat.add_le_add_right hsum
    (SourceClauseClearExcept.workCount keepBefore + 2)

theorem afterTime_le (S : Stack → List Bool) :
    afterTime S ≤
      SourceClauseClearExcept.workCount keepAfter * maxLength S +
        SourceClauseClearExcept.workCount keepAfter + 2 := by
  unfold afterTime
  have hsum :
      (∑ i : Fin (SourceClauseClearExcept.workCount keepAfter),
        ((withColumn S)
          (SourceClauseClearExcept.workBank keepAfter i)).length) ≤
      ∑ _ : Fin (SourceClauseClearExcept.workCount keepAfter),
        maxLength S := by
    apply Finset.sum_le_sum
    intro i _
    exact withColumn_length_le S _
  simpa using Nat.add_le_add_right hsum
    (SourceClauseClearExcept.workCount keepAfter + 2)

def factor : Nat :=
  SourceClauseClearExcept.workCount keepBefore +
    SourceClauseClearExcept.workCount keepAfter + 5

theorem reentry_clock_le (S : Stack → List Bool) :
    CodeRecursiveReentry.clock S ≤ factor * (maxLength S+1)+10 := by
  have hb := beforeTime_le S
  have ha := afterTime_le S
  have h52 := length_le_max S 52
  have h37 := length_le_max S 37
  dsimp [CodeRecursiveReentry.clock,
    CodeRecursiveReentry.b₂, CodeRecursiveReentry.b₁, factor]
  nlinarith

#print axioms reentry_clock_le

end Paper2.CodeGeneratorReentryBound
