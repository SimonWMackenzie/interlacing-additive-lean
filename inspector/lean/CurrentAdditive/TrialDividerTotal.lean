import CurrentAdditive.TrialDividerMachine

/-!
Exact execution of all shifts for one monic trial divisor. The program is
the literal five-stack TM2 controller in `TrialDividerMachine`; the unary
count stack has one marker per division iteration. This file relates its
entire run to the frozen `TrialSearch.remainder` recurrence and bounds its
literal transition count quadratically in the dividend degree.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialDividerTotal

open CurrentAdditive.FieldMachineHelper.TrialDividerMachine
open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE bitsBE_length)
open CurrentAdditive.FieldMachineHelper.DivisionRepackBridge (bitsBE_shifted_succ)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
  (step run remainder_eq_run)

def divisorWord (e tail : Nat) : Nat → List Bool
  | 0 => (bitsBE (e + 1) (monicBits e tail)).dropLast
  | m + 1 => bitsBE (e + m + 1) ((monicBits e tail) <<< m)

theorem divisorWord_succ_drop (e tail m : Nat) :
    (divisorWord e tail (m + 1)).dropLast = divisorWord e tail m := by
  cases m with
  | zero => rfl
  | succ m =>
    change (bitsBE (e + (m + 1) + 1)
      ((monicBits e tail) <<< (m + 1))).dropLast =
      bitsBE (e + m + 1) ((monicBits e tail) <<< m)
    rw [bitsBE_shifted_succ]
    simp

def divisionClock (e : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => (4 * (e + m + 1) + 6) + divisionClock e m

theorem divisionClock_le (e m : Nat) :
    divisionClock e m ≤ m * (4 * (e + m) + 6) := by
  induction m with
  | zero => simp [divisionClock]
  | succ m ih =>
    have hmono : 4 * (e + m) + 6 ≤ 4 * (e + (m + 1)) + 6 := by omega
    have hmul := Nat.mul_le_mul_left m hmono
    have hbound := ih.trans hmul
    have hterm : 4 * (e + m + 1) + 6 =
        4 * (e + (m + 1)) + 6 := by omega
    change (4 * (e + m + 1) + 6) + divisionClock e m ≤
      (m + 1) * (4 * (e + (m + 1)) + 6)
    rw [hterm]
    calc
      (4 * (e + (m + 1)) + 6) + divisionClock e m ≤
          (4 * (e + (m + 1)) + 6) +
            m * (4 * (e + (m + 1)) + 6) :=
        Nat.add_le_add_left hbound _
      _ = (m + 1) * (4 * (e + (m + 1)) + 6) := by
        rw [Nat.succ_mul m (4 * (e + (m + 1)) + 6)]
        omega

theorem divisionClock_remainder_le (d e : Nat) (he : e ≤ d) :
    divisionClock e (d - e + 1) + 1 ≤
      (d + 1) * (4 * (d + 1) + 6) + 1 := by
  have hw : e + (d - e + 1) = d + 1 := by omega
  have hm : d - e + 1 ≤ d + 1 := by omega
  calc
    divisionClock e (d - e + 1) + 1 ≤
        (d - e + 1) * (4 * (e + (d - e + 1)) + 6) + 1 :=
      Nat.add_le_add_right (divisionClock_le e (d - e + 1)) 1
    _ = (d - e + 1) * (4 * (d + 1) + 6) + 1 := by rw [hw]
    _ ≤ (d + 1) * (4 * (d + 1) + 6) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) 1

/-- The complete physical loop ends with the exact arithmetic remainder bits. -/
theorem divider_run (e tail : Nat) (htail : tail < 2 ^ e) :
    ∀ (m acc : Nat) (b : Bool),
      ∃ (bFinal : Bool),
        TrialDividerMachine.run (divisionClock e m)
          (cfg (some .next) (b, none, none)
            (bitsBE (e + m) acc) (divisorWord e tail m)
            [] [] (List.replicate m true)) =
        cfg (some .next) (bFinal, none, none)
          (bitsBE e (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.run
            e (monicBits e tail) m acc))
          (divisorWord e tail 0) [] [] [] := by
  intro m
  induction m with
  | zero =>
    intro acc b
    exact ⟨b, by simp [divisionClock, TrialDividerMachine.run,
      CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.run]⟩
  | succ m ih =>
    intro acc b
    let divisor := monicBits e tail
    let nextAcc := step e m divisor acc
    have hstep := oneTrialStep b e m tail acc
      (List.replicate m true) htail
    have hclock : divisionClock e (m + 1) =
        (4 * (e + m + 1) + 6) + divisionClock e m := rfl
    have hdiv : (bitsBE (e + m + 1) (divisor <<< m)).dropLast =
        divisorWord e tail m := by
      simpa [divisor, divisorWord] using divisorWord_succ_drop e tail m
    have hphase : TrialDividerMachine.run (4 * (e + m + 1) + 6)
        (cfg (some .next) (b, none, none)
          (bitsBE (e + (m + 1)) acc) (divisorWord e tail (m + 1))
          [] [] (List.replicate (m + 1) true)) =
        cfg (some .next) (acc.testBit (e + m), none, none)
          (bitsBE (e + m) nextAcc) (divisorWord e tail m)
          [] [] (List.replicate m true) := by
      rw [← hdiv]
      simpa [divisorWord, nextAcc, divisor, Nat.add_assoc] using hstep
    obtain ⟨bFinal, htailRun⟩ := ih nextAcc (acc.testBit (e + m))
    refine ⟨bFinal, ?_⟩
    rw [hclock, TrialDividerMachine.run_add, hphase, htailRun]
    rfl

/-- The inner trial test halts and leaves the frozen remainder in stack 0. -/
theorem divider_remainder (d e tail dividend : Nat)
    (he : e ≤ d) (htail : tail < 2 ^ e) :
    ∃ (bFinal : Bool),
      TrialDividerMachine.run (divisionClock e (d - e + 1) + 1)
        (cfg (some .next) (false, none, none)
          (bitsBE (d + 1) dividend)
          (divisorWord e tail (d - e + 1))
          [] [] (List.replicate (d - e + 1) true)) =
      cfg none (bFinal, none, none)
        (bitsBE e (remainder d e (monicBits e tail) dividend))
        (divisorWord e tail 0) [] [] [] := by
  have hw : e + (d - e + 1) = d + 1 := by omega
  obtain ⟨bFinal, hrun⟩ := divider_run e tail htail
    (d - e + 1) dividend false
  rw [hw] at hrun
  have hhalt := halt_after_empty_count bFinal
    (bitsBE e (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.run
      e (monicBits e tail) (d - e + 1) dividend))
    (divisorWord e tail 0)
  refine ⟨bFinal, ?_⟩
  rw [TrialDividerMachine.run_add, hrun, hhalt]
  rw [remainder_eq_run]

#print axioms divider_remainder
#print axioms divisionClock_remainder_le

#print axioms divider_run

end CurrentAdditive.FieldMachineHelper.TrialDividerTotal
