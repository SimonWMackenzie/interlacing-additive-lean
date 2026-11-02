import CurrentAdditive.QuarticWidthFromN
import Paper2.SeedTableClock

/-! A fixed polynomial clock for the complete unary-n to quartic-width
physical subprogram. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.RandomizedSchedule

theorem clock_poly (n : ℕ) :
    clock n ≤ SeedT45.SeedClock.seedC * (n + 2) ^ 16 := by
  let N := n + 2
  let e := RestorationWidthScheduleScratch.ell (Nat.clog 2 n)
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hN16 : N ≤ N ^ 16 := by
    calc N = N ^ 1 := by simp
      _ ≤ N ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have hpow : (n + 1) ^ 6 ≤ N ^ 16 := by
    calc
      (n + 1) ^ 6 ≤ N ^ 6 := Nat.pow_le_pow_left (by dsimp [N]; omega) 6
      _ ≤ N ^ 16 := Nat.pow_le_pow_right hN (by omega)
  have hL := SeedT45.SeedClock.lBd_poly n
  have hL' : LProducer.lBd n ≤ 729 * SeedT45.SeedClock.W ^ 6 * N ^ 16 :=
    hL.trans (Nat.mul_le_mul_left _ hpow)
  have he : e ≤ n + 1 := by
    have h0 : Nat.clog 2 n ≤ n :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have h1 : Nat.clog 2 (Nat.clog 2 n + 1) ≤ Nat.clog 2 n + 1 :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    dsimp [e, RestorationWidthScheduleScratch.ell]
    omega
  have he' : e ≤ N ^ 16 := he.trans (by omega)
  have hw := width_clock_poly n
  change WidthMachine.clock e ≤ 100 * N ^ 16 at hw
  change LProducer.lBd n + (2 * e + 2) + WidthMachine.clock e + 2 ≤
    SeedT45.SeedClock.seedC * N ^ 16
  have hC : SeedT45.SeedClock.seedC = 729 * SeedT45.SeedClock.W ^ 6 + 100000 := rfl
  rw [hC]
  nlinarith

theorem run_poly (n : ℕ) :
    let e := RestorationWidthScheduleScratch.ell (Nat.clog 2 n)
    ∃ T ≤ SeedT45.SeedClock.seedC * (n + 2) ^ 16,
      ∃ F : LProducer.LK → List Bool,
      ((advance program)^[T])
        (⟨some startLabel, initialControl, initial n⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, initialControl,
          Sum.elim F (Sum.elim
            (Function.update (Function.update (Function.update (WidthMachine.initial e) 1
              (List.replicate 4 true)) 5 (List.replicate (4 * e) true))
              9 (List.replicate (width27 (Nat.clog 2 n)) true))
            (fun _ => []))⟩ ∧ CountFront.LFacts n F := by
  intro e
  obtain ⟨T, hT, F, hr, hFacts⟩ := run n
  exact ⟨T, hT.trans (clock_poly n), F, hr, hFacts⟩

end Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN.clock_poly
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.WidthFromN.run_poly
