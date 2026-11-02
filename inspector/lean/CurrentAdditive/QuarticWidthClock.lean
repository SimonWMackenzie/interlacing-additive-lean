import CurrentAdditive.QuarticWidthMachine
import Paper2.A3Clock

/-! Polynomial clock for the fixed quartic-width machine on the graph-derived
exponent `ell = clog₂(clog₂ n + 1)`. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.RandomizedSchedule

theorem width_clock_poly (n : ℕ) :
    WidthMachine.clock (RestorationWidthScheduleScratch.ell (Nat.clog 2 n)) ≤
      100 * (n + 2) ^ 16 := by
  let N := n + 2
  let L := Nat.clog 2 n
  let e := RestorationWidthScheduleScratch.ell L
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hL : L ≤ n := by
    dsimp [L]
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have he : e ≤ L + 1 := by
    dsimp [e, RestorationWidthScheduleScratch.ell]
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hpow : 2 ^ e ≤ (L + 3) ^ 2 := by
    simpa [e, RestorationWidthScheduleScratch.ell] using
      (Paper2.A3Assembly.Clock.two_pow_clog_le (L + 1))
  have hL3 : L + 3 ≤ 2 * N := by dsimp [N]; omega
  have h2N : 2 * N ≤ N ^ 2 := by nlinarith
  have h2e : 2 ^ e ≤ N ^ 4 := calc
    2 ^ e ≤ (L + 3) ^ 2 := hpow
    _ ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left hL3 2
    _ ≤ (N ^ 2) ^ 2 := Nat.pow_le_pow_left h2N 2
    _ = N ^ 4 := by ring
  have hw : 2 ^ (4 * e) ≤ N ^ 16 := by
    calc
      2 ^ (4 * e) = (2 ^ e) ^ 4 := by rw [← pow_mul]; ring
      _ ≤ (N ^ 4) ^ 4 := Nat.pow_le_pow_left h2e 4
      _ = N ^ 16 := by ring
  have hN1 : 1 ≤ N ^ 16 := Nat.one_le_pow _ _ (by omega)
  have hN16 : N ≤ N ^ 16 := by
    calc N = N ^ 1 := by simp
      _ ≤ N ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
  have heN : e ≤ N ^ 16 := by dsimp [N] at *; omega
  change WidthMachine.clock e ≤ 100 * N ^ 16
  unfold WidthMachine.clock MatrixAddressMachine.exactTime
  nlinarith

/-- On unary `ell` obtained from the graph, the actual fixed width machine
halts in a graph-polynomial clock with exactly the unary quartic width. -/
theorem width_program_graph_clock (n : ℕ) :
    let e := RestorationWidthScheduleScratch.ell (Nat.clog 2 n)
    ∃ T ≤ 100 * (n + 2) ^ 16,
      ((advance WidthMachine.program)^[T])
        (⟨some WidthMachine.startLabel, WidthMachine.initialControl,
          WidthMachine.initial e⟩ :
          TM2.Cfg (fun _ : WidthMachine.Stack => Bool) _ _) =
        ⟨none, WidthMachine.initialControl,
          Function.update (Function.update (Function.update (WidthMachine.initial e) 1
            (List.replicate 4 true)) 5 (List.replicate (4 * e) true))
            9 (List.replicate (width27 (Nat.clog 2 n)) true)⟩ := by
  intro e
  obtain ⟨T, hT, hr⟩ := WidthMachine.run e
  refine ⟨T, hT.trans (width_clock_poly n), ?_⟩
  simpa only [width27, RestorationWidthScheduleScratch.ell, e,
    Nat.mul_comm] using hr

end Paper2.CurrentAdditive.QuarticNumericFront

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.width_clock_poly
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.width_program_graph_clock
