import CurrentAdditive.QuarticTMValues
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

namespace Paper2.CurrentAdditive.QuarticDimensionsMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CurrentAdditive.QuarticNumericFront
open CurrentAdditive.RandomizedSchedule
open SourceRecursiveNoSampling

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 65536

theorem dimensions_le_machine_clock (n m L Δ k : ℕ) (γ : ℚ) :
    sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
      BitMachineStackGrowth.perStep TMFront.tmProg *
        TMFront.tmBd k (vector27 n m L Δ γ) L ∧
    sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k ≤
      BitMachineStackGrowth.perStep TMFront.tmProg *
        TMFront.tmBd k (vector27 n m L Δ γ) L := by
  obtain ⟨t, ht, vc, FT, FM, hr, _, hMF⟩ :=
    TMFront.tm_run k (vector27 n m L Δ γ) L
  obtain ⟨hcol, hrow⟩ := TM27.source_dims_of_MFacts n m L Δ k γ FM hMF
  have h10 := BitMachineStackGrowth.run_growth TMFront.tmProg
    (⟨some TMFront.tmStart, TMFront.tmCtl,
      TMFront.TM0 k (vector27 n m L Δ γ) L⟩ :
      TM2.Cfg (fun _ : TMFront.JM => Bool) _ _) t (TMFront.mc 10)
  have h13 := BitMachineStackGrowth.run_growth TMFront.tmProg
    (⟨some TMFront.tmStart, TMFront.tmCtl,
      TMFront.TM0 k (vector27 n m L Δ γ) L⟩ :
      TM2.Cfg (fun _ : TMFront.JM => Bool) _ _) t (TMFront.mc 13)
  rw [hr] at h10 h13
  have h10' : (FM 10).length ≤ BitMachineStackGrowth.perStep TMFront.tmProg * t := by
    simpa [TMFront.TM0, TMFront.mc] using h10
  have h13' : (FM 13).length ≤ BitMachineStackGrowth.perStep TMFront.tmProg * t := by
    simpa [TMFront.TM0, TMFront.mc] using h13
  rw [hrow, List.length_replicate] at h13'
  rw [hcol, List.length_replicate] at h10'
  constructor
  · exact h13'.trans (Nat.mul_le_mul_left _ ht)
  · exact h10'.trans (Nat.mul_le_mul_left _ ht)


#print axioms dimensions_le_machine_clock

end
end Paper2.CurrentAdditive.QuarticDimensionsMachine
