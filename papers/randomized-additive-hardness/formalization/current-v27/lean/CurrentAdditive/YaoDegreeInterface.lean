import CurrentAdditive.YaoDegreeClock

/-! Stable output and polynomial-clock interface for the renderer. -/

namespace CurrentAdditive.SmallBias.YaoDegreeInterface

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding

theorem output_degree (S : Fin 16 → List Bool) (b t : ℕ) :
    YaoDegreeMachine.finalBank S b t 3 =
      List.replicate (publicFieldDegree b t) true := by
  simp [YaoDegreeMachine.finalBank]

theorem preserve_other (S : Fin 16 → List Bool) (b t : ℕ)
    (z : Fin 16) (h3 : z ≠ 3) (h4 : z ≠ 4)
    (h5 : z ≠ 5) (h6 : z ≠ 6) :
    YaoDegreeMachine.finalBank S b t z = S z := by
  have hscan : YaoDegreeMachine.scanBank S b t z =
      YaoDegreeMachine.baseBank S b t z := by
    exact YaoCutScanLoop.scanState_other _ _ _ _ z h3 h4 h5
  have hbase : YaoDegreeMachine.baseBank S b t z = S z := by
    simp [YaoDegreeMachine.baseBank, h5, h6]
  simpa [YaoDegreeMachine.finalBank, YaoDegreeMachine.powerBank,
    Function.update_apply, h3, h4, h5, h3.symm, h4.symm, h5.symm]
    using hscan.trans hbase

theorem output_suffix (S : Fin 16 → List Bool) (b t : ℕ) :
    YaoDegreeMachine.finalBank S b t 4 =
      List.replicate (sourceSuffixDepth b t) true := by
  simp [YaoDegreeMachine.finalBank, YaoDegreeMachine.powerBank]

theorem output_power (S : Fin 16 → List Bool) (b t : ℕ) :
    YaoDegreeMachine.finalBank S b t 5 =
      List.replicate (2 ^ sourceSuffixDepth b t) true := by
  simp [YaoDegreeMachine.finalBank, YaoDegreeMachine.powerBank]

theorem output_threshold (S : Fin 16 → List Bool) (b t : ℕ) :
    YaoDegreeMachine.finalBank S b t 6 =
      List.replicate (2 ^ (t + b - 3)) true := by
  have hscan : YaoDegreeMachine.scanBank S b t 6 =
      YaoDegreeMachine.baseBank S b t 6 := by
    exact YaoCutScanLoop.scanState_other _ _ _ _ 6 (by decide)
      (by decide) (by decide)
  simp [YaoDegreeMachine.finalBank, YaoDegreeMachine.powerBank,
    hscan, YaoDegreeMachine.baseBank]

theorem run_polynomial (S : Fin 16 → List Bool) (b t : ℕ) (ht : 4 ≤ t)
    (hb : S 0 = List.replicate b true)
    (hH : S 1 = List.replicate (2 ^ b) true)
    (hblank : YaoDegreeSetupScan.preBlank S) :
    ∃ u ≤ YaoDegreeClock.polynomial t (2 ^ b),
      ((BitMachineEncoding.advance (YaoDegreeMachine.program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
            YaoDegreeMachine.afterCtrl), S⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl), YaoDegreeMachine.finalBank S b t⟩ := by
  obtain ⟨u, hu, hr⟩ := YaoDegreeMachine.run S b t ht hb hH hblank
  exact ⟨u, hu.trans (YaoDegreeClock.timeBound_polynomial b t ht), hr⟩

#print axioms output_degree
#print axioms preserve_other
#print axioms run_polynomial

end CurrentAdditive.SmallBias.YaoDegreeInterface
