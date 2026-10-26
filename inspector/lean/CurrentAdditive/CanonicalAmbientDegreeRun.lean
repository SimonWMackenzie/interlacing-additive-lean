import CurrentAdditive.CanonicalHeaderBulkPrep
import CurrentAdditive.YaoDegreeInterface

/-! The physical public-degree constructor, including its actual cut search,
embedded in the common source/writer ambient stack namespace. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias

def degreeStage (t : ℕ) :=
  fun l => stackStmt (degreeEmbed t 16)
    (YaoDegreeMachine.program t l)

theorem physical_ambient_degree (t b : ℕ) (ht : 4 ≤ t)
    (S : Cell t 16 → List Bool)
    (hb : S (.degree 0) = List.replicate b true)
    (hH : S (.degree 1) = List.replicate (2^b) true)
    (hblank : ∀ i : Fin 16, 3 ≤ i.val → S (.degree i) = []) :
    ∃ steps ≤ YaoDegreeClock.polynomial t (2^b),
      ((advance (degreeStage t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
            YaoDegreeMachine.afterCtrl), S⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        stackCfg (degreeEmbed t 16) S
          (⟨none,
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl),
            YaoDegreeMachine.finalBank
              (fun i : Fin 16 => S (.degree i)) b t⟩ :
                TM2.Cfg (fun _ : Fin 16 => Bool) _ _) := by
  let D : Fin 16 → List Bool := fun i => S (.degree i)
  obtain ⟨steps, hsteps, hrun⟩ :=
    YaoDegreeInterface.run_polynomial D b t ht hb hH hblank
  refine ⟨steps, hsteps, ?_⟩
  have hbank := bank_eq_self (degreeEmbed t 16) S D (by intro i; rfl)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (degreeEmbed t 16) S (YaoDegreeMachine.program t)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl), D⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) steps
  have hr := congrArg (stackCfg (degreeEmbed t 16) S) hrun
  have hcombined := he.trans hr
  simpa [degreeStage, stackCfg, hbank, D] using hcombined

#print axioms physical_ambient_degree

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
