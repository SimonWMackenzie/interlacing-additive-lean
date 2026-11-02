import CurrentAdditive.YaoRendererBudget

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 65536

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.YaoFrame Paper2.HeaderA

def rendererWord {t : ℕ} (x : YaoSource t) : List Bool :=
  let b := paddedEdgeBits x.2.1
  let d := publicFieldDegree b t
  encodeInstance
    (instanceOfTable b t d
      ((CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d).getD 0)
      (le_paddedEdgeCount x.2.1) x.2.2)

theorem renderer_outputs_valid (t : ℕ) (ht : 4 ≤ t) (x : YaoSource t) :
    (rendererMachine t).OutputsWithin (encode x) (rendererWord x)
      (rendererBudget x) := by
  obtain ⟨c, hc, hfirst, u, hu, v, hv, steps, hsteps, hhalt, hout⟩ :=
    physical_renderer_budget t ht x
  unfold rendererMachine
  apply outputsWithin_of_raw_run
    (rendererInputCell t) (rendererOutputCell t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      Paper2.YaoHeaderParser.startLabel)))))))))
    ((((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none)),
      ((MultiMove.initial, ()), (false, (false, false)))),
      ((none, (none, (none, ()))),
        ((MultiMove.initial, writerTableControl),
          (MultiMove.initial, progCtl))))
    (rendererProgram t) (encode x) (rendererWord x)
    steps (rendererBudget x) hsteps
  · change (((advance (rendererProgram t))^[steps])
        ⟨some _, _, fun j => if j = rendererInputCell t then encode x else []⟩).l = none
    rw [← renderer_initial_bank t x]
    exact hhalt
  · change (((advance (rendererProgram t))^[steps])
        ⟨some _, _, fun j => if j = rendererInputCell t then encode x else []⟩).stk
          (rendererOutputCell t) = rendererWord x
    rw [← renderer_initial_bank t x]
    simpa [rendererOutputCell, rendererWord, hfirst] using hout

#print axioms renderer_outputs_valid

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
