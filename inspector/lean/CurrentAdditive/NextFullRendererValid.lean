import CurrentAdditive.NextThresholdWriter

/-! A single fixed ambient TM2 program, from only the valid encoded Yao
source, through every physical constructor to the exact encoded instance. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.YaoFrame Paper2.HeaderA

def sourceDimensionsClock {t : ℕ} (x : YaoSource t)
    (u v : ℕ) : ℕ := sourceFieldClock x u + v + 1

def thresholdWriterClock {t : ℕ} (x : YaoSource t)
    (u c : ℕ) : ℕ :=
  let b := paddedEdgeBits x.2.1
  ((2*b+2)+(2*(2*b+2)+(4*t+3)+2)+1) +
    writerAfterThresholdClock x u c + 1

def rendererProgram (t : ℕ) :=
  BitMachineRawSequence.program (sourceThroughDimensions t)
    (thresholdWriterProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none)),
      ((MultiMove.initial, ()), (false, (false, false))))
    ((none, (none, (none, ()))),
      ((MultiMove.initial, writerTableControl),
        (MultiMove.initial, progCtl)))

theorem physical_renderer_valid (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let d := publicFieldDegree b t
    let n := paddedEdgeCount x.2.1*(arity t+1)
    let H := paddedEdgeCount x.2.1
    let cap := H^(2^(t-1))
    let R2 := (2^d)^2
    ∃ c < 2^d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ u ≤ prepTime d n +
          55*2^d*2^(d/2)*(d+1)^2+2+
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        ∃ v ≤
          CopyFill.fillCost (dimensionJobs t) (sourceFieldOutput x u) + 1 +
          (2^(t-1)+1) + 1 +
          (MatrixAddressMachine.exactTime x.1 cap 0 +
            MatrixAddressMachine.exactTime (2^(t-1)) H 0 +
            MatrixAddressMachine.exactTime ((2^(t-1))*H) R2 0+2)+1,
          ∃ steps ≤ sourceDimensionsClock x u v +
              thresholdWriterClock x u c + 1,
            let z := ((advance (rendererProgram t))^[steps])
              (⟨some (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      (BitMachineRawSequence.leftLabel
                        (BitMachineRawSequence.leftLabel
                          (BitMachineRawSequence.leftLabel
                            (BitMachineRawSequence.leftLabel
                              (BitMachineRawSequence.leftLabel
                                (BitMachineRawSequence.leftLabel
                                  Paper2.YaoHeaderParser.startLabel))))))))),
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
                      (MultiMove.initial, progCtl)))),
                bank (sourceEmbed t 16) (blank t 16)
                  (Paper2.YaoMachine.initBank 0 x [])⟩ :
                    TM2.Cfg (fun _ : Cell t 16 => Bool) _ _)
            z.l = none ∧
            z.stk (.header outH) =
              encodeInstance
                (instanceOfTable b t d
                  (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c)
                  (le_paddedEdgeCount x.2.1) x.2.2) := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let d := publicFieldDegree b t
  let n := H*(arity t+1)
  let cap := H^(2^(t-1))
  let R2 := (2^d)^2
  obtain ⟨c, hc, hfirst, u, hu, v, hv, s, hs, hdim, hpacked⟩ :=
    physical_source_dimensions t ht x
  obtain ⟨w, hw, control, htail⟩ :=
    physical_threshold_writer t x u c hpacked
  change s ≤ sourceDimensionsClock x u v at hs
  change w ≤ thresholdWriterClock x u c at hw
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceThroughDimensions t) (thresholdWriterProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    Paper2.YaoHeaderParser.startLabel))))))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none)),
      ((MultiMove.initial, ()), (false, (false, false))))
    (((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none)),
      ((MultiMove.initial, ()), (false, (false, false))))
    ((none, (none, (none, ()))),
      ((MultiMove.initial, writerTableControl), (MultiMove.initial, progCtl)))
    ((none, (none, (none, ()))),
      ((MultiMove.initial, control), (MultiMove.initial, progCtl)))
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x []))
    (sourceDimensionsOutput x u) _ s w hdim htail
  refine ⟨c, hc, hfirst, u, hu, v, hv,
    steps, by omega, ?_⟩
  dsimp only
  rw [show ((advance (rendererProgram t))^[steps]) _ = _ from
    (by simpa [rendererProgram] using hrun)]
  constructor
  · rfl
  · dsimp only [TM2.Cfg.stk]
    change bank (headerEmbed t 16) _ _ (.header outH) = _
    have hslot : (headerEmbed t 16) outH =
        (.header outH : Cell t 16) := rfl
    rw [← hslot, bank_at]
    simp

#print axioms physical_renderer_valid

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
