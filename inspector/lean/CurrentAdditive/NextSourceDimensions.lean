import CurrentAdditive.NextFieldDimensionsLocal

/-! Source-started parsing, degree, field search/list, and exact dimensions
as one ambient TM2 program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceFieldClock {t : ℕ} (x : YaoSource t) (u : ℕ) : ℕ :=
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let n := paddedEdgeCount x.2.1*(arity t+1)
  (sourceSelectorClock x +
    ((2*d+2)+((2*d+2)+5+2+
      MatrixWeightedPower.powerBound 4 d+3)+1)+1) +
  ((2*d+2)+(2*n+2)+1+u+1) + 1

def sourceThroughDimensions (t : ℕ) :=
  BitMachineRawSequence.program (sourceThroughField t)
    (dimensionsFullProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob))))
    ((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none))
    ((MultiMove.initial, ()), (false, (false, false)))

theorem physical_source_dimensions (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    let n := paddedEdgeCount x.2.1*(arity t+1)
    let H := paddedEdgeCount x.2.1
    let cap := H^(2^(t-1))
    let R2 := (2^d)^2
    ∃ c < 2^d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ u ≤ FieldUnaryUnifiedMachine.prepTime d n +
          55*2^d*2^(d/2)*(d+1)^2+2+
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        ∃ v ≤
          CopyFill.fillCost (dimensionJobs t) (sourceFieldOutput x u) + 1 +
          (2^(t-1)+1) + 1 +
          (MatrixAddressMachine.exactTime x.1 cap 0 +
            MatrixAddressMachine.exactTime (2^(t-1)) H 0 +
            MatrixAddressMachine.exactTime ((2^(t-1))*H) R2 0+2)+1,
          ∃ steps ≤ sourceFieldClock x u + v + 1,
            ((advance (sourceThroughDimensions t))^[steps])
              (⟨some (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      (BitMachineRawSequence.leftLabel
                        (BitMachineRawSequence.leftLabel
                          (BitMachineRawSequence.leftLabel
                            (BitMachineRawSequence.leftLabel
                              (BitMachineRawSequence.leftLabel
                                Paper2.YaoHeaderParser.startLabel)))))))),
                (((((((CanonicalSourcePrelude.initialControl t,
                  (none, (none, none))),
                  ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
                    YaoDegreeMachine.afterCtrl)),
                  ((none, none), (none, ((), false)))),
                  (none, ((), (none, (false, false))))),
                  (none, (none, ((), ((), (false, false)))))),
                  ((none, none), prepEmbed none)),
                  ((MultiMove.initial, ()), (false, (false, false)))),
                bank (sourceEmbed t 16) (blank t 16)
                  (Paper2.YaoMachine.initBank 0 x [])⟩ :
                    TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
              ⟨none,
                (((((((CanonicalSourcePrelude.initialControl t,
                  (none, (none, none))),
                  ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
                    YaoDegreeMachine.afterCtrl)),
                  ((none, none), (none, ((), false)))),
                  (none, ((), (none, (false, false))))),
                  (none, (none, ((), ((), (false, false)))))),
                  ((none, none), prepEmbed none)),
                  ((MultiMove.initial, ()), (false, (false, false)))),
                sourceDimensionsOutput x u⟩ ∧
            sourceFieldOutput x u
              (.field (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
                CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
              CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n := by
  dsimp only
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let H := paddedEdgeCount x.2.1
  let cap := H^(2^(t-1))
  let R2 := (2^d)^2
  obtain ⟨c, hc, hfirst, u, hu, s, hs, hfield, hpacked⟩ :=
    physical_source_field t ht x
  obtain ⟨v, hv, hdim⟩ := physical_dimensions_after_field t x u
  let r := FieldUnaryUnifiedMachine.run u
    (FieldUnaryUnifiedMachine.initialConfig d (H*(arity t+1)))
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceThroughField t) (dimensionsFullProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  Paper2.YaoHeaderParser.startLabel)))))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob))))
    ((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none))
    ((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), r.var))
    ((MultiMove.initial, ()), (false, (false, false)))
    ((MultiMove.initial, ()), (false, (false, false)))
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x []))
    (sourceFieldOutput x u) _ s v
    hfield (by simpa using hdim)
  change s ≤ sourceFieldClock x u at hs
  refine ⟨c, hc, hfirst, u, hu, v, hv, steps, by omega, ?_, hpacked⟩
  simpa [sourceThroughDimensions, r] using hrun

#print axioms physical_source_dimensions

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
