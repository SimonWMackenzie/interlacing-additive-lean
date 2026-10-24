import CurrentAdditive.NextSourceSquareBridge

/-! Valid source through the real degree compiler and unified first-passing
field search/list printer in one ambient program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceFieldOutput {t : ℕ} (x : YaoSource t) (u : ℕ) :
    Cell t 16 → List Bool :=
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let n := paddedEdgeCount x.2.1*(arity t+1)
  bank (fieldCombinedEmbed t 16)
    (fieldInputBank t d n (sourceSquareOutput x))
    (FieldUnaryUnifiedMachine.run u
      (FieldUnaryUnifiedMachine.initialConfig d n)).stk

def sourceThroughField (t : ℕ) :=
  BitMachineRawSequence.program (sourceThroughSquare t)
    (fieldFullProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((((CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false))))))
    ((none, none), prepEmbed none)

theorem physical_source_field (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    let n := paddedEdgeCount x.2.1*(arity t+1)
    ∃ c < 2^d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ u ≤ FieldUnaryUnifiedMachine.prepTime d n +
          55*2^d*2^(d/2)*(d+1)^2+2+
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        ∃ steps ≤
          (sourceSelectorClock x +
            ((2*d+2)+((2*d+2)+5+2+
              MatrixWeightedPower.powerBound 4 d+3)+1)+1) +
          ((2*d+2)+(2*n+2)+1+u+1) + 1,
          ((advance (sourceThroughField t))^[steps])
            (⟨some (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      (BitMachineRawSequence.leftLabel
                        (BitMachineRawSequence.leftLabel
                          (BitMachineRawSequence.leftLabel
                            Paper2.YaoHeaderParser.startLabel))))))),
              ((((((CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.initialControl t,
                (none, (none, none))),
                ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
                  YaoDegreeMachine.afterCtrl)),
                ((none, none), (none, ((), false)))),
                (none, ((), (none, (false, false))))),
                (none, (none, ((), ((), (false, false)))))),
                ((none, none), prepEmbed none)),
              bank (sourceEmbed t 16) (blank t 16)
                (Paper2.YaoMachine.initBank 0 x [])⟩ :
                  TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
            ⟨none,
              ((((((CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.initialControl t,
                (none, (none, none))),
                ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
                  YaoDegreeMachine.afterCtrl)),
                ((none, none), (none, ((), false)))),
                (none, ((), (none, (false, false))))),
                (none, (none, ((), ((), (false, false)))))),
                ((none, none),
                  (FieldUnaryUnifiedMachine.run u
                    (FieldUnaryUnifiedMachine.initialConfig d n)).var)),
              sourceFieldOutput x u⟩ ∧
          sourceFieldOutput x u
            (.field (printerSlots
              CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
            CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n := by
  dsimp only
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let n := paddedEdgeCount x.2.1*(arity t+1)
  let S := sourceSquareOutput x
  obtain ⟨s, hs, hprefix⟩ := physical_source_square t ht x
  obtain ⟨hd, hn, _, _, _⟩ := sourceSquareOutput_public x
  obtain ⟨hblank, hscratch⟩ := sourceSquareOutput_fieldBlank x
  obtain ⟨c, hc, hfirst, u, hu, total, htotal, hfield, hpacked⟩ :=
    physical_field_full t d n (public_degree_pos _ _) S
      hd hn hblank hscratch
  let r := FieldUnaryUnifiedMachine.run u
    (FieldUnaryUnifiedMachine.initialConfig d n)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceThroughSquare t) (fieldFullProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                Paper2.YaoHeaderParser.startLabel))))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((((CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false))))))
    (((((CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false))))))
    ((none, none), prepEmbed none)
    ((none, none), r.var)
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x [])) S _ s total
    (by simpa [S] using hprefix)
    (by simpa [S, r] using hfield)
  dsimp [d, n] at hs htotal
  refine ⟨c, hc, hfirst, u, hu, steps, by omega, ?_, ?_⟩
  · simpa [sourceThroughField, sourceFieldOutput,
      S, d, n, r, stackCfg] using hrun
  · have hslot : fieldCombinedEmbed t 16
        (FieldUnaryUnifiedMachine.fieldSlots
          (printerSlots
            CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
        (.field (printerSlots
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output) :
            Cell t 16) := rfl
    change bank (fieldCombinedEmbed t 16)
      (fieldInputBank t d n S) r.stk
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) = _
    rw [← hslot, bank_at]
    exact hpacked

#print axioms physical_source_field

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
