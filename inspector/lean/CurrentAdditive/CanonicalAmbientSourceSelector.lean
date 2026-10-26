import CurrentAdditive.CanonicalAmbientSourceDegreeWidthBridge

/-! Valid source through parser, cut-based degree, width, and selector-capacity
powering in one ambient TM2 program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceSelectorOutput {t : ℕ} (x : YaoSource t) :
    Cell t 16 → List Bool :=
  bank (selectorEmbed t 16)
    (selectorInputBank t 16 (paddedEdgeCount x.2.1)
      (sourceDegreeWidthOutput x))
    (Function.update
      (CanonicalSelectorBankPower.initial (paddedEdgeCount x.2.1)) 1
      (List.replicate
        ((paddedEdgeCount x.2.1)^(2^(t-1))) true))

def sourceThroughSelector (t : ℕ) :=
  BitMachineRawSequence.program (sourceThroughDegreeWidth t)
    (selectorFullProgram t 16)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false))))
    (none, ((), (none, (false, false))))

theorem physical_source_selector (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤
      ((CanonicalSourcePrelude.sourceClock x +
        ((2*b+2)+(2*H+2)+(2*K+2)+2) + 1 +
        YaoDegreeClock.polynomial t (2^b) + 1) +
       (((2*H+2)+(2*K+2)+1) +
        ((2*K+2)+2+MatrixAddressMachine.exactTime H (K+1) 0+2)+1) + 1) +
      ((2*H+2) +
        ((2^(t-1)+1) +
          (MatrixWeightedPower.powerBound H (2^(t-1))+2)+1)+1) + 1,
      ((advance (sourceThroughSelector t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    Paper2.YaoHeaderParser.startLabel))))),
          ((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
            ((none, none), (none, ((), false)))),
            (none, ((), (none, (false, false))))),
          bank (sourceEmbed t 16) (blank t 16)
            (Paper2.YaoMachine.initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none,
          ((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
            ((none, none), (none, ((), false)))),
            (none, ((), (none, (false, false))))),
          sourceSelectorOutput x⟩ := by
  dsimp only
  let H := paddedEdgeCount x.2.1
  let S := sourceDegreeWidthOutput x
  obtain ⟨u, hu, hprefix⟩ := physical_source_degree_width t ht x
  obtain ⟨_, hH, _⟩ := sourceDegreeWidthOutput_public x
  obtain ⟨hblank, _, _, _, hscratch⟩ :=
    sourceDegreeWidthOutput_next_blank x
  obtain ⟨v, hv, hselector⟩ := physical_selector_full t 16 H S
    hH hblank hscratch
  dsimp [H] at hv
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceThroughDegreeWidth t) (selectorFullProgram t 16)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            Paper2.YaoHeaderParser.startLabel))))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false))))
    (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false))))
    (none, ((), (none, (false, false))))
    (none, ((), (none, (false, false))))
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x [])) S _ u v
    (by simpa [S] using hprefix)
    (by simpa [S, sourceSelectorOutput, H, stackCfg] using hselector)
  exact ⟨steps, by omega,
    by simpa [sourceThroughSelector, sourceSelectorOutput,
      S, H, stackCfg] using hrun⟩

#print axioms physical_source_selector

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
