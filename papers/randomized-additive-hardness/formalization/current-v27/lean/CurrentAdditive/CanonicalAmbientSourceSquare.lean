import CurrentAdditive.CanonicalAmbientSourceSelectorBridge

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceSelectorClock {t : ℕ} (x : YaoSource t) : ℕ :=
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let K := arity t
  ((CanonicalSourcePrelude.sourceClock x +
    ((2*b+2)+(2*H+2)+(2*K+2)+2) + 1 +
    YaoDegreeClock.polynomial t (2^b) + 1) +
   (((2*H+2)+(2*K+2)+1) +
    ((2*K+2)+2+MatrixAddressMachine.exactTime H (K+1) 0+2)+1) + 1) +
  ((2*H+2) +
    ((2^(t-1)+1) +
      (MatrixWeightedPower.powerBound H (2^(t-1))+2)+1)+1) + 1

def sourceSquareOutput {t : ℕ} (x : YaoSource t) :
    Cell t 16 → List Bool :=
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  bank (squareEmbed t 16)
    (squareInputBank t 16 d (sourceSelectorOutput x))
    (Function.update (Function.update
      (CanonicalFieldSquare.initial d) 2
      (List.replicate 4 true)) 3
      (List.replicate ((2^d)^2) true))

def sourceThroughSquare (t : ℕ) :=
  BitMachineRawSequence.program (sourceThroughSelector t)
    (squareFullProgram t 16 (by decide))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false)))))
    (none, (none, ((), ((), (false, false)))))

theorem physical_source_square (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    ∃ steps ≤ sourceSelectorClock x +
      ((2*d+2) +
        ((2*d+2)+5+2+MatrixWeightedPower.powerBound 4 d+3)+1) + 1,
      ((advance (sourceThroughSquare t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      Paper2.YaoHeaderParser.startLabel)))))),
          (((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
            ((none, none), (none, ((), false)))),
            (none, ((), (none, (false, false))))),
            (none, (none, ((), ((), (false, false)))))),
          bank (sourceEmbed t 16) (blank t 16)
            (Paper2.YaoMachine.initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none,
          (((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
            ((none, none), (none, ((), false)))),
            (none, ((), (none, (false, false))))),
            (none, (none, ((), ((), (false, false)))))),
          sourceSquareOutput x⟩ := by
  dsimp only
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let S := sourceSelectorOutput x
  obtain ⟨u, hu, hprefix⟩ := physical_source_selector t ht x
  obtain ⟨hd, hblank, hscratch⟩ :=
    sourceSelectorOutput_square_input x
  obtain ⟨v, hv, hsquare⟩ := physical_square_full t 16 d
    (by decide) S hd hblank hscratch
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceThroughSelector t) (squareFullProgram t 16 (by decide))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              Paper2.YaoHeaderParser.startLabel)))))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false)))))
    ((((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false)))))
    (none, (none, ((), ((), (false, false)))))
    (none, (none, ((), ((), (false, false)))))
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x [])) S _ u v
    (by simpa [S] using hprefix)
    (by simpa [S, sourceSquareOutput, d, stackCfg] using hsquare)
  change u ≤ sourceSelectorClock x at hu
  dsimp [d] at hv
  exact ⟨steps, by omega,
    by simpa [sourceThroughSquare, sourceSquareOutput,
      S, d, stackCfg] using hrun⟩

#print axioms physical_source_square

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
