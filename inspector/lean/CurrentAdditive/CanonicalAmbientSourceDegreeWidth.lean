import CurrentAdditive.CanonicalAmbientSourceDegreeBridge

/-! Source parsing, real degree construction, and width multiplication in one
literal ambient program from a valid encoded source. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceDegreeWidthOutput {t : ℕ} (x : YaoSource t) :
    Cell t 16 → List Bool :=
  bank (widthEmbed t 16)
    (widthInputBank t 16 (paddedEdgeCount x.2.1) (arity t)
      (sourceDegreeOutput x))
    (Function.update (Function.update
      (CanonicalWidthMultiply.initial (paddedEdgeCount x.2.1) (arity t)) 2
      (List.replicate (arity t+1) true)) 3
      (List.replicate (paddedEdgeCount x.2.1*(arity t+1)) true))

def sourceThroughDegreeWidth (t : ℕ) :=
  BitMachineRawSequence.program (sourceThroughDegree t)
    (widthFullProgram t 16)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl))
    ((none, none), (none, ((), false)))

theorem physical_source_degree_width (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤
        (CanonicalSourcePrelude.sourceClock x +
          ((2*b+2)+(2*H+2)+(2*K+2)+2) + 1 +
          YaoDegreeClock.polynomial t (2^b) + 1) +
        (((2*H+2)+(2*K+2)+1) +
          ((2*K+2)+2+MatrixAddressMachine.exactTime H (K+1) 0+2)+1) + 1,
      ((advance (sourceThroughDegreeWidth t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  Paper2.YaoHeaderParser.startLabel)))),
          (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
            ((none, none), (none, ((), false)))),
          bank (sourceEmbed t 16) (blank t 16)
            (Paper2.YaoMachine.initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none,
          (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
            ((none, none), (none, ((), false)))),
          sourceDegreeWidthOutput x⟩ := by
  dsimp only
  let H := paddedEdgeCount x.2.1
  let K := arity t
  let S := sourceDegreeOutput x
  obtain ⟨u, hu, hfirst⟩ := physical_source_through_degree t ht x
  obtain ⟨_, hH, hK⟩ := sourceDegreeOutput_public x
  obtain ⟨hwidthBlank, _, _, _, _, hscratch⟩ :=
    sourceDegreeOutput_foreign_blank x
  obtain ⟨v, hv, hsecond⟩ := physical_width_full t 16 H K S
    hH hK hwidthBlank hscratch
  dsimp [H, K] at hv
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceThroughDegree t) (widthFullProgram t 16)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          Paper2.YaoHeaderParser.startLabel)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl))
    ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl))
    ((none, none), (none, ((), false)))
    ((none, none), (none, ((), false)))
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x [])) S _ u v
    (by simpa [S, sourceDegreeOutput] using hfirst) hsecond
  exact ⟨steps, by omega,
    by simpa [sourceThroughDegreeWidth, sourceDegreeWidthOutput,
      S, H, K, stackCfg] using hrun⟩

#print axioms physical_source_degree_width

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
