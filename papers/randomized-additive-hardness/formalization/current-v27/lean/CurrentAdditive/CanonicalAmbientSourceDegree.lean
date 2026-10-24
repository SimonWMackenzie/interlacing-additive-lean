import CurrentAdditive.CanonicalAmbientDegreeRun

/-! One literal source-parser-to-public-degree program. Its degree is computed
by the finite physical cut search, never supplied on the initial bank. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceDegreeBank {t : ℕ} (x : YaoSource t) :
    Cell t 16 → List Bool := degreeInputBank (by decide) x

def sourceThroughDegree (t : ℕ) :=
  BitMachineRawSequence.program
    (sourceToDegreeInputs t 16 (by decide)) (degreeStage t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    (CanonicalSourcePrelude.initialControl t, (none, (none, none)))
    ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
      YaoDegreeMachine.afterCtrl)

theorem sourceDegreeBank_inputs {t : ℕ} (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    sourceDegreeBank x (.degree 0) = List.replicate b true ∧
    sourceDegreeBank x (.degree 1) = List.replicate (2^b) true ∧
    (∀ i : Fin 16, 3 ≤ i.val → sourceDegreeBank x (.degree i) = []) := by
  dsimp only
  refine ⟨by simp [sourceDegreeBank, degreeInputBank], ?_, ?_⟩
  · simp [sourceDegreeBank, degreeInputBank, paddedEdgeCount]
  · intro i hi
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h1 : i ≠ 1 := by intro h; subst i; omega
    have h2 : i ≠ 2 := by intro h; subst i; omega
    simp [sourceDegreeBank, degreeInputBank, h0, h1, h2,
      sourceBank_degree]

theorem physical_source_through_degree (t : ℕ) (ht : 4 ≤ t)
    (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤ CanonicalSourcePrelude.sourceClock x +
        ((2*b+2) + (2*H+2) + (2*K+2) + 2) + 1 +
        YaoDegreeClock.polynomial t (2^b) + 1,
      ((advance (sourceThroughDegree t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel))),
          ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
          bank (sourceEmbed t 16) (blank t 16)
            (Paper2.YaoMachine.initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none,
          ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
              YaoDegreeMachine.afterCtrl)),
          bank (degreeEmbed t 16) (sourceDegreeBank x)
            (YaoDegreeMachine.finalBank
              (fun i : Fin 16 => sourceDegreeBank x (.degree i)) b t)⟩ := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let D := sourceDegreeBank x
  obtain ⟨hDb, hDH, hDblank⟩ := sourceDegreeBank_inputs x
  obtain ⟨s, hs, hsource⟩ :=
    physical_source_to_degree_inputs t 16 (by omega) (by decide) x
  obtain ⟨u, hu, hdegree⟩ :=
    physical_ambient_degree t b ht D hDb hDH hDblank
  dsimp [b] at hu
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceToDegreeInputs t 16 (by decide)) (degreeStage t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    (CanonicalSourcePrelude.initialControl t, (none, (none, none)))
    (CanonicalSourcePrelude.initialControl t, (none, (none, none)))
    ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
      YaoDegreeMachine.afterCtrl)
    ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
      YaoDegreeMachine.afterCtrl)
    (bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x [])) D _ s u
    (by simpa [D, sourceDegreeBank] using hsource) hdegree
  exact ⟨steps, by omega,
    by simpa [sourceThroughDegree, D, sourceDegreeBank, stackCfg]
      using hrun⟩

#print axioms sourceDegreeBank_inputs
#print axioms physical_source_through_degree

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
