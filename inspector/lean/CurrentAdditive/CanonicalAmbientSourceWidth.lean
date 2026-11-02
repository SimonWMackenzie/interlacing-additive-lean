import CurrentAdditive.CanonicalAmbientWidthInputs

/-! The valid encoded source drives both public degree inputs and width inputs
through one literal ambient program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def degreeInputBank {t N : ℕ} (hN : 2 < N) (x : YaoSource t) :
    Cell t N → List Bool :=
  Function.update
    (Function.update
      (Function.update (sourceBank x) (.degree ⟨0, by omega⟩)
        (List.replicate (paddedEdgeBits x.2.1) true))
      (.degree ⟨1, by omega⟩)
      (List.replicate (paddedEdgeCount x.2.1) true))
    (.degree ⟨2, hN⟩) (List.replicate (arity t) true)

def sourceToWidthInputs (t N : ℕ) (hN : 2 < N) :=
  BitMachineRawSequence.program
    (sourceToDegreeInputs t N hN) (widthInputProgram t N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (CanonicalSourcePrelude.initialControl t, (none, (none, none)))
    (none, none)

theorem physical_source_width_inputs (t N : ℕ) (ht : 1 ≤ t)
    (hN : 2 < N) (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤ CanonicalSourcePrelude.sourceClock x +
        ((2*b+2) + (2*H+2) + (2*K+2) + 2) + 1 +
        ((2*H+2) + (2*K+2) + 1) + 1,
      ((advance (sourceToWidthInputs t N hN))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel))),
          ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            (none, none)),
          bank (sourceEmbed t N) (blank t N)
            (Paper2.YaoMachine.initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none,
          ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            (none, none)),
          Function.update
            (Function.update (degreeInputBank hN x) (.width 0)
              (List.replicate H true)) (.width 1)
              (List.replicate K true)⟩ := by
  dsimp only
  let H := paddedEdgeCount x.2.1
  let K := arity t
  let D := degreeInputBank hN x
  have hp := sourceReady_public_cells x
  obtain ⟨_, _, _, _, hH, hK⟩ := hp
  have hDsourceH : D (.source (sN 6)) = List.replicate H true := by
    simpa [D, degreeInputBank, H, sourceBank_source] using hH
  have hDsourceK : D (.source (sN 9)) = List.replicate K true := by
    simpa [D, degreeInputBank, K, sourceBank_source] using hK
  have hDwidth (i : Fin 8) : D (.width i) = [] := by
    have hblank : sourceBank (N := N) x (.width i) = [] := by
      apply bank_outside (sourceEmbed t N) (blank t N) (sourceReady x)
      intro ⟨j, hj⟩
      cases hj
    simpa [D, degreeInputBank] using hblank
  have hDscratch : D (.copyScratch 0) = [] := by
    simpa [D, degreeInputBank] using sourceBank_copyScratch (N := N) x 0
  obtain ⟨s, hs, hsource⟩ := physical_source_to_degree_inputs t N ht hN x
  obtain ⟨u, hu, hwidth⟩ := physical_width_inputs t N H K D
    hDsourceH hDsourceK (hDwidth 0) (hDwidth 1) hDscratch
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceToDegreeInputs t N hN) (widthInputProgram t N)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (CanonicalSourcePrelude.initialControl t, (none, (none, none)))
    (CanonicalSourcePrelude.initialControl t, (none, (none, none)))
    (none, none) (none, none)
    (bank (sourceEmbed t N) (blank t N) (Paper2.YaoMachine.initBank 0 x []))
    D _ s u (by simpa [D, degreeInputBank] using hsource) hwidth
  exact ⟨steps, by omega, by simpa [sourceToWidthInputs, D] using hrun⟩

#print axioms physical_source_width_inputs

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
