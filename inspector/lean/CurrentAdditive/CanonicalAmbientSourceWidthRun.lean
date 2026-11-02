import CurrentAdditive.CanonicalAmbientSourceWidth

/-! One actual source-to-width program, with the multiplication run embedded. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceWidthInputBank {t N : ℕ} (hN : 2 < N) (x : YaoSource t) :
    Cell t N → List Bool :=
  Function.update
    (Function.update (degreeInputBank hN x) (.width 0)
      (List.replicate (paddedEdgeCount x.2.1) true))
    (.width 1) (List.replicate (arity t) true)

def sourceThroughWidth (t N : ℕ) (hN : 2 < N) :=
  BitMachineRawSequence.program
    (sourceToWidthInputs t N hN) (widthStage t N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      (none, none))
    (none, ((), false))

theorem sourceWidthInputBank_local {t N : ℕ} (hN : 2 < N)
    (x : YaoSource t) (i : Fin 8) :
    sourceWidthInputBank hN x (.width i) =
      CanonicalWidthMultiply.initial
        (paddedEdgeCount x.2.1) (arity t) i := by
  have hblank : sourceBank (N := N) x (.width i) = [] := by
    apply bank_outside (sourceEmbed t N) (blank t N) (sourceReady x)
    intro ⟨j, hj⟩
    cases hj
  have hd : degreeInputBank hN x (.width i) = [] := by
    simpa [degreeInputBank] using hblank
  fin_cases i <;>
    simp_all [sourceWidthInputBank, CanonicalWidthMultiply.initial]

theorem physical_source_through_width (t N : ℕ) (ht : 1 ≤ t)
    (hN : 2 < N) (x : YaoSource t) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let K := arity t
    ∃ steps ≤ CanonicalSourcePrelude.sourceClock x +
        ((2*b+2) + (2*H+2) + (2*K+2) + 2) + 1 +
        ((2*H+2) + (2*K+2) + 1) + 1 +
        ((2*K+2) + 2 +
          MatrixAddressMachine.exactTime H (K+1) 0 + 2) + 1,
      ((advance (sourceThroughWidth t N hN))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  Paper2.YaoHeaderParser.startLabel)))),
          (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            (none, none)), (none, ((), false))),
          bank (sourceEmbed t N) (blank t N)
            (Paper2.YaoMachine.initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none,
          (((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
            (none, none)), (none, ((), false))),
          bank (widthEmbed t N) (sourceWidthInputBank hN x)
            (Function.update (Function.update
              (CanonicalWidthMultiply.initial H K) 2
              (List.replicate (K+1) true)) 3
              (List.replicate (H*(K+1)) true))⟩ := by
  dsimp only
  let H := paddedEdgeCount x.2.1
  let K := arity t
  let W := sourceWidthInputBank hN x
  obtain ⟨s, hs, hsource⟩ := physical_source_width_inputs t N ht hN x
  obtain ⟨u, hu, hwidth⟩ := physical_ambient_width t N H K W
    (sourceWidthInputBank_local hN x)
  dsimp [H, K] at hu
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (sourceToWidthInputs t N hN) (widthStage t N)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      (none, none))
    ((CanonicalSourcePrelude.initialControl t, (none, (none, none))),
      (none, none))
    (none, ((), false)) (none, ((), false))
    (bank (sourceEmbed t N) (blank t N)
      (Paper2.YaoMachine.initBank 0 x [])) W _ s u
    (by simpa [W, sourceWidthInputBank] using hsource) hwidth
  exact ⟨steps, by omega, by simpa [sourceThroughWidth, W] using hrun⟩

#print axioms sourceWidthInputBank_local
#print axioms physical_source_through_width

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
