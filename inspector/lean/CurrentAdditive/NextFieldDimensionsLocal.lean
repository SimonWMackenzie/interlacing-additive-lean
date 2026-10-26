import CurrentAdditive.NextSourceFieldBridge

/-! The field printer's untouched public cells directly drive the physical
row/column dimension multiplier. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def sourceDimensionsOutput {t : ℕ} (x : YaoSource t) (u : ℕ) :
    Cell t 16 → List Bool :=
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let d := publicFieldDegree b t
  let cap := H^(2^(t-1))
  let R2 := (2^d)^2
  bank (dimensionsEmbed t 16)
    (dimensionPrepared t x.1 cap H R2 (sourceFieldOutput x u))
    (Function.update
      (Function.update
        (Function.update
          (CanonicalDimensionsMultiply.initial x.1 cap H R2 (2^(t-1))) 5
          (List.replicate (x.1*cap) true)) 6
        (List.replicate ((2^(t-1))*H) true)) 7
      (List.replicate ((2^(t-1))*H*R2) true))

theorem physical_dimensions_after_field (t : ℕ) (x : YaoSource t)
    (u : ℕ) :
    let b := paddedEdgeBits x.2.1
    let H := paddedEdgeCount x.2.1
    let d := publicFieldDegree b t
    let cap := H^(2^(t-1))
    let R2 := (2^d)^2
    let S := sourceFieldOutput x u
    ∃ steps ≤ CopyFill.fillCost (dimensionJobs t) S + 1 +
        (2^(t-1)+1) + 1 +
        (MatrixAddressMachine.exactTime x.1 cap 0 +
          MatrixAddressMachine.exactTime (2^(t-1)) H 0 +
          MatrixAddressMachine.exactTime ((2^(t-1))*H) R2 0 + 2) + 1,
      ((advance (dimensionsFullProgram t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob)))),
          ((MultiMove.initial, ()), (false, (false, false))), S⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, ((MultiMove.initial, ()), (false, (false, false))),
          sourceDimensionsOutput x u⟩ := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let d := publicFieldDegree b t
  let cap := H^(2^(t-1))
  let R2 := (2^d)^2
  let S := sourceFieldOutput x u
  obtain ⟨_, _, hv, _, hH, _, _, hcap, hR2⟩ :=
    sourceFieldOutput_public x u
  obtain ⟨hblank, _, _, _, hscratch⟩ :=
    sourceFieldOutput_later_blank x u
  obtain ⟨steps, hsteps, hrun⟩ :=
    physical_dimensions_full t x.1 cap H R2 S
      hblank hscratch hv hcap hH hR2
  exact ⟨steps, hsteps,
    by simpa [sourceDimensionsOutput, S, H, d, cap, R2, b]
      using hrun⟩

#print axioms physical_dimensions_after_field

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
