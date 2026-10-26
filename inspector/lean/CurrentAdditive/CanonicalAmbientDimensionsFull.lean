import CurrentAdditive.CanonicalDimensionsBulkPrep
import CurrentAdditive.CanonicalAmbientDimensionsRun

/-! A single ambient program copies four public dimensions, writes the fixed
selector count, and multiplies the row and column counts. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine

def dimensionPrepared (t v cap H R2 : ℕ)
    (S : Cell t 16 → List Bool) :=
  Function.update (CopyFill.fill (dimensionJobs t) S)
    (.dimensions 4) (List.replicate (2^(t-1)) true)

def dimensionsFullProgram (t : ℕ) :=
  BitMachineRawSequence.program (dimensionPrepProgram t)
    (dimensionsStage t 16)
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (MultiMove.initial, ()) (false, (false, false))

theorem dimensionPrepared_local (t v cap H R2 : ℕ)
    (S : Cell t 16 → List Bool)
    (hblank : ∀ i : Fin 11, S (.dimensions i) = [])
    (hv : S (.source (sN 3)) = List.replicate v true)
    (hcap : S (.selector 1) = List.replicate cap true)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hR2 : S (.square 3) = List.replicate R2 true) :
    ∀ i : Fin 11,
      dimensionPrepared t v cap H R2 S (.dimensions i) =
        CanonicalDimensionsMultiply.initial v cap H R2 (2^(t-1)) i := by
  intro i
  have h := dimensionCopy_local t v cap H R2 S hblank hv hcap hH hR2
  fin_cases i <;>
    simp_all [dimensionPrepared, CanonicalDimensionsMultiply.initial]

theorem physical_dimensions_full (t v cap H R2 : ℕ)
    (S : Cell t 16 → List Bool)
    (hblank : ∀ i : Fin 11, S (.dimensions i) = [])
    (hscratch : S (.copyScratch 0) = [])
    (hv : S (.source (sN 3)) = List.replicate v true)
    (hcap : S (.selector 1) = List.replicate cap true)
    (hH : S (.source (sN 6)) = List.replicate H true)
    (hR2 : S (.square 3) = List.replicate R2 true) :
    ∃ steps ≤ CopyFill.fillCost (dimensionJobs t) S + 1 +
        (2^(t-1)+1) + 1 +
        (MatrixAddressMachine.exactTime v cap 0 +
          MatrixAddressMachine.exactTime (2^(t-1)) H 0 +
          MatrixAddressMachine.exactTime ((2^(t-1))*H) R2 0 + 2) + 1,
      ((advance (dimensionsFullProgram t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob)))),
          ((MultiMove.initial, ()), (false, (false, false))), S⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, ((MultiMove.initial, ()), (false, (false, false))),
          bank (dimensionsEmbed t 16)
            (dimensionPrepared t v cap H R2 S)
            (Function.update
              (Function.update
                (Function.update
                  (CanonicalDimensionsMultiply.initial v cap H R2 (2^(t-1))) 5
                  (List.replicate (v*cap) true)) 6
                (List.replicate ((2^(t-1))*H) true)) 7
              (List.replicate ((2^(t-1))*H*R2) true))⟩ := by
  let S1 := dimensionPrepared t v cap H R2 S
  obtain ⟨u, hu, hprep⟩ := physical_dimension_prep t v cap H R2 S
    hblank hscratch hv hcap hH hR2
  obtain ⟨w, hw, hdim⟩ := physical_ambient_dimensions t 16
    v cap H R2 (2^(t-1)) S1
      (dimensionPrepared_local t v cap H R2 S hblank hv hcap hH hR2)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (dimensionPrepProgram t) (dimensionsStage t 16)
    (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel ((dimensionJobs t).map CopyFill.toJob)))
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (MultiMove.initial, ()) (MultiMove.initial, ())
    (false, (false, false)) (false, (false, false))
    S S1 _ u w
    (by simpa [S1, dimensionPrepared] using hprep) hdim
  exact ⟨steps, by omega,
    by simpa [dimensionsFullProgram, S1, dimensionPrepared, stackCfg] using hrun⟩

#print axioms dimensionPrepared_local
#print axioms physical_dimensions_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
