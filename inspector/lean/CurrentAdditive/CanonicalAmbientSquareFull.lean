import CurrentAdditive.CanonicalAmbientSelectorFull

/-! Physical degree copy followed by 4^d powering as one ambient TM2
program. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def squareInputBank (t N d : ℕ) (S : Cell t N → List Bool) :=
  Function.update S (.square 0) (List.replicate d true)

def squareFullProgram (t N : ℕ) (hN : 3 < N) :=
  BitMachineRawSequence.program
    (MatrixStage4ScalarPreparationOps.copyProgram (squareDPlace t N hN))
    (squareStage t N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none (none, ((), ((), (false, false))))

theorem squareInputBank_local (t N d : ℕ) (S : Cell t N → List Bool)
    (hblank : ∀ i : Fin 9, S (.square i) = [])
    (i : Fin 9) :
    squareInputBank t N d S (.square i) =
      CanonicalFieldSquare.initial d i := by
  fin_cases i <;>
    simp_all [squareInputBank, CanonicalFieldSquare.initial]

theorem physical_square_full (t N d : ℕ) (hN : 3 < N)
    (S : Cell t N → List Bool)
    (hd : S (.degree ⟨3, hN⟩) = List.replicate d true)
    (hblank : ∀ i : Fin 9, S (.square i) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ∃ steps ≤ (2*d+2) +
        ((2*d+2) + 5 + 2 + MatrixWeightedPower.powerBound 4 d + 3) + 1,
      ((advance (squareFullProgram t N hN))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, (none, ((), ((), (false, false))))), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        ⟨none, (none, (none, ((), ((), (false, false))))),
          bank (squareEmbed t N) (squareInputBank t N d S)
            (Function.update (Function.update
              (CanonicalFieldSquare.initial d) 2
              (List.replicate 4 true)) 3
              (List.replicate ((2^d)^2) true))⟩ := by
  let S1 := squareInputBank t N d S
  have hcopy := physical_square_input t N d hN S hd (hblank 0) hscratch
  obtain ⟨u, hu, hpower⟩ := physical_ambient_square t N d S1
    (squareInputBank_local t N d S hblank)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (MatrixStage4ScalarPreparationOps.copyProgram (squareDPlace t N hN))
    (squareStage t N)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, ((), ((), (false, false))))
    (none, ((), ((), (false, false))))
    S S1 _ (2*d+2) u
    (by simpa [S1, squareInputBank] using hcopy) hpower
  exact ⟨steps, by omega,
    by simpa [squareFullProgram, S1, squareInputBank, stackCfg] using hrun⟩

#print axioms physical_square_full

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
