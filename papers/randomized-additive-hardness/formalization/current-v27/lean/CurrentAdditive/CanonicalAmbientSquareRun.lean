import CurrentAdditive.CanonicalAmbientSelectorRun

/-! The public unary degree is physically copied to the field-pair square
input, then the fixed 4^d power program runs in the shared ambient bank. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def squareDPlace (t N : ℕ) (hN : 3 < N) : Fin 3 ↪ Cell t N :=
  ⟨![.degree ⟨3, hN⟩, .square 0, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem physical_square_input (t N d : ℕ) (hN : 3 < N)
    (S : Cell t N → List Bool)
    (hd : S (.degree ⟨3, hN⟩) = List.replicate d true)
    (hsquare : S (.square 0) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ((advance (MatrixStage4ScalarPreparationOps.copyProgram
      (squareDPlace t N hN)))^[2*d+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none,
        Function.update S (.square 0) (List.replicate d true)⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run
    (squareDPlace t N hN) S (by simpa [squareDPlace] using hscratch)
  simpa [squareDPlace, hd, hsquare] using hr

def squareStage (t N : ℕ) :=
  fun l => stackStmt (squareEmbed t N)
    (CanonicalFieldSquare.program l)

theorem physical_ambient_square (t N d : ℕ) (S : Cell t N → List Bool)
    (hlocal : ∀ i : Fin 9,
      S (.square i) = CanonicalFieldSquare.initial d i) :
    ∃ steps ≤ (2*d+2) + 5 + 2 +
        MatrixWeightedPower.powerBound 4 d + 3,
      ((advance (squareStage t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ((), ((), (false, false)))), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        stackCfg (squareEmbed t N) S
          (⟨none, (none, ((), ((), (false, false)))),
            Function.update (Function.update
              (CanonicalFieldSquare.initial d) 2
              (List.replicate 4 true)) 3
              (List.replicate ((2^d)^2) true)⟩ :
                TM2.Cfg (fun _ : Fin 9 => Bool) _ _) := by
  obtain ⟨steps, hsteps, hrun⟩ :=
    CanonicalFieldSquare.physical_field_square d
  refine ⟨steps, hsteps, ?_⟩
  have hbank := bank_eq_self (squareEmbed t N) S _
    (by intro i; exact (hlocal i).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (squareEmbed t N) S CanonicalFieldSquare.program
    (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      (none, ((), ((), (false, false)))),
      CanonicalFieldSquare.initial d⟩ :
        TM2.Cfg (fun _ : Fin 9 => Bool) _ _) steps
  have hr := congrArg (stackCfg (squareEmbed t N) S) hrun
  have hcombined := he.trans hr
  simpa [squareStage, stackCfg, hbank] using hcombined

#print axioms physical_square_input
#print axioms physical_ambient_square

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
