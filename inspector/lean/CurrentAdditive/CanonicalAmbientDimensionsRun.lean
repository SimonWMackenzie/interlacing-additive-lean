import CurrentAdditive.CanonicalAmbientSquareRun

/-! The fixed unary row/column multiplier embedded in the common ambient
machine; its five input words are a separate charged preparation obligation. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

def dimensionsStage (t N : ℕ) :=
  fun l => stackStmt (dimensionsEmbed t N)
    (CanonicalDimensionsMultiply.program l)

theorem physical_ambient_dimensions (t N v cap H R2 q : ℕ)
    (S : Cell t N → List Bool)
    (hlocal : ∀ i : Fin 11,
      S (.dimensions i) =
        CanonicalDimensionsMultiply.initial v cap H R2 q i) :
    ∃ steps ≤ MatrixAddressMachine.exactTime v cap 0 +
        MatrixAddressMachine.exactTime q H 0 +
        MatrixAddressMachine.exactTime (q*H) R2 0 + 2,
      ((advance (dimensionsStage t N))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          (false, (false, false)), S⟩ :
            TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
        stackCfg (dimensionsEmbed t N) S
          (⟨none, (false, (false, false)),
            Function.update
              (Function.update
                (Function.update
                  (CanonicalDimensionsMultiply.initial v cap H R2 q) 5
                  (List.replicate (v*cap) true)) 6
                (List.replicate (q*H) true)) 7
              (List.replicate (q*H*R2) true)⟩ :
                TM2.Cfg (fun _ : Fin 11 => Bool) _ _) := by
  obtain ⟨steps, hsteps, hrun⟩ :=
    CanonicalDimensionsMultiply.physical_dimensions v cap H R2 q
  refine ⟨steps, hsteps, ?_⟩
  have hbank := bank_eq_self (dimensionsEmbed t N) S _
    (by intro i; exact (hlocal i).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (dimensionsEmbed t N) S CanonicalDimensionsMultiply.program
    (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
      (false, (false, false)),
      CanonicalDimensionsMultiply.initial v cap H R2 q⟩ :
        TM2.Cfg (fun _ : Fin 11 => Bool) _ _) steps
  have hr := congrArg (stackCfg (dimensionsEmbed t N) S) hrun
  have hcombined := he.trans hr
  simpa [dimensionsStage, stackCfg, hbank] using hcombined

#print axioms physical_ambient_dimensions

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
