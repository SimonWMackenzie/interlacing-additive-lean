import CurrentAdditive.CanonicalWidthMultiply
import CurrentAdditive.CanonicalPhysicalSelectorStrideInit

/-! A fixed finite-stack program writes the canonical selector count
`H^(2^(t-1))` from unary H, including physical preparation of the fixed
exponent fuel and the zero-to-one accumulator initialization. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalSelectorBankPower

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

def program (t : ℕ) :=
  BitMachineRawSequence.program
    (SourceClauseFixedUnary.program (11 : Fin 12) (2 ^ (t - 1)))
    selectorStrideProgram
    (BitMachineRawSequence.leftLabel ()) ()
    (none, (false, false))

def initial (H : ℕ) : Fin 12 → List Bool :=
  fun k => if k = 6 then List.replicate H true else []

theorem physical_selector_bank_power (t H : ℕ) :
    ∃ steps ≤ (2 ^ (t - 1) + 1) +
        (MatrixWeightedPower.powerBound H (2 ^ (t - 1)) + 2) + 1,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (0 : SourceClauseFixedUnary.Label (2 ^ (t - 1)))),
          ((), (none, (false, false))), initial H⟩ :
          TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
        ⟨none, ((), (none, (false, false))),
          Function.update (initial H) 1
            (List.replicate (H ^ (2 ^ (t - 1))) true)⟩ := by
  let q := 2 ^ (t - 1)
  let S := initial H
  let S1 := Function.update S 11 (List.replicate q true)
  have hfixed := SourceClauseFixedUnary.run (11 : Fin 12) S q (by simp [S, initial])
  have hfixed' : ((advance (SourceClauseFixedUnary.program (11 : Fin 12) q))^[q+1])
      (⟨some (0 : SourceClauseFixedUnary.Label q), (), S⟩ :
        TM2.Cfg (fun _ : Fin 12 => Bool) _ _) = ⟨none, (), S1⟩ := by
    simpa [S1] using hfixed
  obtain ⟨u, hu, hpower⟩ := physical_selector_stride_from_blank H q S1
    (by simp [S1, S, initial])
    (by simp [S1, S, initial])
    (by simp [S1, S, initial])
    (by simp [S1, S, initial])
    (by simp [S1, S, initial])
    (by simp [S1, S, initial])
    (by simp [S1, S, initial])
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (11 : Fin 12) q) selectorStrideProgram
    (0 : SourceClauseFixedUnary.Label q)
    (BitMachineRawSequence.leftLabel ())
    () () (none, (false, false)) (none, (false, false))
    S S1 _ (q+1) u hfixed' hpower
  refine ⟨steps, by dsimp [q] at *; omega, ?_⟩
  have hbank : Function.update (Function.update S1 1
      (List.replicate (H ^ q) true)) 11 [] =
      Function.update S 1 (List.replicate (H ^ q) true) := by
    funext k
    fin_cases k <;> simp [S1, S, initial]
  rw [hbank] at hrun
  simpa [program, q, S] using hrun

#print axioms physical_selector_bank_power

end CurrentAdditive.FiniteFieldConstructor.CanonicalSelectorBankPower
