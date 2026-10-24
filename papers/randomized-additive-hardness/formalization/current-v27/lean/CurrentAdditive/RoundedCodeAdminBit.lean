import CurrentAdditive.RoundedCodeAdminSteps

namespace EthInapproximability.CurrentPaper.RoundedCodeAdmin

open Turing BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
noncomputable section

private theorem inputBank_update (S : RoundedCodeDraw.OldStack → List Bool)
    (k : RoundedCodeDraw.OldStack) (word : List Bool) :
    Function.update (RoundedCodeDraw.inputBank S) (.inl k) word =
      RoundedCodeDraw.inputBank (Function.update S k word) := by
  funext j
  rcases j with j | j <;> simp [RoundedCodeDraw.inputBank, Function.update]

def bitOldBank (cs : List Code) (out bits : List Bool) (b : ℕ) :
    RoundedCodeDraw.OldStack → List Bool :=
  Function.update (readyOldBank ⟨.bit :: cs, out⟩ bits b)
    RoundedCodeDraw.oldAlphabet [true, true]

theorem route_bit (cs : List Code) (out bits : List Bool) (b : ℕ) :
    run 1 (ready ⟨.bit :: cs, out⟩ bits b) =
      drawCfg .bit (bitOldBank cs out bits b) := by
  have hA : RoundedCodeDraw.inputBank (readyOldBank ⟨.bit :: cs, out⟩ bits b)
      (.inl RoundedCodeDraw.oldAlphabet) = [] := rfl
  change BitMachineEncoding.advance program
      ⟨some .route, (kindControl .bit, RoundedLoadedDraw.initial),
        RoundedCodeDraw.inputBank (readyOldBank ⟨.bit :: cs, out⟩ bits b)⟩ = _
  simp only [BitMachineEncoding.advance, TM2.step, Option.getD_some, program, TM2.stepAux,
    kindControl, Option.isSome_some, cond_true, decide_true, hA,
    Function.update_self, Function.update_idem]
  change (⟨some (.draw .bit drawStart), (kindControl .bit, RoundedLoadedDraw.initial),
    Function.update (RoundedCodeDraw.inputBank (readyOldBank ⟨.bit :: cs, out⟩ bits b))
      (.inl RoundedCodeDraw.oldAlphabet) [true, true]⟩ : Config) = _
  rw [inputBank_update]
  rfl

/-- A source `.bit` is a rounded uniform-two request and consumes the same
full b-bit block as every other finite choice. -/
theorem bit_from_ready (b : ℕ) (cs : List Code) (out : List Bool)
    (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ 1 + RoundedLoadedClock.coefficient * (2 + b + 2) ^ 2,
      let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
      let S := bitOldBank cs out input b
      run t (ready ⟨.bit :: cs, out⟩ input b) =
        ⟨none, (kindControl .bit, RoundedLoadedDraw.initial),
          RoundedCodeDraw.resultBank S 2 b input suffix
            ((Paper2.RecursiveLabelCodecScratch.finCodec 2).encode
              (CurrentAdditive.RoundedDraw.draw 2 (2 ^ b) (by decide) (by positivity)
                (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
  let S := bitOldBank cs out input b
  obtain ⟨t, ht, hr⟩ := draw_run .bit S 2 b (by decide) bits suffix
    (by simp [S, bitOldBank])
    (by simp [S, bitOldBank, RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldAlphabet,
      Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h]; rfl)
    (by simp [S, bitOldBank, RoundedCodeDraw.oldTape, RoundedCodeDraw.oldAlphabet,
      Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h]; rfl)
    (by simp [S, bitOldBank, RoundedCodeDraw.oldResult, RoundedCodeDraw.oldAlphabet,
      Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h]; rfl)
  refine ⟨1 + t, by omega, ?_⟩
  dsimp only
  have hjoin : run (1 + t) (ready ⟨.bit :: cs, out⟩ input b) =
      run t (run 1 (ready ⟨.bit :: cs, out⟩ input b)) := by
    rw [run, Nat.add_comm 1 t, Function.iterate_add_apply]
    rfl
  rw [hjoin, route_bit]
  exact hr

#print axioms route_bit
#print axioms bit_from_ready

end
end EthInapproximability.CurrentPaper.RoundedCodeAdmin
