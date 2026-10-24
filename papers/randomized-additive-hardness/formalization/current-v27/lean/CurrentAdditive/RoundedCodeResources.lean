import CurrentAdditive.RoundedCodeCodec
import CurrentAdditive.RoundedCodeSharedPort

namespace EthInapproximability.CurrentPaper.RoundedCodeOutput

open Turing BitMachineEncoding Paper2.GeneratorCode Paper2.GeneratorPositive
open Paper2.GeneratorSerialization Paper2.RecursiveSamplingProgram
open CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000

def publishedCoefficient : ℕ := RoundedCodeLoop.interpreterCoefficient + 1

theorem forward_clock (R b N : ℕ) :
    RoundedCodeLoop.interpreterCoefficient * (N + 1) * (R + b + 3) ^ 2 + R + 2 ≤
      publishedCoefficient * (N + 1) * (R + b + 3) ^ 2 := by
  let X := R + b + 3
  have hx : 1 ≤ X := by dsimp [X]; omega
  have hx2 : X ≤ X ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_left X hx
  have hRX : R + 2 ≤ X := by dsimp [X]; omega
  have hn : X ^ 2 ≤ (N + 1) * X ^ 2 := by
    simpa using Nat.mul_le_mul_right (X ^ 2) (show 1 ≤ N + 1 by omega)
  have hsmall : R + 2 ≤ (N + 1) * X ^ 2 := hRX.trans (hx2.trans hn)
  calc
    RoundedCodeLoop.interpreterCoefficient * (N + 1) * (R + b + 3) ^ 2 + R + 2 ≤
        RoundedCodeLoop.interpreterCoefficient * (N + 1) * X ^ 2 + (N + 1) * X ^ 2 := by
      dsimp only [X] at hsmall ⊢
      omega
    _ = publishedCoefficient * (N + 1) * (R + b + 3) ^ 2 := by
      unfold publishedCoefficient; dsimp [X]; ring

theorem physical_codec_polynomial {α : Type*} {A : ℕ} (c : Code) (hc : Positive c)
    (p : Program α) (encode : α → List Bool) (he : meaning c = Program.map encode p)
    (b N : ℕ) (hA : p.maxAlphabet ≤ A) (hN : p.maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ publishedCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2,
      run t (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b) =
        ⟨none, initial, finalBank
          (encode (CurrentAdditive.RoundedProgram.runProgram b N ⟨p, hA⟩ hN bits))
          ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_codec c hc p encode he b N hA hN bits suffix
  exact ⟨t, ht.trans (forward_clock _ _ _), hr⟩

theorem physical_shared_codec {J α : Type*} [DecidableEq J] {A : ℕ}
    (source : J) (F : J → List Bool) (c : Code) (hc : Positive c)
    (hcode : F source = encodeCode c) (p : Program α) (encode : α → List Bool)
    (he : meaning c = Program.map encode p) (b N : ℕ)
    (hA : p.maxAlphabet ≤ A) (hN : p.maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ publishedCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2,
      ((BitMachineEncoding.advance (embeddedProgram (sharedSlots source)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl RoundedCodeLoop.entry)), initial,
          sharedInitial F (RoundedCodeLoop.tapeWord b N bits ++ suffix) b⟩ :
            TM2.Cfg (fun _ : SharedBank J => Bool) Label Control) =
        ⟨none, initial, sharedFinal source F
          (encode (CurrentAdditive.RoundedProgram.runProgram b N ⟨p, hA⟩ hN bits))
          ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b⟩ := by
  have hac : (meaning c).maxAlphabet ≤ A := by simpa only [he, Program.maxAlphabet_map] using hA
  have hnc : (meaning c).maxDraws ≤ N := by simpa only [he, Program.maxDraws_map] using hN
  obtain ⟨t, ht, hr⟩ := physical_shared source F c hc hcode b N hac hnc bits suffix
  exact ⟨t, ht.trans (forward_clock _ _ _),
    by simpa only [runProgram_of_code c p encode he b N hA hN bits] using hr⟩

#print axioms forward_clock
#print axioms physical_shared_codec

end
end EthInapproximability.CurrentPaper.RoundedCodeOutput
