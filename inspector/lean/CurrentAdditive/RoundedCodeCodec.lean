import CurrentAdditive.RoundedCodeFramed
import CurrentAdditive.RoundedProgramMap

namespace EthInapproximability.CurrentPaper.RoundedCodeOutput

open Turing BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorSerialization
open Paper2.RecursiveSamplingProgram CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000

theorem final_result (out tape : List Bool) (b : ℕ) :
    finalBank out tape b resultPort = out := by simp [finalBank]

theorem final_tape (out tape : List Bool) (b : ℕ) :
    finalBank out tape b tapePort = tape := by
  simp [finalBank, tapePort, resultPort, RoundedCodeReset.code, RoundedCodeReset.tape,
    RoundedCodeDraw.oldTape, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d]

theorem final_width (out tape : List Bool) (b : ℕ) :
    finalBank out tape b widthPort = List.replicate b true := by
  simp [finalBank, widthPort, tapePort, resultPort, RoundedCodeReset.code,
    RoundedCodeReset.tape, RoundedCodeReset.width, RoundedCodeDraw.oldTape,
    RoundedCodeDraw.oldWidth, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d]

theorem final_other (out tape : List Bool) (b : ℕ) (k : Stack)
    (hr : k ≠ resultPort) (ht : k ≠ tapePort) (hb : k ≠ widthPort) :
    finalBank out tape b k = [] := by simp [finalBank, hr, ht, hb]

theorem runProgram_of_code {α : Type*} {A : ℕ} (c : Code) (p : Program α)
    (encode : α → List Bool) (he : meaning c = Program.map encode p)
    (b N : ℕ) (hA : p.maxAlphabet ≤ A) (hN : p.maxDraws ≤ N)
    (bits : BitBlocks b N) :
    CurrentAdditive.RoundedProgram.runProgram b N
        ⟨meaning c, by simpa only [he, Program.maxAlphabet_map] using hA⟩
        (by simpa only [he, Program.maxDraws_map] using hN) bits =
      encode (CurrentAdditive.RoundedProgram.runProgram b N ⟨p, hA⟩ hN bits) := by
  simpa only [he, CurrentAdditive.RoundedProgram.mapState] using
    CurrentAdditive.RoundedProgram.runProgram_map encode b N ⟨p, hA⟩ hN bits

/-- An exact source-Code compiler equality is enough to obtain literal
forward encoded samples from the actual fixed rounded bit machine. -/
theorem physical_codec {α : Type*} {A : ℕ} (c : Code) (hc : Positive c)
    (p : Program α) (encode : α → List Bool) (he : meaning c = Program.map encode p)
    (b N : ℕ) (hA : p.maxAlphabet ≤ A) (hN : p.maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ RoundedCodeLoop.interpreterCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2 +
        codeSize c + 2,
      run t (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b) =
        ⟨none, initial, finalBank
          (encode (CurrentAdditive.RoundedProgram.runProgram b N ⟨p, hA⟩ hN bits))
          ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b⟩ := by
  have hac : (meaning c).maxAlphabet ≤ A := by simpa only [he, Program.maxAlphabet_map] using hA
  have hnc : (meaning c).maxDraws ≤ N := by simpa only [he, Program.maxDraws_map] using hN
  obtain ⟨t, ht, hr⟩ := physical_forward c hc b N hac hnc bits suffix
  exact ⟨t, ht, by simpa only [runProgram_of_code c p encode he b N hA hN bits] using hr⟩

theorem encoded_event_error_200 {α : Type*} {A : ℕ} (p : Program α)
    (encode : α → List Bool) (b N : ℕ) (hA : p.maxAlphabet ≤ A) (hN : p.maxDraws ≤ N)
    (hbudget : 200 * A * N ≤ 2 ^ b) (E : Set (List Bool)) :
    |(bitBlocksLaw b N).prob (fun bits =>
        E (encode (CurrentAdditive.RoundedProgram.runProgram b N ⟨p, hA⟩ hN bits))) -
      p.eventProb {a | E (encode a)}| ≤ (1 : ℝ) / 200 :=
  CurrentAdditive.RoundedProgram.runProgram_event_error_200 b N ⟨p, hA⟩ hN hbudget {a | E (encode a)}

#print axioms physical_codec
#print axioms encoded_event_error_200

end
end EthInapproximability.CurrentPaper.RoundedCodeOutput
