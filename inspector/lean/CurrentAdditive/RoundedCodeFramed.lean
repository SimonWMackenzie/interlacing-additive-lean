import CurrentAdditive.RoundedCodeOutput

namespace EthInapproximability.CurrentPaper.RoundedCodeOutput

open Turing BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorSerialization
open CurrentAdditive.RoundedDraw
noncomputable section

variable {K : Type*} [DecidableEq K]

def embeddedProgram (ι : Stack ↪ K) (l : Label) := stackStmt ι (program l)

/-- The exact input-bank contract permits sharing the serialized Code port
with a physical compiler's output. Every bank outside the chosen injection
is preserved, and no copying or clearing of those foreign banks is asserted. -/
theorem physical_from_bank {A : ℕ} (ι : Stack ↪ K) (S : K → List Bool)
    (c : Code) (hc : Positive c) (b N : ℕ)
    (hA : (meaning c).maxAlphabet ≤ A) (hN : (meaning c).maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool)
    (hinit : ∀ k, S (ι k) =
      (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b).stk k) :
    ∃ t ≤ RoundedCodeLoop.interpreterCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2 +
        codeSize c + 2,
      ((advance (embeddedProgram ι))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl RoundedCodeLoop.entry)), initial, S⟩ :
          TM2.Cfg (fun _ : K => Bool) Label Control) =
        ⟨none, initial, bank ι S (finalBank
          (CurrentAdditive.RoundedProgram.runProgram b N ⟨meaning c, hA⟩ hN bits)
          ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b)⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_forward c hc b N hA hN bits suffix
  have hh := BitMachineStackRun.run ι S program
    (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b) t
  change ((advance program)^[t]) _ = _ at hr
  rw [hr] at hh
  have hi : bank ι S (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b).stk = S := by
    apply bank_eq_self
    intro k
    exact (hinit k).symm
  change ((advance (embeddedProgram ι))^[t])
    ⟨some (BitMachineRawSequence.leftLabel (.inl RoundedCodeLoop.entry)), initial,
      bank ι S (start c (RoundedCodeLoop.tapeWord b N bits ++ suffix) b).stk⟩ = _ at hh
  rw [hi] at hh
  exact ⟨t, ht, hh⟩

theorem final_foreign (ι : Stack ↪ K) (S : K → List Bool)
    (out tape : List Bool) (b : ℕ) (k : K) (hk : ¬ ∃ i, ι i = k) :
    bank ι S (finalBank out tape b) k = S k := bank_outside ι S _ k hk

#print axioms physical_from_bank

end
end EthInapproximability.CurrentPaper.RoundedCodeOutput
