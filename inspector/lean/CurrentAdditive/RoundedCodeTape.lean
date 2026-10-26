import CurrentAdditive.RoundedCodeSemantics
namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Paper2.GeneratorCode CurrentAdditive.RoundedDraw
noncomputable section

def consumed (b : ℕ) : (N : ℕ) → State → BitBlocks b N → ℕ
  | 0, _, _ => 0
  | N+1, s, bits =>
      if (Paper2.GeneratorCode.normalize s).todo = [] then 0 else
        consumed b N (roundedNext s b bits.1) bits.2 + 1

theorem consumed_le (b N : ℕ) (s : State) (bits : BitBlocks b N) :
    consumed b N s bits ≤ N := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      dsimp only [consumed]
      split
      · omega
      · have ht := ih (roundedNext s b bits.1) bits.2; omega

theorem tapeWord_length (b N : ℕ) (bits : BitBlocks b N) :
    (tapeWord b N bits).length = b * N := by
  induction N with
  | zero => simp [tapeWord]
  | succ N ih =>
      simp only [tapeWord, List.length_append, Paper2.CappedTicketMachine.ticketWord_length, ih]
      ring

/-- The physical result's unused word is literally a suffix of the reserved
tape after exactly b bits for each actual finite-choice request. -/
theorem exact_tape_split (b N : ℕ) (s : State) (bits : BitBlocks b N) :
    ∃ usedWord : List Bool, usedWord.length = b * consumed b N s bits ∧
      tapeWord b N bits = usedWord ++ (execute b N s bits).2 := by
  induction N generalizing s with
  | zero => exact ⟨[], by simp [consumed], rfl⟩
  | succ N ih =>
      by_cases hd : (Paper2.GeneratorCode.normalize s).todo = []
      · exact ⟨[], by simp [consumed, hd], by simp [execute, hd]⟩
      · obtain ⟨usedWord, hlen, hword⟩ := ih (roundedNext s b bits.1) bits.2
        refine ⟨Paper2.CappedTicketMachine.ticketWord bits.1 ++ usedWord, ?_, ?_⟩
        · simp only [List.length_append, Paper2.CappedTicketMachine.ticketWord_length,
            consumed, hd, ↓reduceIte, hlen]
          ring
        · simpa only [tapeWord, execute, hd, ↓reduceIte, List.append_assoc] using
            congrArg (fun tail => Paper2.CappedTicketMachine.ticketWord bits.1 ++ tail) hword

theorem unused_length (b N : ℕ) (s : State) (bits : BitBlocks b N) :
    (execute b N s bits).2.length = b * (N - consumed b N s bits) := by
  obtain ⟨usedWord, hlen, hword⟩ := exact_tape_split b N s bits
  have hall := tapeWord_length b N bits
  rw [hword, List.length_append, hlen] at hall
  have hused := consumed_le b N s bits
  have hid : b * N = b * consumed b N s bits + b * (N - consumed b N s bits) := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hused]
  omega

#print axioms exact_tape_split

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
