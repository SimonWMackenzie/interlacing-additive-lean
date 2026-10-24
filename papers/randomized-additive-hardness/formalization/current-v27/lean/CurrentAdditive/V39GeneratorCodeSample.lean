import CurrentAdditive.V39GeneratorCodeSize

namespace CurrentAdditive.V39GeneratorCode

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator

def sampleCode (n p₀ q₁ q₂ s w Q k m : ℕ) : Code :=
  .append (copies m (currentCodes n p₀ q₁ q₂ s w Q k).1)
    (copies m (currentCodes n p₀ q₁ q₂ s w Q k).2)

def sampleWord (n p₀ q₁ q₂ s w Q k m : ℕ)
    (z : (Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) : List Bool :=
  tupleWord (words n p₀ q₁ q₂ s w Q k).1 m z.1 ++
    tupleWord (words n p₀ q₁ q₂ s w Q k).2 m z.2

section Exact
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

/-- One compact first-order instruction datum prints both complete ordered
samples. Its exact Program tree is the current generator with deterministic
encoding at the leaves. -/
theorem sampleCode_exact (k m : ℕ) :
    meaning (sampleCode n p₀ q₁ q₂ s w Q k m) =
      Program.map (sampleWord n p₀ q₁ q₂ s w Q k m)
        (sampleProgram n p₀ q₁ q₂ s w Q k m) := by
  have h := currentCodes_exact n p₀ q₁ q₂ s w Q k
  exact pairCode_exact _ _ _ _ _ _
    (copies_word_exact _ _ _ h.1 m) (copies_word_exact _ _ _ h.2 m)

theorem sampleCode_draws_le (k m : ℕ) :
    (meaning (sampleCode n p₀ q₁ q₂ s w Q k m)).maxDraws ≤
      sampleDrawBudget p₀ q₁ q₂ s w Q k m := by
  rw [sampleCode_exact n p₀ q₁ q₂ s w Q k m, Program.maxDraws_map]
  exact draws_sampleProgram_le n p₀ q₁ q₂ s w Q k m

theorem sampleCode_alphabet_le (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ) :
    (meaning (sampleCode n p₀ q₁ q₂ s w Q k m)).maxAlphabet ≤
      publicA n s q₂ w Q p₀ := by
  rw [sampleCode_exact n p₀ q₁ q₂ s w Q k m, Program.maxAlphabet_map]
  exact alphabet_sampleProgram_le n p₀ q₁ q₂ s w Q hs hq₁ k m

#print axioms sampleCode_exact
#print axioms sampleCode_draws_le
#print axioms sampleCode_alphabet_le

end Exact

theorem sampleCode_size (n p₀ q₁ q₂ s w Q k m : ℕ) :
    codeSize (sampleCode n p₀ q₁ q₂ s w Q k m) =
      m * (codeSize (currentCodes n p₀ q₁ q₂ s w Q k).1 +
        codeSize (currentCodes n p₀ q₁ q₂ s w Q k).2 + 6) + 11 := by
  simp only [sampleCode, codeSize, Paper2.GeneratorSize.copies_size]
  ring

end CurrentAdditive.V39GeneratorCode
