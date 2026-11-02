import CurrentAdditive.V39DeadTaggedCompiler
import CurrentAdditive.V39GeneratorCodeSample
namespace CurrentAdditive.V39DeadTaggedCompiler

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.RecursiveLabelCodecScratch
open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
open CurrentAdditive.V39GeneratorCode CurrentAdditive.V39RecursiveGenerator

def deadCodes (n p₀ q₁ q₂ s w Q : ℕ) : ℕ → Code × Code
  | 0 => (copies p₀ .bit, .ticket p₀)
  | k + 1 =>
    let previous := deadCodes n p₀ q₁ q₂ s w Q k
    (copies Q (.append (.ticket w) (deadTaggedCode q₁ q₂ s previous.2)),
      .append (.ticket Q) (copies w (graphRowsCode (V := Fin n) q₁ q₂ s previous.1)))

section Exact
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

theorem deadCodes_exact (k : ℕ) :
    meaning (deadCodes n p₀ q₁ q₂ s w Q k).1 =
        Program.map (words n p₀ q₁ q₂ s w Q k).1 (V39RecursiveGenerator.programs n p₀ q₁ q₂ s w Q k).1 ∧
    meaning (deadCodes n p₀ q₁ q₂ s w Q k).2 =
        Program.map (words n p₀ q₁ q₂ s w Q k).2 (V39RecursiveGenerator.programs n p₀ q₁ q₂ s w Q k).2 := by
  induction k with
  | zero =>
    exact ⟨copies_word_exact _ _ .bit rfl p₀, meaning_ticket p₀ (Nat.pos_of_ne_zero (NeZero.ne p₀))⟩
  | succ k ih =>
    have htag := deadTagged_exact (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ ih.2
    have hrowUnit := pairCode_exact (finCodec w).encode _
      (Paper2.RecursiveSampling.uniform w) _ (.ticket w) _
      (meaning_ticket w (Nat.pos_of_ne_zero (NeZero.ne w))) htag
    have hrow := copies_word_exact _ _ _ hrowUnit Q
    have hraw := currentRows_exact (n := n) (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ ih.1
    have hcolUnit := copies_word_exact _ _ _ hraw w
    have hcol := pairCode_exact (finCodec Q).encode _
      (Paper2.RecursiveSampling.uniform Q) _ (.ticket Q) _
      (meaning_ticket Q (Nat.pos_of_ne_zero (NeZero.ne Q))) hcolUnit
    exact ⟨hrow, hcol⟩

theorem deadCodes_same_meaning (k : ℕ) :
    meaning (deadCodes n p₀ q₁ q₂ s w Q k).1 = meaning (currentCodes n p₀ q₁ q₂ s w Q k).1 ∧
    meaning (deadCodes n p₀ q₁ q₂ s w Q k).2 = meaning (currentCodes n p₀ q₁ q₂ s w Q k).2 := by
  have hd := deadCodes_exact n p₀ q₁ q₂ s w Q k
  have hc := currentCodes_exact n p₀ q₁ q₂ s w Q k
  exact ⟨hd.1.trans hc.1.symm, hd.2.trans hc.2.symm⟩

def deadSampleCode (k m : ℕ) : Code :=
  .append (copies m (deadCodes n p₀ q₁ q₂ s w Q k).1)
    (copies m (deadCodes n p₀ q₁ q₂ s w Q k).2)

theorem deadSampleCode_exact (k m : ℕ) :
    meaning (deadSampleCode n p₀ q₁ q₂ s w Q k m) =
      Program.map (sampleWord n p₀ q₁ q₂ s w Q k m)
        (sampleProgram n p₀ q₁ q₂ s w Q k m) := by
  have h := deadCodes_exact n p₀ q₁ q₂ s w Q k
  exact pairCode_exact _ _ _ _ _ _
    (copies_word_exact _ _ _ h.1 m) (copies_word_exact _ _ _ h.2 m)

theorem deadSampleCode_same_meaning (k m : ℕ) :
    meaning (deadSampleCode n p₀ q₁ q₂ s w Q k m) =
      meaning (sampleCode n p₀ q₁ q₂ s w Q k m) :=
  (deadSampleCode_exact n p₀ q₁ q₂ s w Q k m).trans
    (sampleCode_exact n p₀ q₁ q₂ s w Q k m).symm

theorem deadSampleCode_draws_le (k m : ℕ) :
    (meaning (deadSampleCode n p₀ q₁ q₂ s w Q k m)).maxDraws ≤
      sampleDrawBudget p₀ q₁ q₂ s w Q k m := by
  rw [deadSampleCode_same_meaning]
  exact sampleCode_draws_le n p₀ q₁ q₂ s w Q k m

theorem deadSampleCode_alphabet_le (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ) :
    (meaning (deadSampleCode n p₀ q₁ q₂ s w Q k m)).maxAlphabet ≤
      V38OneStep.publicA n s q₂ w Q p₀ := by
  rw [deadSampleCode_same_meaning]
  exact sampleCode_alphabet_le n p₀ q₁ q₂ s w Q hs hq₁ k m

#print axioms deadCodes_exact
#print axioms deadCodes_same_meaning
#print axioms deadSampleCode_draws_le
#print axioms deadSampleCode_alphabet_le

end Exact
end CurrentAdditive.V39DeadTaggedCompiler
