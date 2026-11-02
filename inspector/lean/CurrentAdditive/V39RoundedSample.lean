import CurrentAdditive.V39RecursiveGenerator

set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace CurrentAdditive.V39RecursiveGenerator

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open CurrentAdditive.V38OneStep CurrentAdditive.V38Resource

section Alphabet
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

omit [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂] [NeZero s]
  [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q] in
theorem publicA_covers (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) :
    let A := publicA n s q₂ w Q p₀
    512 ≤ A ∧ n ≤ A ∧ s ≤ A ∧ q₁ ≤ A ∧ q₂ ≤ A ∧
      4 * s ≤ A ∧ s - 3 ≤ A ∧ w ≤ A ∧ Q ≤ A ∧ p₀ ≤ A := by
  dsimp only
  have h512 : 512 ≤ publicA n s q₂ w Q p₀ := Nat.le_max_left _ _
  have hlarge : 4 * s * (n + s) ≤ publicA n s q₂ w Q p₀ :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hq₂ : q₂ ≤ publicA n s q₂ w Q p₀ :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hw : w ≤ publicA n s q₂ w Q p₀ :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hQ : Q ≤ publicA n s q₂ w Q p₀ :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  have hp₀ : p₀ ≤ publicA n s q₂ w Q p₀ :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  have hn : n ≤ publicA n s q₂ w Q p₀ := by nlinarith
  have h4s : 4 * s ≤ publicA n s q₂ w Q p₀ := by nlinarith
  have hsA : s ≤ publicA n s q₂ w Q p₀ := by omega
  exact ⟨h512, hn, hsA, by omega, hq₂, h4s, by omega, hw, hQ, hp₀⟩

/-- The manuscript's A covers every elementary request in the actual
recursive generators. In particular the seed and both item families are
discharged here, rather than left as a caller-supplied alphabet premise. -/
theorem alphabet_programs_le (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k : ℕ) :
    (programs n p₀ q₁ q₂ s w Q k).1.maxAlphabet ≤ publicA n s q₂ w Q p₀ ∧
    (programs n p₀ q₁ q₂ s w Q k).2.maxAlphabet ≤ publicA n s q₂ w Q p₀ := by
  rcases publicA_covers n p₀ q₁ q₂ s w Q hs hq₁ with
    ⟨h512, hn, hsA, hq₁A, hq₂A, h4s, hs3, hw, hQ, hp₀⟩
  induction k with
  | zero =>
    constructor
    · apply (alphabet_iid_le _ _).trans
      simp only [Program.maxAlphabet_map, Paper2.RecursiveSampling.uniform,
        Program.maxAlphabet_uniform]
      omega
    · change (Paper2.RecursiveSampling.uniform p₀).maxAlphabet ≤ _
      simpa only [Paper2.RecursiveSampling.uniform,
        Program.maxAlphabet_uniform] using hp₀
  | succ k ih =>
    exact ⟨alphabet_successorRow_le _ _ (by omega) hq₂A hw ih.2,
      alphabet_successorColumn_le _ _ _ h512 hsA hq₁A h4s hs3 hQ
        (by simpa only [Paper2.RecursiveSampling.uniform, Program.maxAlphabet_uniform] using hn) ih.1⟩

theorem alphabet_sampleProgram_le (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ) :
    (sampleProgram n p₀ q₁ q₂ s w Q k m).maxAlphabet ≤ publicA n s q₂ w Q p₀ := by
  exact (alphabet_prod_le _ _).trans (max_le
    ((alphabet_iid_le _ _).trans (alphabet_programs_le n p₀ q₁ q₂ s w Q hs hq₁ k).1)
    ((alphabet_iid_le _ _).trans (alphabet_programs_le n p₀ q₁ q₂ s w Q hs hq₁ k).2))

end Alphabet

section Sample
variable (n p₀ q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q]

def roundedLabels (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ)
    (bits : CurrentAdditive.RoundedDraw.BitBlocks
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)) :
    (Fin m → Row n p₀ q₁ q₂ s w Q k) × (Fin m → Column n p₀ q₁ q₂ s w Q k) :=
  CurrentAdditive.RoundedProgram.runProgram _ _
    ⟨sampleProgram n p₀ q₁ q₂ s w Q k m,
      alphabet_sampleProgram_le n p₀ q₁ q₂ s w Q hs hq₁ k m⟩
    (draws_sampleProgram_le n p₀ q₁ q₂ s w Q k m) bits

/-- Every joint event on all 2m complete level-k labels has the stated
1/200 error under the fixed reserved fair-bit tape, with no resource
premises for the recursively generated labels. -/
theorem roundedLabels_event_error_200 (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ)
    (P : ((Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)).prob
        (fun bits => P (roundedLabels n p₀ q₁ q₂ s w Q hs hq₁ k m bits)) -
      (sampleLaw n p₀ q₁ q₂ s w Q k m).toFiniteLaw.prob P| ≤ (1 : ℝ) / 200 := by
  have h := CurrentAdditive.RoundedProgram.runProgram_event_error_200
    (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
    (sampleDrawBudget p₀ q₁ q₂ s w Q k m)
    ⟨sampleProgram n p₀ q₁ q₂ s w Q k m,
      alphabet_sampleProgram_le n p₀ q₁ q₂ s w Q hs hq₁ k m⟩
    (draws_sampleProgram_le n p₀ q₁ q₂ s w Q k m)
    (publicBits_budget _ _) {z | P z}
  rw [generates_eventProb (generates_sampleProgram n p₀ q₁ q₂ s w Q k m) {z | P z}] at h
  exact h

/-- Any deterministic evaluation/serialization of those same labels inherits
the error bound. The evaluator is unrestricted, including all m² exact
entry lookups; this is not a claim about its physical machine clock. -/
theorem rounded_map_event_error_200 {β : Type*}
    (hs : 4 ≤ s) (hq₁ : q₁ = s - 2) (k m : ℕ)
    (eval : ((Fin m → Row n p₀ q₁ q₂ s w Q k) ×
      (Fin m → Column n p₀ q₁ q₂ s w Q k)) → β) (P : β → Prop) :
    |(CurrentAdditive.RoundedDraw.bitBlocksLaw
      (publicBits (publicA n s q₂ w Q p₀) (sampleDrawBudget p₀ q₁ q₂ s w Q k m))
      (sampleDrawBudget p₀ q₁ q₂ s w Q k m)).prob
        (fun bits => P (eval (roundedLabels n p₀ q₁ q₂ s w Q hs hq₁ k m bits))) -
      (sampleLaw n p₀ q₁ q₂ s w Q k m).toFiniteLaw.prob (fun z => P (eval z))| ≤ (1 : ℝ) / 200 :=
  roundedLabels_event_error_200 n p₀ q₁ q₂ s w Q hs hq₁ k m (fun z => P (eval z))

#print axioms alphabet_programs_le
#print axioms roundedLabels_event_error_200
#print axioms rounded_map_event_error_200

end Sample
end CurrentAdditive.V39RecursiveGenerator
