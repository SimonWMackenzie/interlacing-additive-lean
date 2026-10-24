import CurrentAdditive.AdaptiveFallback
import CurrentAdditive.GenericSamplerRunSplit

/-! Manuscript-faithful total table sampling on the old public fair-bit tape.
Every exhausted draw uses the first member of its current alphabet and the
program continues; no whole-table abort or zero-table substitution occurs. -/

namespace Paper2.GenericSamplerFallbackTable

open Paper2.RecursiveSamplingProgram
open Paper2.RecursiveSamplingCapped
open Paper2.RecursiveSamplingExecution
open Paper2.RecursiveSampling
open Paper2.RecursiveEntries
open Paper2.RecursiveSamplingSeed
open Paper2.GenericSamplerRunSplit

theorem runStateFallback_allLeaves {A : Type*} {M : ℕ}
    (P : A → Prop) (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (t : CappedSampler.Adaptive.Tape B R N)
    (hs : AllLeaves P s.val) :
    AllLeaves P (runStateFallback B R hMB N s t).val := by
  induction N generalizing s with
  | zero => simpa [runStateFallback, CappedSampler.Adaptive.runFallback] using hs
  | succ N ih =>
      let i : Fin (stateDenominator s) :=
        (CappedSampler.runWideBits (stateDenominator s) B R
          (state_width hMB s) t.1).getD ⟨0, stateDenominator_pos s⟩
      change AllLeaves P (runStateFallback B R hMB N (stateStep s i) t.2).val
      exact ih (stateStep s i) t.2 (allLeaves_step P s.val i hs)

theorem runProgramFallback_allLeaves {A : Type*} {M : ℕ}
    (P : A → Prop) (B R : ℕ) (hMB : Nat.clog 2 M ≤ B)
    (N : ℕ) (s : State A M) (hN : s.val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N)
    (hs : AllLeaves P s.val) :
    P (runProgramFallback B R hMB N s hN t) := by
  obtain ⟨a, ha⟩ := runStateFallback_pure B R hMB N s hN t
  have hall := runStateFallback_allLeaves P B R hMB N s t hs
  have hPa : P a := by simpa only [ha, AllLeaves] using hall
  simpa only [runProgramFallback_eq_leaf B R hMB N s hN t a ha] using hPa

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- The same public tape budget as `RecursiveSamplingExecution.run`, with
first-symbol fallback at each failed bounded draw. -/
def run (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) : Fin mX → Fin mY → Bool :=
  runProgramFallback _ _ le_rfl _
    (state order hs p hp activity ξ k mX mY)
    (program_drawBound order hs p hp activity ξ k mX mY) t

/-- Each fixed fair-bit tape yields an actual recursive matrix on one pair
of sampled indexed row and column arrays, including exhausted draws. -/
theorem run_is_sampled_table
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) :
    ∃ rows : Fin mX → Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k,
      ∃ cols : Fin mY → Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k,
        run order hs p hp activity ξ k mX mY t =
          RecursiveEntries.table (LookupSeed.matrix p) activity ξ k rows cols := by
  let F : (Fin mY → Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k) ×
      (Fin mX → Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k) →
      Fin mX → Fin mY → Bool :=
    fun pair => RecursiveEntries.table (LookupSeed.matrix p) activity ξ k pair.2 pair.1
  have hall : AllLeaves (fun T => ∃ pair, T = F pair)
      (state order hs p hp activity ξ k mX mY).val := by
    change AllLeaves (fun T => ∃ pair, T = F pair)
      (RecursiveSampling.tableProgram order hs (seedRow p) (seedColumn p hp)
        (LookupSeed.matrix p) activity ξ k mX mY)
    exact allLeaves_map _ F _ (fun pair => ⟨pair, rfl⟩)
  obtain ⟨pair, hpair⟩ := runProgramFallback_allLeaves
    (fun T => ∃ pair, T = F pair) _ _ le_rfl _
    (state order hs p hp activity ξ k mX mY)
    (program_drawBound order hs p hp activity ξ k mX mY) t hall
  exact ⟨pair.2, pair.1, hpair⟩

#print axioms run_is_sampled_table

end Paper2.GenericSamplerFallbackTable
