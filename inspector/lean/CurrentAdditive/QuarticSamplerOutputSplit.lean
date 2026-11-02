import CurrentAdditive.GenericSamplerRunSplit
import CurrentAdditive.QuarticConstructor

/-! The actual v27 good-branch table has two literal outcomes on every
correctly sized fair-bit tape: a recursive table on one indexed sampled
row/column pair, or the all-zero abort table. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace Paper2.GenericQuarticOutput

open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩

theorem scheduled27_table_split {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (CurrentAdditive.RandomizedSchedule.width27 L)
      (CurrentAdditive.RandomizedSchedule.Q27
        (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    let activity := SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin m) hc.1)
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n
      (CurrentAdditive.RandomizedSchedule.width27 L)
      (CurrentAdditive.RandomizedSchedule.Q27
        (V := Fin n) (E := Fin m) L γ Δ)
      hn (by unfold CurrentAdditive.RandomizedSchedule.width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
    (∃ rows cols,
      (scheduledTable27 hn edge L Δ γ k hc bits).matrix =
        RecursiveEntries.table (LookupSeed.matrix (LookupSeed.width L))
          activity ξ k rows cols) ∨
      (scheduledTable27 hn edge L Δ γ k hc bits).matrix =
        (fun _ _ => false) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero (width L) := ⟨by unfold width; positivity⟩
  letI : NeZero (width L - 2) := ⟨by have := width_admissible L; omega⟩
  letI : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
  letI : NeZero (CurrentAdditive.RandomizedSchedule.width27 L) :=
    ⟨by unfold CurrentAdditive.RandomizedSchedule.width27; positivity⟩
  letI : NeZero (CurrentAdditive.RandomizedSchedule.Q27
      (V := Fin n) (E := Fin m) L γ Δ) :=
    ⟨Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩
  have h := GenericSamplerRunSplit.run_sampled_table_or_zero
    (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity)
    (SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep
        L (Fin m) hc.1))
    (CanonicalDefaultSource.canonicalDefaultTails L n
      (CurrentAdditive.RandomizedSchedule.width27 L)
      (CurrentAdditive.RandomizedSchedule.Q27
        (V := Fin n) (E := Fin m) L γ Δ)
      hn (by unfold CurrentAdditive.RandomizedSchedule.width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _))
    k (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)
    (RecursiveSamplingTape.readTape _ _ _ bits)
  rw [scheduled27_eq_tabulate]
  rcases h with ⟨rows, cols, hr⟩ | hr
  · left
    refine ⟨rows, cols, ?_⟩
    funext i j
    rw [YaoMaterialization.tabulate_matrix]
    exact congrFun (congrFun hr i) j
  · right
    funext i j
    rw [YaoMaterialization.tabulate_matrix]
    exact congrFun (congrFun hr i) j

#print axioms scheduled27_table_split

end Paper2.GenericQuarticOutput
