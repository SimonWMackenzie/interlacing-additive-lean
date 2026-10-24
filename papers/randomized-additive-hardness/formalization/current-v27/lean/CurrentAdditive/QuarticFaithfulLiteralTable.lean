import CurrentAdditive.QuarticFaithfulSelectedGraphMachine

/-! Exact row-major table object for one total v27 good-branch tape. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace Paper2.GenericQuarticFaithful

open Paper2.SourceProfileParameters
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

local instance (L : ℕ) : NeZero (width L) :=
  ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) :=
  ⟨by have := width_admissible L; omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩

theorem table27Faithful_eq_tabulate {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ)
    (bits : RecursiveSamplingMaterialization.TapeList (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k)) :
    let activity := SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1)
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      hn (by unfold width27; positivity)
      (by exact RestorationPublicQScratch.publicQ_pos _ _)
    ∃ rows cols,
      table27Faithful hn edge L Δ γ k hc bits =
        YaoMaterialization.tabulate
          (RecursiveEntries.table (LookupSeed.matrix (LookupSeed.width L))
            activity ξ k rows cols) := by
  intro activity ξ
  obtain ⟨rows, cols, hmatrix⟩ :=
    table27Faithful_sampled hn edge L Δ γ k hc bits
  refine ⟨rows, cols, ?_⟩
  apply congrArg YaoMaterialization.tabulate
  funext i j
  exact (table27Faithful_entry hn edge L Δ γ k hc bits i j).symm.trans
    (congrFun (congrFun hmatrix i) j)

#print axioms table27Faithful_eq_tabulate

end Paper2.GenericQuarticFaithful
