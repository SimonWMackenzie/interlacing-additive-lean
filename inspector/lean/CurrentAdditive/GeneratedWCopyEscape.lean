import CurrentAdditive.GeneratedWProtectedMassBalance
import CurrentAdditive.GeneratedNExactNearFull
import Paper2.SourceProjection

/-! A short physical W node induces a short restriction of its own literal N
copy, on actual surviving tuple projections and actual retained tagged labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := s) μX μY)

theorem indexed_copy_restriction_le_W
    (μI : PositiveRationalLaw I) (streams : InternalStreams src μI w)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (Vnode : Set (Fin w × Column src)) (i : Fin w) :
    Paper2.Compression.restrictionD (N src R activity ξ₀)
      {Z | (i,Z) ∈ Vnode}
      ((fun t => InternalStreams.decode src streams t i) '' Yevent) ≤
    Paper2.Compression.restrictionD (W src streams R activity ξ₀)
      Yevent Vnode := by
  classical
  have hmap := Paper2.SourceProjection.restrictionD_projected_le
    (fun row col => W src streams R activity ξ₀ col row)
    (N src R activity ξ₀)
    (fun Z : Column src => (i,Z))
    (fun t => InternalStreams.decode src streams t i)
    Vnode Yevent {Z | (i,Z) ∈ Vnode}
    (by intro Z hZ; exact hZ)
    (by intro Z hZ t ht; rfl)
  have ht := Paper2.SourceProjection.restrictionD_transpose
    (W src streams R activity ξ₀) Yevent Vnode
  simpa only [ht] using hmap

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_copy_restriction_le_W
