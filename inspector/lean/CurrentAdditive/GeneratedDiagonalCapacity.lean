import CurrentAdditive.GeneratedBranchBudget
import CurrentAdditive.DeterministicIndexedTemplates
import Paper2.SourceProjection

/-!
The literal indexed diagonal of the generated matrix realizes the interlace
of the generated transposed base matrix. This is the source-specific cost
transfer needed at an Alice node of `det:near-full`.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def selectedInner (e : Fin k → Fin q₂) (z : src.inner.Label) :
    Fin k → InnerRow q₁ X := fun i => src.inner.decode z (e i)

/-- A whole retained indexed selector is projected once and is shared by
every selected diagonal row. The selected diagonal inputs and selector rows
must themselves belong to the actual retained matrix. -/
theorem selected_indexed_diagonal_cost_le (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (e : Fin k → Fin q₂)
    (K : Set src.inner.Label) (S : Set (Fin k × src.gamma.Label))
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, Column.diagonal (e a.1, a.2) ∈ U) :
    Paper2.Compression.restrictionD (Paper2.fullInterlace (A src R) k)
      S (selectedInner src e '' K) ≤
    Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  classical
  let F : (Fin k × src.gamma.Label) → src.inner.Label → Bool :=
    fun a z => N src R activity ξ₀ (.diagonal (e a.1, a.2)) (.inl (p, z))
  have hentry : ∀ a ∈ S, ∀ z ∈ K,
      F a z = Paper2.fullInterlace (A src R) k a (selectedInner src e z) := by
    intro a ha z hz
    rfl
  have hproj := restrictionD_projected_le F
    (Paper2.fullInterlace (A src R) k) id (selectedInner src e)
    S K S (fun _ h => h) hentry
  have hmap := restrictionD_map_le (N src R activity ξ₀)
    (fun a : Fin k × src.gamma.Label => Column.diagonal (e a.1, a.2))
    (fun z : src.inner.Label => Sum.inl (p, z))
    U V S K hS hK
  exact hproj.trans hmap

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.selected_indexed_diagonal_cost_le
