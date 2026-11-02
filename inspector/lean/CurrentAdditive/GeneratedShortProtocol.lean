import CurrentAdditive.GeneratedNearFullSubtypeBridge

/-!
The hypothesis that the actual retained indexed N has a short protocol is
realized by a genuine minimizing protocol on the retained subtype inputs.
Transpose changes only which party is written first; the raw matrix entry
and protocol cost are preserved.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix
open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem short_protocol_from_restriction
    (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (H : ℕ)
    (hshort : Paper2.Compression.restrictionD
      (N src R activity ξ₀) U V ≤ H) :
    ∃ P : Protocol V U Bool,
      P.cost ≤ H ∧
      ∀ (v : V) (z : U),
        P.eval v z = N src R activity ξ₀ z.val v.val := by
  classical
  let f : U → V → Bool := fun z v => N src R activity ξ₀ z.val v.val
  have hne : (AchievableCosts f).Nonempty :=
    Workspace.UpperBound.AchievableCosts_nonempty f
  have hmem : Workspace.Types.CommComplexity.D f ∈ AchievableCosts f := by
    simpa [Workspace.Types.CommComplexity.D] using (Nat.sInf_mem hne)
  obtain ⟨Q, hQc, hQcomp⟩ := hmem
  let P := Workspace.UpperBound.Protocol.transpose Q
  refine ⟨P, ?_, ?_⟩
  · change (Workspace.UpperBound.Protocol.transpose Q).cost ≤ H
    rw [Workspace.UpperBound.Protocol.transpose_cost]
    have hD : Workspace.Types.CommComplexity.D f ≤ H := by
      simpa only [f, Paper2.Compression.restrictionD] using hshort
    omega
  · intro v z
    change (Workspace.UpperBound.Protocol.transpose Q).eval v z = _
    rw [Workspace.UpperBound.Protocol.transpose_eval]
    exact hQcomp z v

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.short_protocol_from_restriction
