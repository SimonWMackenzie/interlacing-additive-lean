import CurrentAdditive.GeneratedCollisionEndpointExact
import Paper2.SourceSurvivingCollisionsBranches

/-!
The graph item rows of the indexed generated matrix have exactly the old
source item carrier and base-row law. A raw shadow retains every template
row but exactly the indexed retained item rows. It is used only for the old
graph collision combinatorics, not for the indexed matrix's template law.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceDeficiency
open Paper2.SourceSurvivingCollisions

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def rawItemShadow
    (V : Set (Row (I := SourceConstruction.Items s G) src)) :
    Set (RawRow q₁ q₂ s X (SourceConstruction.Items s G))
  | .inl _ => True
  | .inr iu => Sum.inr iu ∈ V

def rawItemCode
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s) :
    RawRow q₁ q₂ s X (SourceConstruction.Items s G) → Fin s
  | .inl _ => ⟨0, NeZero.pos s⟩
  | .inr iu => rowCode (.inr iu)

@[simp] theorem rawItemShadow_source
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (i : SourceConstruction.Items s G) (u : X) :
    Sum.inr (i,u) ∈ rawItemShadow src V ↔ Sum.inr (i,u) ∈ V := Iff.rfl

@[simp] theorem rawItemCode_source
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s)
    (i : SourceConstruction.Items s G) (u : X) :
    rawItemCode src rowCode (.inr (i,u)) = rowCode (.inr (i,u)) := rfl

theorem raw_shadow_item_kept
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (i : SourceConstruction.Items s G) :
    itemKept μX (rawItemShadow src V) i ↔
      1/2 ≤ μX.toFiniteLaw.prob (fun u => Sum.inr (i,u) ∈ V) := Iff.rfl

theorem raw_shadow_item_branch_mass
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s)
    (i : SourceConstruction.Items s G) (b : Fin s) :
    itemBranchMass μX (rawItemShadow src V) (rawItemCode src rowCode) i b =
      μX.toFiniteLaw.prob (fun u => Sum.inr (i,u) ∈ V ∧
        rowCode (.inr (i,u)) = b) := rfl

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.raw_shadow_item_branch_mass
