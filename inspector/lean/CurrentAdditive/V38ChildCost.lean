import CurrentAdditive.V38MassSplit

/-!
The actual first-message subtrees compute the corresponding ambient
restricted rectangles. This keeps protocol cost tied to the same original
matrix and input labels.
-/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {A B : Type*} [Fintype A] [Fintype B]

theorem row_child_cost_eq (F : A → B → Bool) (U : Set A) (V : Set B)
    [Fintype U] [Fintype V]
    (a : U → Bool) (t : Bool) :
    D (fun (x : {x : U // a x = t}) (y : V) => F x.1.1 y.1) =
      Compression.restrictionD F (childSet U a t) V := by
  classical
  let ρ : {x : U // a x = t} → childSet U a t :=
    fun x => ⟨x.1.1, x.1.2, x.2⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨hU, ha⟩
    exact ⟨⟨⟨x, hU⟩, ha⟩, rfl⟩
  have h := pullback_D_eq_of_surjective
    (fun (x : childSet U a t) (y : V) => F x.1 y.1)
    ρ id hρ Function.surjective_id
  exact h

theorem col_child_cost_eq (F : A → B → Bool) (U : Set A) (V : Set B)
    [Fintype U] [Fintype V]
    (b : V → Bool) (t : Bool) :
    D (fun (x : U) (y : {y : V // b y = t}) => F x.1 y.1.1) =
      Compression.restrictionD F U (childSet V b t) := by
  classical
  let σ : {y : V // b y = t} → childSet V b t :=
    fun y => ⟨y.1.1, y.1.2, y.2⟩
  have hσ : Function.Surjective σ := by
    rintro ⟨y, hy⟩
    rcases hy with ⟨hV, hb⟩
    exact ⟨⟨⟨y, hV⟩, hb⟩, rfl⟩
  have h := pullback_D_eq_of_surjective
    (fun (x : U) (y : childSet V b t) => F x.1 y.1)
    id σ Function.surjective_id hσ
  exact h

/-- First message of an optimal protocol for the actual rectangle. Both
children refer to subsets of the original ambient input labels. -/
theorem firstMessage_rectangle (F : A → B → Bool) (U : Set A) (V : Set B)
    (hpos : 1 ≤ Compression.restrictionD F U V) :
    (∃ a : U → Bool, ∀ t : Bool,
      Compression.restrictionD F (childSet U a t) V ≤
        Compression.restrictionD F U V - 1) ∨
    (∃ b : V → Bool, ∀ t : Bool,
      Compression.restrictionD F U (childSet V b t) ≤
        Compression.restrictionD F U V - 1) := by
  classical
  have h := firstMessage_split (fun (x : U) (y : V) => F x.1 y.1) hpos
  rcases h with ⟨a, ha⟩ | ⟨b, hb⟩
  · left
    refine ⟨a, ?_⟩
    intro t
    simpa only [row_child_cost_eq] using ha t
  · right
    refine ⟨b, ?_⟩
    intro t
    simpa only [col_child_cost_eq] using hb t

#print axioms row_child_cost_eq
#print axioms col_child_cost_eq
#print axioms firstMessage_rectangle

end Paper2.V38SmallBlocks
