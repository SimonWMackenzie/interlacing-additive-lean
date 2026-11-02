import Paper2.TwoStreamColumnStep

/-!
# A column query after projecting the actual retained tuples

Frozen v12 Section 5, `res:destinations`, the first-Bob capacity argument.
The two child images may overlap: a projected word can have original
completions answering either bit. Subadditivity, not a disjointness or
independence claim, supplies a child with half the projected mass. The
communication bound charges that actual Bob bit on the original matrix.
-/

namespace Paper2.ReferenceColumnStep

open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {A B Z : Type*}

def columnChild (O : Set B) (query : B → Bool) (b : Bool) : Set B :=
  {y | y ∈ O ∧ query y = b}

theorem image_child_subset (f : B → Z) (O : Set B) (query : B → Bool) (b : Bool) :
    f '' columnChild O query b ⊆ f '' O := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, hy.1, rfl⟩

theorem image_mem_child (f : B → Z) (O : Set B) (query : B → Bool)
    (z : Z) (hz : z ∈ f '' O) :
    z ∈ f '' columnChild O query false ∨ z ∈ f '' columnChild O query true := by
  rcases hz with ⟨y, hy, rfl⟩
  cases hq : query y
  · exact Or.inl ⟨y, ⟨hy, hq⟩, rfl⟩
  · exact Or.inr ⟨y, ⟨hy, hq⟩, rfl⟩

/-- No measure is placed on selected completions. Both image masses use
the same ambient law on projected labels, and overlap is permitted. -/
theorem projected_mass_le_children [Fintype Z] (μ : FiniteLaw Z)
    (f : B → Z) (O : Set B) (query : B → Bool) :
    μ.prob (· ∈ f '' O) ≤
      μ.prob (· ∈ f '' columnChild O query false) +
      μ.prob (· ∈ f '' columnChild O query true) := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  have hw := μ.nonneg z
  by_cases hz : z ∈ f '' O
  · rcases image_mem_child f O query z hz with hf | ht
    · simp only [hz, hf, ite_true]
      split_ifs <;> linarith
    · simp only [hz, ht, ite_true]
      split_ifs <;> linarith
  · simp only [hz, ite_false]
    split_ifs <;> linarith

theorem exists_dense_projected_child [Fintype Z] (μ : FiniteLaw Z)
    (f : B → Z) (O : Set B) (query : B → Bool)
    (beta : ℝ) (hO : beta ≤ μ.prob (· ∈ f '' O)) :
    ∃ b, beta / 2 ≤ μ.prob (· ∈ f '' columnChild O query b) := by
  have hsum := projected_mass_le_children μ f O query
  by_cases hf : beta / 2 ≤ μ.prob (· ∈ f '' columnChild O query false)
  · exact ⟨false, hf⟩
  · exact ⟨true, by linarith⟩

/-- The chosen original child computes the entire retained rectangle,
and its parent query consumes one bit. -/
theorem restriction_add_one_le [Fintype A] [Fintype B]
    (M : A → B → Bool) (R : Set A) (O : Set B) (query : B → Bool)
    (left right : Protocol A B Bool)
    (hP : ∀ x ∈ R, ∀ y ∈ O,
      (Protocol.bNode query left right).eval x y = M x y)
    (b : Bool) :
    Compression.restrictionD M R (columnChild O query b) + 1 ≤
      (Protocol.bNode query left right).cost := by
  classical
  let child := if b then right else left
  let Q := Workspace.UpperBound.Protocol.comap
    (fun x : R => x.val) (fun y : columnChild O query b => y.val) child
  have hQ : Q.Computes (fun (x : R) (y : columnChild O query b) => M x.val y.val) := by
    intro x y
    rw [Workspace.UpperBound.Protocol.comap_eval]
    have he := hP x.val x.property y.val y.property.1
    have hb : query y.val = b := y.property.2
    cases b <;> simpa [Protocol.eval, hb, child] using he
  have hupper : Compression.restrictionD M R (columnChild O query b) ≤ child.cost := by
    have h : Compression.restrictionD M R (columnChild O query b) ≤ Q.cost :=
      Nat.sInf_le ⟨Q, rfl, hQ⟩
    simpa only [Q, Workspace.UpperBound.Protocol.comap_cost] using h
  have hchild : child.cost + 1 ≤ (Protocol.bNode query left right).cost := by
    dsimp only [child]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Protocol.cost]
    · simpa only [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_max_left left.cost right.cost) 1
    · simpa only [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_max_right left.cost right.cost) 1
  exact (Nat.add_le_add_right hupper 1).trans hchild

end Paper2.ReferenceColumnStep

#print axioms Paper2.ReferenceColumnStep.projected_mass_le_children
#print axioms Paper2.ReferenceColumnStep.exists_dense_projected_child
#print axioms Paper2.ReferenceColumnStep.restriction_add_one_le
