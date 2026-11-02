import CurrentAdditive.V38PairProjection

/-!
Actual mass conservation under a protocol's first query. Child masses refer
to the original finite law, not the law conditioned on the parent rectangle.
-/

namespace Paper2.V38SmallBlocks

variable {A : Type*} [Fintype A]

def childSet (U : Set A) (b : U → Bool) (t : Bool) : Set A :=
  {a | ∃ h : a ∈ U, b ⟨a, h⟩ = t}

theorem childSet_sub (U : Set A) (b : U → Bool) (t : Bool) :
    childSet U b t ⊆ U := by
  rintro a ⟨h, _⟩
  exact h

theorem prob_child_split (μ : FiniteLaw A) (U : Set A) (b : U → Bool) :
    μ.prob (· ∈ childSet U b false) +
      μ.prob (· ∈ childSet U b true) = μ.prob (· ∈ U) := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hU : a ∈ U
  · by_cases hb : b ⟨a, hU⟩ = true
    · have hfalse : a ∉ childSet U b false := by
        rintro ⟨ha, h⟩
        have : (⟨a, ha⟩ : U) = ⟨a, hU⟩ := Subtype.ext rfl
        rw [this, hb] at h
        cases h
      have htrue : a ∈ childSet U b true := ⟨hU, hb⟩
      simp [hU, hfalse, htrue]
    · have hb' : b ⟨a, hU⟩ = false := by
        cases hval : b ⟨a, hU⟩ <;> simp_all
      have htrue : a ∉ childSet U b true := by
        rintro ⟨ha, h⟩
        have : (⟨a, ha⟩ : U) = ⟨a, hU⟩ := Subtype.ext rfl
        rw [this, hb'] at h
        cases h
      have hfalse : a ∈ childSet U b false := ⟨hU, hb'⟩
      simp [hU, hfalse, htrue]
  · have hfalse : a ∉ childSet U b false := fun h => hU (childSet_sub U b false h)
    have htrue : a ∉ childSet U b true := fun h => hU (childSet_sub U b true h)
    simp [hU, hfalse, htrue]

theorem exists_heavy_child (μ : FiniteLaw A) (U : Set A) (b : U → Bool) :
    ∃ t : Bool, μ.prob (· ∈ U) / 2 ≤ μ.prob (· ∈ childSet U b t) := by
  have hsplit := prob_child_split μ U b
  by_cases h : μ.prob (· ∈ U) / 2 ≤ μ.prob (· ∈ childSet U b false)
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    push_neg at h
    linarith

#print axioms prob_child_split
#print axioms exists_heavy_child

end Paper2.V38SmallBlocks
