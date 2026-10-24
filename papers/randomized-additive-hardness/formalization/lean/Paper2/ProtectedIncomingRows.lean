import Paper2.SourcePopulation
import Paper2.SourceProjection
import Paper2.ProtectedDensityGroups

/-!
# Original protected rows at an incoming restoration node

Frozen v12 `res:incoming`, lines 351--379. This module starts after the
density group and selected original template bins have been found. It
tracks the two protected tags separately, using their exact original
conditional laws, and never conditions a law on the retained row event.
-/

namespace Paper2.ProtectedIncomingRows

open SourceMatrix SourceLaws SourceProjection

variable {Y : Type*} {q₁ q₂ s w : ℕ}

/-- Original fixed-tail rows of copy `i` reaching the actual node. -/
def fixedEvent (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) : Set (Fin s → OuterColumn q₁ q₂ s Y) :=
  fun f => (i, .fixedTail f) ∈ R

/-- Original diagonal rows of copy `i` reaching the same node. -/
def diagonalEvent (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) : Set (OuterColumn q₁ q₂ s Y) :=
  fun j => (i, .diagonal j) ∈ R

/-- Actual image of the surviving fixed-tail labels at bin `p`. The
image may contain correlations imposed by the retained row event. -/
def fixedImage (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) : Set (OuterColumn q₁ q₂ s Y) :=
  (fun f => f p) '' fixedEvent R i

section Mass

variable [Fintype Y] [NeZero q₂]

theorem fixed_pushes (ν : PositiveRationalLaw Y) (p : Fin s) :
    (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.PushesTo
      (outerLaw ν q₁ q₂ s).toFiniteLaw (fun f => f p) := by
  intro E
  exact fixedTail_bin_marginal ν q₁ q₂ s p E

theorem fixed_image_mass (ν : PositiveRationalLaw Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) :
    (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ fixedEvent R i) ≤
      (outerLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ fixedImage R i p) :=
  FiniteLaw.prob_le_image _ _ _ (fixed_pushes ν p) (fixedEvent R i)

/-- Original inner-coordinate fibres with at least the specified
conditional `G₁` word mass. -/
noncomputable def highFibres (ν : PositiveRationalLaw Y)
    (U : Set (OuterColumn q₁ q₂ s Y)) (δ : ℝ) : Finset (Fin q₂) :=
  SourcePopulation.qualifying
    (fun α => (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
      (fun γ => (α, γ) ∈ U)) (δ / 4)

omit [NeZero q₂] in
@[simp] theorem mem_highFibres (ν : PositiveRationalLaw Y)
    (U : Set (OuterColumn q₁ q₂ s Y)) (δ : ℝ) (α : Fin q₂) :
    α ∈ highFibres ν U δ ↔ δ / 4 ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
        (fun γ => (α,γ) ∈ U) :=
  SourcePopulation.mem_qualifying _ _ _

/-- Image mass above `δ/2` forces strictly more than `δq₂/4`
distinct original inner-coordinate fibres. -/
theorem high_fibres_of_image_mass (ν : PositiveRationalLaw Y)
    (U : Set (OuterColumn q₁ q₂ s Y)) (δ : ℝ) (hδ : 0 < δ)
    (hmass : δ / 2 < (outerLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    δ * q₂ / 4 < (highFibres ν U δ).card := by
  let m : Fin q₂ → ℝ := fun α =>
    (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (α,γ) ∈ U)
  have hu (α : Fin q₂) : m α ≤ 1 :=
    (ν.iid (q₁ + s + 1)).toFiniteLaw.prob_le_one _
  have hq : (0 : ℝ) < q₂ := by exact_mod_cast (NeZero.pos q₂)
  have havg := outer_word_average (q₁ := q₁) (s := s) ν U
  have hsum : (q₂ : ℝ) * δ / 2 < ∑ α : Fin q₂, m α := by
    dsimp [m]
    have hm := mul_lt_mul_of_pos_left hmass hq
    rw [havg] at hm
    have hne : (q₂ : ℝ) ≠ 0 := ne_of_gt hq
    field_simp at hm
    nlinarith
  have hbound : (∑ α : Fin q₂, m α) ≤ (q₂ : ℝ) * (δ / 4) +
      ((highFibres ν U δ).card : ℝ) * (1 - δ / 4) := by
    simpa [highFibres, m] using
      SourcePopulation.sum_le_population m (δ / 4) hu
  have hc : (0 : ℝ) ≤ (highFibres ν U δ).card := by positivity
  nlinarith [mul_nonneg hc hδ.le]

theorem fixed_high_fibres (ν : PositiveRationalLaw Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) (δ : ℝ) (hδ : 0 < δ)
    (hmass : δ / 2 <
      (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ fixedEvent R i)) :
    δ * q₂ / 4 < (highFibres ν (fixedImage R i p) δ).card :=
  high_fibres_of_image_mass ν _ δ hδ (hmass.trans_le (fixed_image_mass ν R i p))

theorem diagonal_high_fibres (ν : PositiveRationalLaw Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (δ : ℝ) (hδ : 0 < δ)
    (hmass : δ / 2 <
      (outerLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ diagonalEvent R i)) :
    δ * q₂ / 4 < (highFibres ν (diagonalEvent R i) δ).card :=
  high_fibres_of_image_mass ν _ δ hδ hmass

end Mass

/-- One actual original fixed-tail row for each retained outer label. -/
noncomputable def fixedRepresentative
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) (j : fixedImage R i p) :
    Fin w × TaggedColumn q₁ q₂ s Y :=
  (i, .fixedTail (SourceProjection.representative (fun f => f p)
    (fixedEvent R i) j).val)

theorem fixedRepresentative_survives
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) (j : fixedImage R i p) :
    fixedRepresentative R i p j ∈ R := by
  change (SourceProjection.representative (fun f => f p)
    (fixedEvent R i) j).val ∈ fixedEvent R i
  exact SourceProjection.representative_survives (fun f => f p)
    (fixedEvent R i) j

theorem fixedRepresentative_projects
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) (j : fixedImage R i p) :
    (SourceProjection.representative (fun f => f p)
      (fixedEvent R i) j).val p = j.val :=
  SourceProjection.representative_maps (fun f => f p) (fixedEvent R i) j

theorem fixedRepresentative_injective
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) :
    Function.Injective (fixedRepresentative R i p) := by
  intro j j' h
  apply Subtype.ext
  have hf : (SourceProjection.representative (fun f => f p)
      (fixedEvent R i) j).val =
      (SourceProjection.representative (fun f => f p)
        (fixedEvent R i) j').val :=
    TaggedColumn.fixedTail.inj (Prod.mk.inj h).2
  have hj := fixedRepresentative_projects R i p j
  have hj' := fixedRepresentative_projects R i p j'
  rw [hf] at hj
  exact hj.symm.trans hj'

theorem fixedRepresentative_distinct_coordinates
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i i' : Fin w) (p p' : Fin s)
    (j : fixedImage R i p) (j' : fixedImage R i' p')
    (hii' : i ≠ i') :
    fixedRepresentative R i p j ≠ fixedRepresentative R i' p' j' := by
  intro h
  exact hii' (Prod.mk.inj h).1

/-- A diagonal outer label is already its own original surviving row;
there is no completion or conditioned law. -/
def diagonalRepresentative
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (j : diagonalEvent R i) :
    Fin w × TaggedColumn q₁ q₂ s Y := (i, .diagonal j.val)

theorem diagonalRepresentative_survives
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (j : diagonalEvent R i) :
    diagonalRepresentative R i j ∈ R := j.property

theorem diagonalRepresentative_injective
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) : Function.Injective (diagonalRepresentative R i) := by
  intro j j' h
  apply Subtype.ext
  exact TaggedColumn.diagonal.inj (Prod.mk.inj h).2

theorem diagonalRepresentative_distinct_coordinates
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i i' : Fin w) (j : diagonalEvent R i) (j' : diagonalEvent R i')
    (hii' : i ≠ i') :
    diagonalRepresentative R i j ≠ diagonalRepresentative R i' j' := by
  intro h
  exact hii' (Prod.mk.inj h).1

/-- The two protected tags remain distinct original rows, even if their
outer `J₂` labels happen to coincide. -/
theorem representatives_distinct_tags
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s)
    (f : fixedImage R i p) (d : diagonalEvent R i) :
    fixedRepresentative R i p f ≠ diagonalRepresentative R i d := by
  intro h
  cases (Prod.mk.inj h).2

/-- Each chosen fixed-tail representative reads exactly its original
outer label in the source matrix's template bin. -/
theorem fixedRepresentative_entry
    {X V : Type*} [NeZero s]
    (base : X → Y → Bool)
    (activity : V → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) (j : fixedImage R i p)
    (z : Template q₁ q₂ X) :
    N base activity ξ₀ (fixedRepresentative R i p j).2 (.inl (p,z)) =
      T base z j.val := by
  change T base z ((SourceProjection.representative (fun f => f p)
    (fixedEvent R i) j).val p) = T base z j.val
  rw [fixedRepresentative_projects]

theorem diagonalRepresentative_entry
    {X V : Type*} [NeZero s]
    (base : X → Y → Bool)
    (activity : V → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (i : Fin w) (p : Fin s) (j : diagonalEvent R i)
    (z : Template q₁ q₂ X) :
    N base activity ξ₀ (diagonalRepresentative R i j).2 (.inl (p,z)) =
      T base z j.val := rfl

end Paper2.ProtectedIncomingRows

#print axioms Paper2.ProtectedIncomingRows.fixed_pushes
#print axioms Paper2.ProtectedIncomingRows.fixed_image_mass
#print axioms Paper2.ProtectedIncomingRows.high_fibres_of_image_mass
#print axioms Paper2.ProtectedIncomingRows.fixed_high_fibres
#print axioms Paper2.ProtectedIncomingRows.diagonal_high_fibres
#print axioms Paper2.ProtectedIncomingRows.fixedRepresentative_survives
#print axioms Paper2.ProtectedIncomingRows.fixedRepresentative_injective
#print axioms Paper2.ProtectedIncomingRows.fixedRepresentative_distinct_coordinates
#print axioms Paper2.ProtectedIncomingRows.diagonalRepresentative_survives
#print axioms Paper2.ProtectedIncomingRows.diagonalRepresentative_injective
#print axioms Paper2.ProtectedIncomingRows.diagonalRepresentative_distinct_coordinates
#print axioms Paper2.ProtectedIncomingRows.representatives_distinct_tags
#print axioms Paper2.ProtectedIncomingRows.fixedRepresentative_entry
#print axioms Paper2.ProtectedIncomingRows.diagonalRepresentative_entry
