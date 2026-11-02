import Paper2.PairedSelectorMatrixCore

/-!
# Exact laws of paired selectors and their joint projections

Frozen v12 Section 5, `res:paired`, lines 62--131. The pair of original
selector laws is identified with its genuinely tagged product coordinates.
Every pushforward identity holds for arbitrary joint events. In particular,
the retained selector set below need not have any independence property.
-/

namespace Paper2.PairedSelectorMatrix

open scoped BigOperators

variable {J : Type*} {q n : ℕ}

/-- The two literal selector arrays are exactly one array on tagged blocks. -/
def coordinateEquiv : Selector q J ≃ (Block q → J) where
  toFun := coordinate
  invFun f := (fun i => f (false, i), fun i => f (true, i))
  left_inv z := by cases z; rfl
  right_inv f := by
    funext b
    rcases b with ⟨b, i⟩
    cases b <;> rfl

@[simp] theorem coordinateEquiv_apply (z : Selector q J) :
    coordinateEquiv z = coordinate z := rfl

section Laws

variable [Fintype J]

/-- Pointwise equality of the weights under the tagged coordinate bijection. -/
theorem selector_weight (ν : PositiveRationalLaw J) (z : Selector q J) :
    (selectorLaw ν q).toFiniteLaw.weight z =
      (FiniteLaw.pi (fun _ : Block q => ν.toFiniteLaw)).weight (coordinate z) := by
  rw [selectorLaw, PositiveRationalLaw.toFiniteLaw_prod,
    PositiveRationalLaw.toFiniteLaw_iid]
  simp [FiniteLaw.prod, FiniteLaw.iid, FiniteLaw.pi, Fintype.prod_prod_type,
    coordinate, mul_comm]

/-- Equality on every joint event, not just events depending on one block. -/
theorem selector_pushes (ν : PositiveRationalLaw J) :
    (selectorLaw ν q).toFiniteLaw.PushesTo
      (FiniteLaw.pi (fun _ : Block q => ν.toFiniteLaw)) coordinate := by
  classical
  intro E
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv coordinateEquiv
  intro z
  simp only [coordinateEquiv_apply]
  split_ifs
  · exact selector_weight ν z
  · rfl

/-- Injective selection of tagged blocks preserves the full iid law. -/
theorem projection_pushes (ν : PositiveRationalLaw J)
    (e : Fin n → Block q) (he : Function.Injective e) :
    (selectorLaw ν q).toFiniteLaw.PushesTo (ν.iid n).toFiniteLaw (projection e) := by
  intro E
  calc
    _ = (FiniteLaw.pi (fun _ : Block q => ν.toFiniteLaw)).prob
        (fun z => E (fun i => z (e i))) :=
      selector_pushes ν (fun z => E (fun i => z (e i)))
    _ = (FiniteLaw.pi (fun _ : Fin n => ν.toFiniteLaw)).prob E :=
      FiniteLaw.pi_prob_restrict (fun _ : Block q => ν.toFiniteLaw) e he E
    _ = _ := by rw [PositiveRationalLaw.toFiniteLaw_iid]; rfl

/-- The image of the same retained pair set has at least its original mass. -/
theorem projection_mass (ν : PositiveRationalLaw J)
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) :
    (selectorLaw ν q).toFiniteLaw.prob (· ∈ A) ≤
      (ν.iid n).toFiniteLaw.prob (· ∈ projection e '' A) :=
  FiniteLaw.prob_le_image _ _ _ (projection_pushes ν e he) A

/-- Each literal tagged coordinate has the original base law. -/
theorem coordinate_pushes (ν : PositiveRationalLaw J) (b : Block q) :
    (selectorLaw ν q).toFiniteLaw.PushesTo ν.toFiniteLaw (fun z => coordinate z b) := by
  intro E
  calc
    _ = (ν.iid 1).toFiniteLaw.prob (fun z => E (z 0)) :=
      projection_pushes ν (fun _ : Fin 1 => b)
        (fun _ _ _ => Subsingleton.elim _ _) (fun z => E (z 0))
    _ = _ := by
      rw [PositiveRationalLaw.toFiniteLaw_iid, FiniteLaw.iid_prob_coordinate]

/-- A scalar projected event also retains at least the original pair mass. -/
theorem coordinate_mass (ν : PositiveRationalLaw J) (b : Block q)
    (A : Set (Selector q J)) :
    (selectorLaw ν q).toFiniteLaw.prob (· ∈ A) ≤
      ν.toFiniteLaw.prob (· ∈ (fun z => coordinate z b) '' A) :=
  FiniteLaw.prob_le_image _ _ _ (coordinate_pushes ν b) A

end Laws

end Paper2.PairedSelectorMatrix

#print axioms Paper2.PairedSelectorMatrix.selector_pushes
#print axioms Paper2.PairedSelectorMatrix.projection_pushes
#print axioms Paper2.PairedSelectorMatrix.projection_mass
#print axioms Paper2.PairedSelectorMatrix.coordinate_pushes
#print axioms Paper2.PairedSelectorMatrix.coordinate_mass
