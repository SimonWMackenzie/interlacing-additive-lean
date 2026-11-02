import Paper2.RationalTupleTransport

/-!
# Product laws and projections onto disjoint coordinate sets

Frozen v12 source: Section 4, `eq:product-projection`, and Section 5,
the product-projection input to `res:projection-cover`. The ambient law is
an actual finite independent product law. Retained events are arbitrary:
they may correlate all coordinates.
-/

namespace Paper2

open scoped BigOperators

namespace FiniteLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {α : ι → Type*} [∀ i, Fintype (α i)]

/-- A finite independent product, allowing different coordinate laws. -/
noncomputable def pi (μ : ∀ i, FiniteLaw (α i)) : FiniteLaw (∀ i, α i) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (μ i).nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.total, Finset.prod_const_one]

theorem pi_prob_coordinatewise (μ : ∀ i, FiniteLaw (α i))
    (E : ∀ i, α i → Prop) :
    (pi μ).prob (fun x => ∀ i, E i (x i)) = ∏ i, (μ i).prob (E i) := by
  classical
  have hprod (x : ∀ i, α i) :
      (if ∀ i, E i (x i) then ∏ i, (μ i).weight (x i) else 0) =
        ∏ i, if E i (x i) then (μ i).weight (x i) else 0 := by
    by_cases hx : ∀ i, E i (x i)
    · simp [hx]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      simp only [hx, ↓reduceIte]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp only [prob, pi]
  simp_rw [hprod]
  exact (Fintype.prod_sum (fun i a => if E i a then (μ i).weight a else 0)).symm

variable {κ A : Type*} [Fintype κ] [DecidableEq κ] [Fintype A]

/-- Injective coordinate selection sends an independent product law to the
corresponding independent marginal, for every joint event. -/
theorem pi_prob_restrict (μ : ι → FiniteLaw A) (e : κ → ι)
    (he : Function.Injective e) (E : (κ → A) → Prop) :
    (pi μ).prob (fun x => E (fun j => x (e j))) =
      (pi (fun j => μ (e j))).prob E := by
  classical
  apply prob_preimage_eq_of_fibres (pi μ) (pi (fun j => μ (e j)))
    (fun x j => x (e j))
  intro y
  let Q : ι → A → Prop := fun i a => ∀ j, e j = i → a = y j
  have hQ (x : ι → A) : (fun j => x (e j)) = y ↔ ∀ i, Q i (x i) := by
    constructor
    · intro h i j hj
      subst i
      exact congrFun h j
    · intro h
      exact funext fun j => h (e j) j rfl
  calc
    _ = (pi μ).prob (fun x => ∀ i, Q i (x i)) := by
      unfold prob
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : (fun j => x (e j)) = y
      · simp [hx, (hQ x).mp hx]
      · have hn : ¬ ∀ i, Q i (x i) := fun h => hx ((hQ x).mpr h)
        simp [hx, hn]
    _ = ∏ i, (μ i).prob (Q i) := pi_prob_coordinatewise μ Q
    _ = ∏ j, (μ (e j)).weight (y j) := by
      symm
      apply Fintype.prod_of_injective e he
      · intro i hi
        have htrue : Q i = fun _ => True := by
          funext a
          apply propext
          constructor
          · intro _; trivial
          · intro _ j hj
            exact False.elim (hi ⟨j, hj⟩)
        rw [htrue, prob_true]
      · intro j
        have hsingle : Q (e j) = fun a => a = y j := by
          funext a
          apply propext
          constructor
          · intro h
            exact h j rfl
          · intro h k hk
            have hkj := he hk
            simpa only [hkj] using h
        rw [hsingle, prob_singleton]
    _ = (pi (fun j => μ (e j))).weight y := rfl

end FiniteLaw

namespace ProductProjections

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Actual image of a retained event under restriction to coordinates `S`. -/
def projected (Z : (ι → A) → Prop) (S : Finset ι) (y : S → A) : Prop :=
  ∃ x, Z x ∧ (fun i : S => x i.val) = y

/-- The map from actual surviving inputs to their projected labels. -/
def retainedProjection (Z : (ι → A) → Prop) (S : Finset ι) :
    {x : ι → A // Z x} → {y : S → A // projected Z S y} :=
  fun x => ⟨fun i => x.val i.val, x.val, x.property, rfl⟩

omit [Fintype ι] [Fintype A] [DecidableEq ι] in
theorem retainedProjection_surjective (Z : (ι → A) → Prop) (S : Finset ι) :
    Function.Surjective (retainedProjection Z S) := by
  rintro ⟨y, x, hx, hxy⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext hxy

/-- A choice of one actual surviving input per projected label. -/
noncomputable def representative (Z : (ι → A) → Prop) (S : Finset ι) :
    {y : S → A // projected Z S y} → {x : ι → A // Z x} :=
  Function.surjInv (retainedProjection_surjective Z S)

omit [Fintype ι] [Fintype A] [DecidableEq ι] in
theorem representative_projection (Z : (ι → A) → Prop) (S : Finset ι)
    (y : {y : S → A // projected Z S y}) :
    retainedProjection Z S (representative Z S y) = y :=
  Function.surjInv_eq (retainedProjection_surjective Z S) y

noncomputable def projectionMass (μ : ι → FiniteLaw A)
    (Z : (ι → A) → Prop) (S : Finset ι) : ℝ :=
  (FiniteLaw.pi (fun i : S => μ i.val)).prob (projected Z S)

omit [Fintype ι] in
theorem projectionMass_nonneg (μ : ι → FiniteLaw A)
    (Z : (ι → A) → Prop) (S : Finset ι) : 0 ≤ projectionMass μ Z S :=
  FiniteLaw.prob_nonneg _ _

omit [Fintype ι] in
theorem projectionMass_le_one (μ : ι → FiniteLaw A)
    (Z : (ι → A) → Prop) (S : Finset ι) : projectionMass μ Z S ≤ 1 :=
  FiniteLaw.prob_le_one _ _

/-- A projection cannot decrease retained mass. -/
theorem prob_le_projectionMass (μ : ι → FiniteLaw A)
    (Z : (ι → A) → Prop) (S : Finset ι) :
    (FiniteLaw.pi μ).prob Z ≤ projectionMass μ Z S := by
  unfold projectionMass
  rw [← FiniteLaw.pi_prob_restrict μ Subtype.val Subtype.val_injective]
  apply FiniteLaw.prob_mono
  intro x hx
  exact ⟨x, hx, rfl⟩

omit [Fintype ι] in
theorem projectionMass_empty_of_nonempty (μ : ι → FiniteLaw A)
    (Z : (ι → A) → Prop) (hZ : ∃ x, Z x) : projectionMass μ Z ∅ = 1 := by
  have htrue : projected Z (∅ : Finset ι) = fun _ => True := by
    funext y
    apply propext
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨x, hx⟩ := hZ
      exact ⟨x, hx, funext fun i => False.elim (Finset.notMem_empty i.val i.property)⟩
  unfold projectionMass
  rw [htrue, FiniteLaw.prob_true]

/-- Ambient independence for genuinely disjoint blocks. Each block event
may impose arbitrary correlations inside that block. -/
theorem prob_disjoint_blocks {κ : Type*} [Fintype κ]
    (μ : ι → FiniteLaw A) (blocks : κ → Finset ι)
    (hdisj : Pairwise (fun j k => Disjoint (blocks j) (blocks k)))
    (E : ∀ j, (blocks j → A) → Prop) :
    (FiniteLaw.pi μ).prob (fun x => ∀ j, E j (fun i => x i.val)) =
      ∏ j, (FiniteLaw.pi (fun i : blocks j => μ i.val)).prob (E j) := by
  classical
  let e : (Σ j, blocks j) → ι := fun z => z.2.val
  have he : Function.Injective e := by
    rintro ⟨j, a⟩ ⟨k, b⟩ hab
    by_cases hjk : j = k
    · subst k
      have hab' : a = b := Subtype.ext hab
      subst b
      rfl
    · have ha : a.val ∈ blocks k := by
        simpa only [show a.val = b.val from hab] using b.property
      exact False.elim ((Finset.disjoint_left.mp (hdisj hjk)) a.property ha)
  let π : (Σ j, blocks j) → FiniteLaw A := fun z => μ (e z)
  let η : ∀ j, FiniteLaw (blocks j → A) :=
    fun j => FiniteLaw.pi (fun i : blocks j => μ i.val)
  calc
    _ = (FiniteLaw.pi π).prob (fun x => ∀ j, E j (fun i => x ⟨j, i⟩)) :=
      FiniteLaw.pi_prob_restrict μ e he (fun x => ∀ j, E j (fun i => x ⟨j, i⟩))
    _ = (FiniteLaw.pi η).prob (fun x => ∀ j, E j (x j)) := by
      unfold FiniteLaw.prob
      apply Fintype.sum_equiv (Equiv.piCurry (fun j (_ : blocks j) => A))
      intro x
      have hw : (FiniteLaw.pi π).weight x =
          (FiniteLaw.pi η).weight (fun j i => x ⟨j, i⟩) := by
        simp only [FiniteLaw.pi, π, η, e, Fintype.prod_sigma]
      have hc : (Equiv.piCurry (fun j (_ : blocks j) => A)) x =
          (fun j i => x ⟨j, i⟩) := rfl
      rw [hc]
      split_ifs
      · exact hw
      · rfl
    _ = _ := FiniteLaw.pi_prob_coordinatewise η E

/-- The product-projection inequality for a finite family of disjoint
coordinate sets. The retained event `Z` need not be a product event. -/
theorem prob_le_prod_projectionMass (μ : ι → FiniteLaw A)
    (Z : (ι → A) → Prop) (P : Finset (Finset ι))
    (hdisj : (P : Set (Finset ι)).Pairwise Disjoint) :
    (FiniteLaw.pi μ).prob Z ≤ ∏ S ∈ P, projectionMass μ Z S := by
  classical
  have hd : Pairwise (fun j k : P => Disjoint j.val k.val) := by
    intro j k hjk
    apply hdisj j.property k.property
    exact fun h => hjk (Subtype.ext h)
  calc
    _ ≤ (FiniteLaw.pi μ).prob
        (fun x => ∀ S : P, projected Z S.val (fun i => x i.val)) := by
      apply FiniteLaw.prob_mono
      intro x hx S
      exact ⟨x, hx, rfl⟩
    _ = ∏ S : P, projectionMass μ Z S.val :=
      prob_disjoint_blocks μ (fun S : P => S.val) hd
        (fun S => projected Z S.val)
    _ = _ := Finset.prod_attach P (fun S => projectionMass μ Z S)

end ProductProjections

end Paper2

#print axioms Paper2.FiniteLaw.pi
#print axioms Paper2.FiniteLaw.pi_prob_restrict
#print axioms Paper2.ProductProjections.prob_le_projectionMass
#print axioms Paper2.ProductProjections.prob_disjoint_blocks
#print axioms Paper2.ProductProjections.prob_le_prod_projectionMass
#print axioms Paper2.ProductProjections.representative_projection
