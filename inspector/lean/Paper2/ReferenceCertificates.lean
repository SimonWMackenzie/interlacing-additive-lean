import Paper2.SourceSupportStep

/-!
# Reference supports retained in both qualifying children

Frozen v12 Section 5, `res:destinations`, lines 250--310. A reference
certificate has weight one until its first split and weight one-half
thereafter, even if it splits again. We store the actual original labels,
the active coordinate set, and its unsplit subset. Weight is derived from
these finite sets, never supplied as a field or conservation certificate.

The protocol and its complete stopping tree are constructed separately.
These local transitions use the actual query on each original label.
-/

namespace Paper2.ReferenceCertificates

open SourceSupportStep

variable {I W : Type*} [Fintype W]

structure Family (I W : Type*) where
  active : Finset I
  unsplit : Finset I
  support : I → Finset W

/-- Twice the total reference weight: one unit for every active support,
and one further unit for each support that has never split. -/
def units (S : Family I W) : ℕ := S.active.card + S.unsplit.card

/-- Keep both qualifying fibres. Only supports that were already unsplit
can remain unsplit; a later split never restores weight one. -/
noncomputable def child (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool) : Family I W where
  active := childCoordinates μ S.active S.active S.support query t b
  unsplit := childAttachments μ S.unsplit S.support query t b
  support := childSupport S.support query b

theorem child_active_subset (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool) :
    (child μ S query t b).active ⊆ S.active :=
  childCoordinates_subset μ S.active S.active S.support query t b

theorem child_unsplit_subset (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool) :
    (child μ S query t b).unsplit ⊆ S.unsplit := by
  intro i hi
  exact ((mem_childAttachments μ S.unsplit S.support query t b i).mp hi).1

theorem child_valid (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool)
    (hS : S.unsplit ⊆ S.active) :
    (child μ S query t b).unsplit ⊆ (child μ S query t b).active := by
  intro i hi
  obtain ⟨hi, _, hb⟩ := (mem_childAttachments μ S.unsplit S.support query t b i).mp hi
  exact (mem_childCoordinates μ S.active S.active S.support query t b i).mpr
    ⟨hS hi, Or.inr hb⟩

theorem child_floor (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool)
    (hS : ∀ i ∈ S.active, 2 * t ≤ mass μ (S.support i)) :
    ∀ i ∈ (child μ S query t b).active,
      t ≤ mass μ ((child μ S query t b).support i) :=
  SourceSupportStep.child_floor μ S.active S.active S.support query t b hS

/-- This rule retains exactly the qualifying original fibres, not merely
one heavier child. The parent floor is what rules out two small children. -/
theorem child_active_iff (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool)
    (hS : ∀ i ∈ S.active, 2 * t ≤ mass μ (S.support i)) (i : I) :
    i ∈ (child μ S query t b).active ↔
      i ∈ S.active ∧ t ≤ mass μ (fibre (S.support i) (query i) b) := by
  constructor
  · intro hi
    exact ⟨child_active_subset μ S query t b hi, child_floor μ S query t b hS i hi⟩
  · rintro ⟨hi, hf⟩
    apply (mem_childCoordinates μ S.active S.active S.support query t b i).mpr
    refine ⟨hi, ?_⟩
    by_cases hb : Both μ (S.support i) (query i) t
    · exact Or.inl ((mem_splits μ S.active S.support query t i).mpr ⟨hi, hb⟩)
    · right
      have ho := other_lt_of_not_both μ (S.support i) (query i) t hb
      cases he : heavyBit μ (S.support i) (query i) <;> cases b <;>
        simp_all only [Bool.not_false, Bool.not_true] <;> linarith

theorem child_reaches {C : Type*} (μ : FiniteLaw W) (S : Family I W)
    (input : I → W → C) (query : C → Bool) (U : Set C) (t : ℝ) (b : Bool)
    (hS : ∀ i ∈ S.active, ∀ w ∈ S.support i, input i w ∈ U) :
    ∀ i ∈ (child μ S (fun i w => query (input i w)) t b).active,
      ∀ w ∈ (child μ S (fun i w => query (input i w)) t b).support i,
        input i w ∈ U ∧ query (input i w) = b :=
  childSupport_reaches μ S.active S.active S.support input query U t b hS

/-- The same original coordinate cannot remain unsplit in both children. -/
theorem unsplit_disjoint (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) :
    Disjoint (child μ S query t false).unsplit
      (child μ S query t true).unsplit :=
  childAttachments_disjoint μ S.unsplit S.support query t

theorem unsplit_loss (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (b : Bool) (i : I)
    (hi : i ∈ (child μ S query t b).unsplit) :
    mass μ (S.support i) - mass μ ((child μ S query t b).support i) < t :=
  attachment_loss μ S.unsplit S.support query t b i hi

/-- A split of an already half-weight support can increase weight, but
neither the first split nor a nonsplitting step can decrease it. -/
theorem units_nondecreasing (μ : FiniteLaw W) (S : Family I W)
    (query : I → W → Bool) (t : ℝ) (hS : S.unsplit ⊆ S.active) :
    units S ≤ units (child μ S query t false) + units (child μ S query t true) := by
  classical
  have hsplit : splits μ S.unsplit S.support query t ⊆
      splits μ S.active S.support query t := by
    intro i hi
    obtain ⟨hi, hb⟩ := (mem_splits μ S.unsplit S.support query t i).mp hi
    exact (mem_splits μ S.active S.support query t i).mpr ⟨hS hi, hb⟩
  have hle := Finset.card_le_card hsplit
  have hQ := childCoordinates_card μ S.active S.active S.support query t
    (Finset.Subset.refl S.active)
  have hU := childAttachments_card μ S.unsplit S.support query t
  dsimp only [units, child]
  omega

/-- Starting with one unsplit support per coordinate gives unit weight
per coordinate, rather than assuming an initial total-weight bound. -/
def initial (Q : Finset I) (support : I → Finset W) : Family I W := ⟨Q, Q, support⟩

omit [Fintype W] in
@[simp] theorem initial_units (Q : Finset I) (support : I → Finset W) :
    units (initial Q support) = 2 * Q.card := by
  simp [units, initial, two_mul]

end Paper2.ReferenceCertificates

#print axioms Paper2.ReferenceCertificates.child_active_iff
#print axioms Paper2.ReferenceCertificates.child_reaches
#print axioms Paper2.ReferenceCertificates.unsplit_disjoint
#print axioms Paper2.ReferenceCertificates.unsplit_loss
#print axioms Paper2.ReferenceCertificates.units_nondecreasing
