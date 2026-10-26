import Paper2.RationalLaws
import Paper2.InterlaceRank

/-!
# Full-tuple transport for rational input laws

Frozen source: v12 Appendix A, `cl:rational-laws`, especially the statements
that independent duplicate choices have the original product law and that
retained sets need not themselves be independent. The public manuscript may
have a later author-only version; this module retains the v12 statement lock.

Every event below may depend on the whole tuple. In particular, retained
tuple sets are not replaced by products of their coordinate projections.
The module does not prove the numerical ceiling repair or the complete
interlacing-profile theorem.
-/

namespace Paper2

open scoped BigOperators
open Workspace.Types.CommComplexity
open RankLeaves

namespace FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

@[simp] theorem prob_singleton (μ : FiniteLaw α) (a : α) :
    μ.prob (fun x => x = a) = μ.weight a := by
  classical
  simp [prob]

/-- Equality of all point-fibre masses gives equality for every event,
without any restriction on the shape of that event. -/
theorem prob_preimage_eq_of_fibres (μ : FiniteLaw α) (ν : FiniteLaw β)
    (f : α → β) (hf : ∀ b, μ.prob (fun a => f a = b) = ν.weight b)
    (E : β → Prop) : μ.prob (fun a => E (f a)) = ν.prob E := by
  classical
  calc
    _ = ∑ a, ∑ b, if f a = b then (if E b then μ.weight a else 0) else 0 := by
      unfold prob
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ b, ∑ a, if f a = b then (if E b then μ.weight a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ b, if E b then μ.prob (fun a => f a = b) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : E b
      · simp only [hb, ↓reduceIte, prob]
      · simp [hb]
    _ = ν.prob E := by
      simp_rw [hf]
      rfl

/-- Coordinatewise events may differ from coordinate to coordinate. -/
theorem iid_prob_coordinatewise (μ : FiniteLaw α) (m : ℕ)
    (E : Fin m → α → Prop) :
    (μ.iid m).prob (fun x => ∀ i, E i (x i)) = ∏ i, μ.prob (E i) := by
  classical
  have hprod (x : Fin m → α) :
      (if ∀ i, E i (x i) then ∏ i, μ.weight (x i) else 0) =
        ∏ i, if E i (x i) then μ.weight (x i) else 0 := by
    by_cases hx : ∀ i, E i (x i)
    · simp [hx]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      simp only [hx, ↓reduceIte]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp only [prob, iid]
  simp_rw [hprod]
  exact (Fintype.prod_sum (fun i a => if E i a then μ.weight a else 0)).symm

/-- Independent pushforward commutes with the entire joint law. The event
`E` is an arbitrary predicate on full tuples, not a product event. -/
theorem iid_prob_preimage (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β)
    (hf : ∀ b, μ.prob (fun a => f a = b) = ν.weight b)
    (m : ℕ) (E : (Fin m → β) → Prop) :
    (μ.iid m).prob (fun x => E (fun i => f (x i))) = (ν.iid m).prob E := by
  apply prob_preimage_eq_of_fibres (μ.iid m) (ν.iid m) (fun x i => f (x i))
  intro y
  calc
    _ = (μ.iid m).prob (fun x => ∀ i, f (x i) = y i) := by
      unfold prob
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i, f (x i) = y i
      · simp [hx]
      · have he : (fun i => f (x i)) ≠ y := fun h => hx (fun i => congrFun h i)
        simp [hx, he]
    _ = ∏ i, μ.prob (fun a => f a = y i) :=
      iid_prob_coordinatewise μ m (fun i a => f a = y i)
    _ = ∏ i, ν.weight (y i) := by simp_rw [hf]
    _ = (ν.iid m).weight y := rfl

end FiniteLaw

namespace PositiveRationalLaw

variable {α : Type*} [Fintype α]

/-- Forget only duplicate labels, retaining the entire indexed tuple. -/
def forgetTuple (μ : PositiveRationalLaw α) (m : ℕ) :
    (Fin m → μ.Copies) → (Fin m → α) := fun z i => μ.forget (z i)

theorem forgetTuple_surjective (μ : PositiveRationalLaw α) (m : ℕ) :
    Function.Surjective (μ.forgetTuple m) := by
  intro x
  exact ⟨fun i => ⟨x i, ⟨0, μ.multiplicity_pos (x i)⟩⟩, rfl⟩

theorem card_copy_tuples (μ : PositiveRationalLaw α) (m : ℕ) :
    Fintype.card (Fin m → μ.Copies) = μ.denominator ^ m := by
  simp [μ.card_copies]

theorem uniformCopies_iid_weight (μ : PositiveRationalLaw α) (m : ℕ)
    (z : Fin m → μ.Copies) :
    (μ.uniformCopies.iid m).weight z = ((μ.denominator : ℝ)⁻¹) ^ m := by
  simp [FiniteLaw.iid, uniformCopies]

/-- Equality of the joint iid laws for every full-tuple event. -/
theorem uniformCopies_iid_prob_preimage (μ : PositiveRationalLaw α)
    (m : ℕ) (E : (Fin m → α) → Prop) :
    (μ.uniformCopies.iid m).prob (fun z => E (μ.forgetTuple m z)) =
      (μ.toFiniteLaw.iid m).prob E := by
  apply FiniteLaw.iid_prob_preimage μ.uniformCopies μ.toFiniteLaw μ.forget
  intro a
  rw [μ.uniformCopies_prob_preimage (fun x => x = a), FiniteLaw.prob_singleton]

/-- Image of an arbitrary retained tuple set under forgetting copy labels.
There is no assumption of coordinatewise independence or rectangularity. -/
def projectedTuples (μ : PositiveRationalLaw α) (m : ℕ)
    (S : (Fin m → μ.Copies) → Prop) (x : Fin m → α) : Prop :=
  ∃ z, S z ∧ μ.forgetTuple m z = x

theorem projectedTuples_preimage (μ : PositiveRationalLaw α) (m : ℕ)
    (T : (Fin m → α) → Prop) (x : Fin m → α) :
    μ.projectedTuples m (fun z => T (μ.forgetTuple m z)) x ↔ T x := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    exact hzx ▸ hz
  · intro hx
    obtain ⟨z, hzx⟩ := μ.forgetTuple_surjective m x
    exact ⟨z, by simpa only [hzx] using hx, hzx⟩

/-- The mass of an arbitrary retained copy-tuple set is bounded by the
original product-law mass of its actual image. -/
theorem uniformCopies_iid_prob_le_projection (μ : PositiveRationalLaw α)
    (m : ℕ) (S : (Fin m → μ.Copies) → Prop) :
    (μ.uniformCopies.iid m).prob S ≤
      (μ.toFiniteLaw.iid m).prob (μ.projectedTuples m S) := by
  rw [← μ.uniformCopies_iid_prob_preimage m]
  apply (μ.uniformCopies.iid m).prob_mono
  intro z hz
  exact ⟨z, hz, rfl⟩

/-- Each original tuple in the image has an actual retained copy-tuple
representative, not an invented tuple assembled from different witnesses. -/
def forgetRetainedTuple (μ : PositiveRationalLaw α) (m : ℕ)
    (S : (Fin m → μ.Copies) → Prop) :
    {z : Fin m → μ.Copies // S z} → {x : Fin m → α // μ.projectedTuples m S x} :=
  fun z => ⟨μ.forgetTuple m z.val, z.val, z.property, rfl⟩

theorem forgetRetainedTuple_surjective (μ : PositiveRationalLaw α) (m : ℕ)
    (S : (Fin m → μ.Copies) → Prop) :
    Function.Surjective (μ.forgetRetainedTuple m S) := by
  rintro ⟨x, z, hz, hzx⟩
  refine ⟨⟨z, hz⟩, ?_⟩
  exact Subtype.ext hzx

/-- Forget row-copy labels without changing the interlace selector. -/
def forgetBlock (μ : PositiveRationalLaw α) (q : ℕ) :
    (Fin q × μ.Copies) → (Fin q × α) := fun z => (z.1, μ.forget z.2)

theorem forgetBlock_surjective (μ : PositiveRationalLaw α) (q : ℕ) :
    Function.Surjective (μ.forgetBlock q) := by
  rintro ⟨i, a⟩
  exact ⟨⟨i, ⟨a, ⟨0, μ.multiplicity_pos a⟩⟩⟩, rfl⟩

/-- Full-event equality for selector-labelled rows. The selector may have
any finite law; choosing its uniform law gives the interlace convention. -/
theorem uniformCopies_block_prob_preimage (μ : PositiveRationalLaw α)
    (q : ℕ) (σ : FiniteLaw (Fin q)) (E : (Fin q × α) → Prop) :
    (σ.prod μ.uniformCopies).prob (fun z => E (μ.forgetBlock q z)) =
      (σ.prod μ.toFiniteLaw).prob E := by
  calc
    _ = ∑ i, σ.weight i * μ.uniformCopies.prob (fun z => E (i, μ.forget z)) :=
      FiniteLaw.prod_prob σ μ.uniformCopies (fun i z => E (i, μ.forget z))
    _ = ∑ i, σ.weight i * μ.toFiniteLaw.prob (fun a => E (i, a)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [μ.uniformCopies_prob_preimage (fun a => E (i, a))]
    _ = _ := (FiniteLaw.prod_prob σ μ.toFiniteLaw (fun i a => E (i, a))).symm

def projectedBlocks (μ : PositiveRationalLaw α) (q : ℕ)
    (S : (Fin q × μ.Copies) → Prop) (a : Fin q × α) : Prop :=
  ∃ z, S z ∧ μ.forgetBlock q z = a

theorem projectedBlocks_preimage (μ : PositiveRationalLaw α) (q : ℕ)
    (T : (Fin q × α) → Prop) (a : Fin q × α) :
    μ.projectedBlocks q (fun z => T (μ.forgetBlock q z)) a ↔ T a := by
  constructor
  · rintro ⟨z, hz, hza⟩
    exact hza ▸ hz
  · intro ha
    obtain ⟨z, hza⟩ := μ.forgetBlock_surjective q a
    exact ⟨z, by simpa only [hza] using ha, hza⟩

theorem uniformCopies_block_prob_le_projection (μ : PositiveRationalLaw α)
    (q : ℕ) (σ : FiniteLaw (Fin q)) (S : (Fin q × μ.Copies) → Prop) :
    (σ.prod μ.uniformCopies).prob S ≤
      (σ.prod μ.toFiniteLaw).prob (μ.projectedBlocks q S) := by
  rw [← μ.uniformCopies_block_prob_preimage q σ]
  apply (σ.prod μ.uniformCopies).prob_mono
  intro z hz
  exact ⟨z, hz, rfl⟩

def forgetRetainedBlock (μ : PositiveRationalLaw α) (q : ℕ)
    (S : (Fin q × μ.Copies) → Prop) :
    {z : Fin q × μ.Copies // S z} → {a : Fin q × α // μ.projectedBlocks q S a} :=
  fun z => ⟨μ.forgetBlock q z.val, z.val, z.property, rfl⟩

theorem forgetRetainedBlock_surjective (μ : PositiveRationalLaw α) (q : ℕ)
    (S : (Fin q × μ.Copies) → Prop) :
    Function.Surjective (μ.forgetRetainedBlock q S) := by
  rintro ⟨a, z, hz, hza⟩
  refine ⟨⟨z, hz⟩, ?_⟩
  exact Subtype.ext hza

end PositiveRationalLaw

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Duplicating each original input before taking the full interlace gives
an actual pullback by the block and full-tuple forgetting maps. -/
theorem rationalCopies_interlace_entry (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool) (q : ℕ)
    (a : Fin q × μ.Copies) (z : Fin q → ν.Copies) :
    fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q a z =
      fullInterlace F q (μ.forgetBlock q a) (ν.forgetTuple q z) := rfl

theorem rationalCopies_interlace_D_eq (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool) (q : ℕ) :
    D (fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q) =
      D (fullInterlace F q) :=
  pullback_D_eq_of_surjective (fullInterlace F q)
    (μ.forgetBlock q) (ν.forgetTuple q)
    (μ.forgetBlock_surjective q) (ν.forgetTuple_surjective q)

theorem rationalCopies_interlace_rank_eq (μ : PositiveRationalLaw X)
    (ν : PositiveRationalLaw Y) (F : X → Y → Bool) (q : ℕ) :
    (realMatrix (fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q)).rank =
      (realMatrix (fullInterlace F q)).rank :=
  pullback_rank_eq_of_surjective (fullInterlace F q)
    (μ.forgetBlock q) (ν.forgetTuple q)
    (μ.forgetBlock_surjective q) (ν.forgetTuple_surjective q)

/-- Exact communication transport for arbitrary retained row blocks and
arbitrary retained full tuples. The projected column family is its actual
image, not the product of coordinate projections. -/
theorem rationalCopies_restricted_interlace_D_eq
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (q : ℕ)
    (S : (Fin q × μ.Copies) → Prop) (T : (Fin q → ν.Copies) → Prop)
    [Fintype {z : Fin q × μ.Copies // S z}]
    [Fintype {z : Fin q → ν.Copies // T z}]
    [Fintype {a : Fin q × X // μ.projectedBlocks q S a}]
    [Fintype {z : Fin q → Y // ν.projectedTuples q T z}] :
    D (fun a : {a : Fin q × μ.Copies // S a} =>
      fun z : {z : Fin q → ν.Copies // T z} =>
      fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q a.val z.val) =
    D (fun a : {a : Fin q × X // μ.projectedBlocks q S a} =>
      fun z : {z : Fin q → Y // ν.projectedTuples q T z} =>
      fullInterlace F q a.val z.val) := by
  exact pullback_D_eq_of_surjective
    (fun a : {a : Fin q × X // μ.projectedBlocks q S a} =>
      fun z : {z : Fin q → Y // ν.projectedTuples q T z} =>
      fullInterlace F q a.val z.val)
    (μ.forgetRetainedBlock q S) (ν.forgetRetainedTuple q T)
    (μ.forgetRetainedBlock_surjective q S) (ν.forgetRetainedTuple_surjective q T)

theorem rationalCopies_restricted_interlace_rank_eq
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (q : ℕ)
    (S : (Fin q × μ.Copies) → Prop) (T : (Fin q → ν.Copies) → Prop)
    [Fintype {z : Fin q → ν.Copies // T z}]
    [Fintype {z : Fin q → Y // ν.projectedTuples q T z}] :
    (realMatrix (fun a : {a : Fin q × μ.Copies // S a} =>
      fun z : {z : Fin q → ν.Copies // T z} =>
      fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q a.val z.val)).rank =
    (realMatrix (fun a : {a : Fin q × X // μ.projectedBlocks q S a} =>
      fun z : {z : Fin q → Y // ν.projectedTuples q T z} =>
      fullInterlace F q a.val z.val)).rank := by
  exact pullback_rank_eq_of_surjective
    (fun a : {a : Fin q × X // μ.projectedBlocks q S a} =>
      fun z : {z : Fin q → Y // ν.projectedTuples q T z} =>
      fullInterlace F q a.val z.val)
    (μ.forgetRetainedBlock q S) (ν.forgetRetainedTuple q T)
    (μ.forgetRetainedBlock_surjective q S) (ν.forgetRetainedTuple_surjective q T)

end Paper2

#print axioms Paper2.FiniteLaw.iid_prob_preimage
#print axioms Paper2.PositiveRationalLaw.uniformCopies_iid_prob_preimage
#print axioms Paper2.PositiveRationalLaw.uniformCopies_iid_prob_le_projection
#print axioms Paper2.PositiveRationalLaw.uniformCopies_block_prob_preimage
#print axioms Paper2.PositiveRationalLaw.uniformCopies_block_prob_le_projection
#print axioms Paper2.rationalCopies_interlace_D_eq
#print axioms Paper2.rationalCopies_interlace_rank_eq
#print axioms Paper2.rationalCopies_restricted_interlace_D_eq
#print axioms Paper2.rationalCopies_restricted_interlace_rank_eq
