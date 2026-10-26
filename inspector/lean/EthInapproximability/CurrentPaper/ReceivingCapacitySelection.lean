import EthInapproximability.CurrentPaper.ProductExtraction
import EthInapproximability.CurrentPaper.DensityBucket

/-!
# Dense donor coordinates and an actual Bob child

Source: frozen v8 `A-stage4-details.tex`, the proof of
`lem:paper-early-protected-closure` following
`eq:paper-early-dyadic-class`.

The donor class supplies enough coordinates to avoid a cover of poor sets.
Bob's actual query splits the original retained columns before projection.
The two projected children may overlap; their union is the parent projection,
which is sufficient for the density bound. No protocol cost or receiving
capacity conclusion is assumed or proved by this finite selection step.
-/

namespace EthInapproximability.CurrentPaper.ReceivingCapacitySelection

open ProductExtraction

/-- A class of `u * B` donors leaves at least `u` donors outside a cover
of size at most `u * (B - 1)`. -/
theorem donor_subset_outside_cover {I : Type*} [DecidableEq I]
    (V E : Finset I) {u B : ℕ} (hB : 1 ≤ B)
    (hV : u * B ≤ V.card) (hE : E.card ≤ u * (B - 1)) :
    ∃ J : Finset I, J ⊆ V \ E ∧ J.card = u := by
  have hcard := Finset.card_le_card_sdiff_add_card (s := V) (t := E)
  have hmul : u * (B - 1) + u = u * B := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hB
    rw [hc]
    have hsub : 1 + c - 1 = c := by omega
    rw [hsub, Nat.mul_add, Nat.mul_one]
    omega
  exact Finset.exists_subset_card_eq (show u ≤ (V \ E).card by omega)

section Projection

variable {C : Type*} [Fintype C] [DecidableEq C] {Q : ℕ}

/-- A selected donor set avoids the poor-set cover and has the promised
density in the projection of the actual retained columns. -/
theorem exists_dense_donors (S : Finset (Fin Q → C))
    (V : Finset (Fin Q)) {u B : ℕ} {ρ θ : ℝ}
    (hC : 0 < Fintype.card C) (hu : 1 ≤ u) (hB : 1 ≤ B)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hgate : ρ ^ B < θ)
    (hS : θ * (Fintype.card C : ℝ) ^ Q ≤ (S.card : ℝ))
    (hV : u * B ≤ V.card) :
    ∃ (E J : Finset (Fin Q)), E.card ≤ u * (B - 1) ∧
      J ⊆ V \ E ∧ J.card = u ∧
      ρ * (Fintype.card C : ℝ) ^ u ≤ ((projection J S).card : ℝ) := by
  obtain ⟨E, hE, hcover⟩ := poor_coordinate_cover S hC hu hB hρ0 hρ1 hgate hS
  obtain ⟨J, hJ, hJcard⟩ := donor_subset_outside_cover V E hB hV hE
  have hgood : ¬ Poor ρ J S := by
    intro hpoor
    obtain ⟨j, hj⟩ := hcover J hJcard hpoor
    exact (Finset.mem_sdiff.mp (hJ (Finset.mem_inter.mp hj).2)).2
      (Finset.mem_inter.mp hj).1
  refine ⟨E, J, hE, hJ, hJcard, ?_⟩
  simpa only [Poor, hJcard] using (not_lt.mp hgood)

omit [Fintype C] in
/-- Split the original retained columns by the actual Boolean query.
The projected children have the parent projection as their union, but need
not be disjoint. -/
theorem projection_bob_split (S : Finset (Fin Q → C))
    (J : Finset (Fin Q)) (b : (Fin Q → C) → Bool) :
    projection J (S.filter (fun y => b y = false)) ∪
      projection J (S.filter (fun y => b y = true)) = projection J S := by
  have hsplit : S.filter (fun y => b y = false) ∪
      S.filter (fun y => b y = true) = S := by
    ext y
    cases hb : b y <;> simp [hb]
  simpa only [projection, Finset.image_union] using
    congrArg (projection J) hsplit

/-- Some actual Bob child retains at least half the parent's joint
projection density. Overlap between the projected children causes no loss. -/
theorem exists_dense_bob_child (S : Finset (Fin Q → C))
    (J : Finset (Fin Q)) (b : (Fin Q → C) → Bool) {ρ : ℝ}
    (hS : ρ * (Fintype.card C : ℝ) ^ J.card ≤ ((projection J S).card : ℝ)) :
    ∃ bit : Bool, (ρ / 2) * (Fintype.card C : ℝ) ^ J.card ≤
      ((projection J (S.filter (fun y => b y = bit))).card : ℝ) := by
  have hcards : ((projection J S).card : ℝ) ≤
      ((projection J (S.filter (fun y => b y = false))).card : ℝ) +
      ((projection J (S.filter (fun y => b y = true))).card : ℝ) := by
    have hnat := Finset.card_union_le
      (projection J (S.filter (fun y => b y = false)))
      (projection J (S.filter (fun y => b y = true)))
    rw [projection_bob_split] at hnat
    exact_mod_cast hnat
  by_cases hfalse : (ρ / 2) * (Fintype.card C : ℝ) ^ J.card ≤
      ((projection J (S.filter (fun y => b y = false))).card : ℝ)
  · exact ⟨false, hfalse⟩
  · refine ⟨true, ?_⟩
    have hfalse' := lt_of_not_ge hfalse
    nlinarith

/-- The cover and actual Bob split, in the order used by the paper.
Every surviving projected tuple still has an original column in the selected
child; no new completion of a projected tuple is introduced. -/
theorem exists_dense_donor_bob_child (S : Finset (Fin Q → C))
    (V : Finset (Fin Q)) (b : (Fin Q → C) → Bool) {u B : ℕ} {ρ θ : ℝ}
    (hC : 0 < Fintype.card C) (hu : 1 ≤ u) (hB : 1 ≤ B)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hgate : ρ ^ B < θ)
    (hS : θ * (Fintype.card C : ℝ) ^ Q ≤ (S.card : ℝ))
    (hV : u * B ≤ V.card) :
    ∃ (E J : Finset (Fin Q)) (bit : Bool),
      E.card ≤ u * (B - 1) ∧ J ⊆ V \ E ∧ J.card = u ∧
      ρ * (Fintype.card C : ℝ) ^ u ≤ ((projection J S).card : ℝ) ∧
      (ρ / 2) * (Fintype.card C : ℝ) ^ u ≤
        ((projection J (S.filter (fun y => b y = bit))).card : ℝ) := by
  obtain ⟨E, J, hE, hJ, hJcard, hparent⟩ :=
    exists_dense_donors S V hC hu hB hρ0 hρ1 hgate hS hV
  obtain ⟨bit, hchild⟩ := exists_dense_bob_child S J b
    (by simpa only [hJcard] using hparent)
  exact ⟨E, J, bit, hE, hJ, hJcard, hparent, by simpa only [hJcard] using hchild⟩

end Projection

section Reindexing

variable {C : Type*} [DecidableEq C] {Q u : ℕ}

/-- Projection of original columns to the selected coordinates in their
chosen `Fin u` ordering. -/
def reindexedProjection (J : Finset (Fin Q)) (e : Fin u ≃ ↥J)
    (S : Finset (Fin Q → C)) : Finset (Fin u → C) :=
  S.image (fun y i => y (e i).val)

/-- Reindexing the selected coordinates is a bijection on joint tuples,
so it preserves the cardinality of the original projection. -/
theorem reindexedProjection_card (J : Finset (Fin Q)) (e : Fin u ≃ ↥J)
    (S : Finset (Fin Q → C)) :
    (reindexedProjection J e S).card = (projection J S).card := by
  have heq : reindexedProjection J e S =
      (projection J S).image (fun y i => y (e i)) := by
    simp only [reindexedProjection, projection, Finset.image_image, Function.comp_def]
  rw [heq]
  apply Finset.card_image_of_injective
  intro f g h
  funext j
  simpa using congrFun h (e.symm j)

/-- Membership supplies one original column completing the entire ordered
tuple simultaneously. -/
theorem mem_reindexedProjection_iff (J : Finset (Fin Q)) (e : Fin u ≃ ↥J)
    (S : Finset (Fin Q → C)) (z : Fin u → C) :
    z ∈ reindexedProjection J e S ↔
      ∃ y ∈ S, (fun i => y (e i).val) = z := by
  exact Finset.mem_image

/-- A joint completion in the original retained set. If `S` is the actual
Bob child filter, the completion remains in that same child. -/
noncomputable def reindexedProjectionSection (J : Finset (Fin Q))
    (e : Fin u ≃ ↥J) (S : Finset (Fin Q → C)) :
    ↥(reindexedProjection J e S) → ↥S := fun z =>
  ⟨Classical.choose ((mem_reindexedProjection_iff J e S z.val).mp z.property),
    (Classical.choose_spec ((mem_reindexedProjection_iff J e S z.val).mp z.property)).1⟩

/-- The chosen completion agrees with every coordinate of the same tuple. -/
theorem reindexedProjectionSection_apply (J : Finset (Fin Q))
    (e : Fin u ≃ ↥J) (S : Finset (Fin Q → C))
    (z : ↥(reindexedProjection J e S)) (i : Fin u) :
    (reindexedProjectionSection J e S z).val (e i).val = z.val i := by
  exact congrFun
    (Classical.choose_spec ((mem_reindexedProjection_iff J e S z.val).mp z.property)).2 i

end Reindexing

/-- The donor cover and actual Bob-child choice for the dyadic density class
already constructed from the incoming mass. -/
theorem dense_bob_child_of_selection {C : Type*} [Fintype C] [DecidableEq C]
    {r B s κ : ℕ} {donors : Finset (Fin (2 ^ r))} {d : Fin (2 ^ r) → ℝ}
    (sel : DensityBucket.Selection donors d B s κ)
    (S : Finset (Fin (2 ^ r) → C)) (b : (Fin (2 ^ r) → C) → Bool)
    {ρ θ : ℝ} (hC : 0 < Fintype.card C) (hB : 1 ≤ B)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hgate : ρ ^ B < θ)
    (hS : θ * (Fintype.card C : ℝ) ^ (2 ^ r) ≤ (S.card : ℝ)) :
    ∃ (J : Finset (Fin (2 ^ r))) (bit : Bool), J ⊆ sel.coordinates ∧
      J.card = 2 ^ sel.widthExponent ∧
      (∀ j ∈ J, (1 / (2 : ℝ) ^ sel.classExponent) / 2 < d j ∧
        d j ≤ 1 / (2 : ℝ) ^ sel.classExponent) ∧
      ρ * (Fintype.card C : ℝ) ^ (2 ^ sel.widthExponent) ≤
        ((projection J S).card : ℝ) ∧
      (ρ / 2) * (Fintype.card C : ℝ) ^ (2 ^ sel.widthExponent) ≤
        ((projection J (S.filter (fun y => b y = bit))).card : ℝ) := by
  have hu : 1 ≤ 2 ^ sel.widthExponent := by
    have hpos : 0 < 2 ^ sel.widthExponent := by positivity
    omega
  obtain ⟨E, J, bit, _, hJ, hJcard, hparent, hchild⟩ :=
    exists_dense_donor_bob_child S sel.coordinates b hC hu hB hρ0 hρ1 hgate hS
      sel.enough_coordinates
  have hJV : J ⊆ sel.coordinates := hJ.trans Finset.sdiff_subset
  exact ⟨J, bit, hJV, hJcard, fun j hj => sel.class_bounds j (hJV hj), hparent, hchild⟩

end EthInapproximability.CurrentPaper.ReceivingCapacitySelection
