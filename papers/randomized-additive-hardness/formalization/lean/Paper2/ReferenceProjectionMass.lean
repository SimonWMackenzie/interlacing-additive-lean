import Paper2.ReferenceCapacity
import Paper2.RestorationPublicCovers

/-!
# Exact masses of actual reference projections

Frozen v12 Sections 4--5, `eq:product-projection` and the restoration
exceptional-coordinate covers. All images below are images of one arbitrary
retained tuple event, not products of separately retained marginals.
-/

namespace Paper2.ReferenceProjectionMass

variable {K : Type*} [Fintype K] {w n : ℕ}

/-- A bijective enumeration of a coordinate set identifies its projection
mass with the iid mass of the one joint selected-column image. This includes
the empty coordinate set. -/
theorem projectionMass_eq_selectedColumns (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (S : Finset (Fin w)) (e : Fin n ≃ S) :
    ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S =
      (κ.iid n).prob (· ∈ ReferenceCapacity.selectedColumns
        (fun j => (e j).val) Y') := by
  classical
  let E : (Fin n → K) → Prop := fun z => z ∈
    ReferenceCapacity.selectedColumns (fun j => (e j).val) Y'
  have hpoint (x : S → K) :
      ProductProjections.projected (· ∈ Y') S x ↔
        E (fun j => x (e j)) := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, ?_⟩
      funext i
      have hi := congrFun h (e.symm i)
      simpa using hi
  calc
    _ = (FiniteLaw.pi (fun _ : S => κ)).prob
        (fun x => E (fun j => x (e j))) := by
          unfold ProductProjections.projectionMass
          congr 1
          funext x
          exact propext (hpoint x)
    _ = (FiniteLaw.pi (fun _ : Fin n => κ)).prob E :=
      FiniteLaw.pi_prob_restrict (fun _ : S => κ) e e.injective E
    _ = _ := by
      exact RestorationCovers.pi_const_prob κ n E

/-- The same identity for a concrete injective list of original labels. -/
theorem projectionMass_eq_selectedColumns_of_injective (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (S : Finset (Fin w))
    (e : Fin n → Fin w) (he : Function.Injective e)
    (himage : Finset.univ.image e = S) :
    ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S =
      (κ.iid n).prob (· ∈ ReferenceCapacity.selectedColumns e Y') := by
  classical
  let eS : Fin n → S := fun j => ⟨e j, by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have heS : Function.Bijective eS := by
    constructor
    · intro i j h
      exact he (congrArg Subtype.val h)
    · rintro ⟨i, hi⟩
      rw [← himage] at hi
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
      exact ⟨j, Subtype.ext hj⟩
  let eEquiv : Fin n ≃ S := Equiv.ofBijective eS heS
  simpa only [eEquiv, eS, Equiv.ofBijective_apply] using
    projectionMass_eq_selectedColumns κ Y' S eEquiv

/-- Any lower bound on one coordinate projection transfers unchanged to its
selected tuple, with no independence assumption on the retained set. -/
theorem selectedColumns_mass_ge (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (S : Finset (Fin w)) (e : Fin n ≃ S)
    (ρ : ℝ)
    (hgood : ρ ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) :
    ρ ≤ (κ.iid n).prob (· ∈ ReferenceCapacity.selectedColumns
      (fun j => (e j).val) Y') := by
  rwa [projectionMass_eq_selectedColumns κ Y' S e] at hgood

/-- A two-position iid sample is exactly an ordered pair of independent
samples. This is an equality for every joint event on pairs. -/
theorem iid_two_pair_prob (κ : FiniteLaw K) (E : (K × K) → Prop) :
    (κ.iid 2).prob (fun z => E (z 0, z 1)) =
      (κ.prod κ).prob E := by
  classical
  let pairEquiv : (Fin 2 → K) ≃ K × K := {
    toFun := fun (z : Fin 2 → K) => (z 0, z 1)
    invFun := fun (p : K × K) (t : Fin 2) => if t = 0 then p.1 else p.2
    left_inv := by
      intro z
      funext t
      fin_cases t <;> simp
    right_inv := by
      intro p
      cases p
      simp }
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv pairEquiv
  intro z
  change (if E (z 0, z 1) then ∏ i : Fin 2, κ.weight (z i) else 0) =
    (if E (pairEquiv z) then κ.weight (pairEquiv z).1 *
      κ.weight (pairEquiv z).2 else 0)
  simp only [pairEquiv, Equiv.coe_fn_mk]
  simp only [Fin.prod_univ_two]

/-- A one-position iid sample is the original coordinate law. -/
theorem iid_one_coordinate_prob (κ : FiniteLaw K) (E : K → Prop) :
    (κ.iid 1).prob (fun z => E (z 0)) = κ.prob E := by
  classical
  let oneEquiv : (Fin 1 → K) ≃ K := {
    toFun := fun z => z 0
    invFun := fun a _ => a
    left_inv := by
      intro z
      funext t
      fin_cases t
      rfl
    right_inv := by intro a; rfl }
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv oneEquiv
  intro z
  change (if E (z 0) then ∏ i : Fin 1, κ.weight (z i) else 0) =
    (if E (oneEquiv z) then κ.weight (oneEquiv z) else 0)
  simp [oneEquiv]

/-- The singleton cover controls the actual original-coordinate image. -/
theorem singleton_image_mass_eq_projectionMass (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (i : Fin w) :
    κ.prob (· ∈ (fun y => y i) '' Y') =
      ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') {i} := by
  classical
  let e : Fin 1 → Fin w := fun _ => i
  have he : Function.Injective e := by
    intro a b _
    fin_cases a
    fin_cases b
    rfl
  have himage : Finset.univ.image e = ({i} : Finset (Fin w)) := by
    ext k
    simp [e]
  calc
    _ = (κ.iid 1).prob (fun z => z 0 ∈ (fun y => y i) '' Y') :=
      (iid_one_coordinate_prob κ _).symm
    _ = (κ.iid 1).prob (· ∈ ReferenceCapacity.selectedColumns e Y') := by
      congr 1
      funext z
      apply propext
      constructor
      · rintro ⟨y, hy, h⟩
        refine ⟨y, hy, ?_⟩
        funext t
        fin_cases t
        simpa [e] using h
      · rintro ⟨y, hy, h⟩
        refine ⟨y, hy, ?_⟩
        simpa [e] using congrArg (fun z : Fin 1 → K => z 0) h
    _ = _ := (projectionMass_eq_selectedColumns_of_injective κ Y' {i} e he himage).symm

theorem singleton_image_mass_ge (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (i : Fin w) (ρ : ℝ)
    (hgood : ρ ≤ ProductProjections.projectionMass
      (fun _ => κ) (· ∈ Y') {i}) :
    ρ ≤ κ.prob (· ∈ (fun y => y i) '' Y') := by
  simpa only [singleton_image_mass_eq_projectionMass κ Y' i] using hgood

/-- Ordered original labels expose exactly their joint pair image; no
product of singleton projected events is introduced. -/
theorem pair_image_mass_eq_projectionMass (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (i j : Fin w) (hij : i ≠ j) :
    (κ.prod κ).prob (· ∈ (fun y => (y i, y j)) '' Y') =
      ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') {i, j} := by
  classical
  let e : Fin 2 → Fin w := fun t => if t = 0 then i else j
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [e, hij] at hab ⊢
    exact False.elim (hij hab.symm)
  have himage : Finset.univ.image e = ({i, j} : Finset (Fin w)) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      fin_cases t <;> simp [e]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [e]⟩
      · exact ⟨1, by simp [e]⟩
  calc
    _ = (κ.iid 2).prob
        (fun z => (z 0, z 1) ∈ (fun y => (y i, y j)) '' Y') :=
      (iid_two_pair_prob κ _).symm
    _ = (κ.iid 2).prob (· ∈ ReferenceCapacity.selectedColumns e Y') := by
      congr 1
      funext z
      apply propext
      constructor
      · rintro ⟨y, hy, h⟩
        refine ⟨y, hy, ?_⟩
        have hp := Prod.mk.inj h
        funext t
        fin_cases t
        · simpa [e] using hp.1
        · simpa [e] using hp.2
      · rintro ⟨y, hy, h⟩
        refine ⟨y, hy, ?_⟩
        have h0 := congrArg (fun z : Fin 2 → K => z 0) h
        have h1 := congrArg (fun z : Fin 2 → K => z 1) h
        exact Prod.ext (by simpa [e] using h0) (by simpa [e] using h1)
    _ = _ := (projectionMass_eq_selectedColumns_of_injective κ Y' {i, j} e he himage).symm

/-- The pair-cover threshold has precisely the premise of the original
foreign-owner pair package. -/
theorem pair_image_mass_ge (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (i j : Fin w) (hij : i ≠ j)
    (ρ : ℝ)
    (hgood : ρ ≤ ProductProjections.projectionMass
      (fun _ => κ) (· ∈ Y') {i, j}) :
    ρ ≤ (κ.prod κ).prob (· ∈ (fun y => (y i, y j)) '' Y') := by
  simpa only [pair_image_mass_eq_projectionMass κ Y' i j hij] using hgood

/-- The public singleton cover yields the original one-coordinate event. -/
theorem singleton_good_of_public_cover (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (E₀ : Finset (Fin w)) (eta : ℝ)
    (hcover : ∀ S : Finset (Fin w), S.card = 1 → Disjoint S E₀ →
      1 - eta ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S)
    (i : Fin w) (hi : i ∉ E₀) :
    1 - eta ≤ κ.prob (· ∈ (fun y => y i) '' Y') := by
  apply singleton_image_mass_ge κ Y' i (1 - eta)
  apply hcover {i} (by simp)
  simp [Finset.disjoint_singleton_left, hi]

/-- The public pair cover yields the ordered two-coordinate event needed
by the original foreign-owner package. -/
theorem pair_good_of_public_cover (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (E₀ : Finset (Fin w))
    (hcover : ∀ S : Finset (Fin w), S.card = 2 → Disjoint S E₀ →
      (99 / 100 : ℝ) ≤
        ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S)
    (i j : Fin w) (hij : i ≠ j) (hi : i ∉ E₀) (hj : j ∉ E₀) :
    (99 / 100 : ℝ) ≤
      (κ.prod κ).prob (· ∈ (fun y => (y i, y j)) '' Y') := by
  apply pair_image_mass_ge κ Y' i j hij (99 / 100)
  apply hcover {i, j} (by simp [hij])
  simp [Finset.disjoint_left, hi, hj]

/-- The dyadic cover lower bound applies to the one joint selected tuple,
not a Cartesian product of its singleton images. -/
theorem dyadic_good_of_public_cover (κ : FiniteLaw K)
    (Y' : Set (Fin w → K)) (E₀ : Finset (Fin w))
    (m : ℕ)
    (hcover : ∀ j : Fin (m - 2), ∀ S : Finset (Fin w),
      S.card = RestorationCovers.smallSize j.val → Disjoint S E₀ →
        (18 / 25 : ℝ) ≤
          ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S)
    (j : Fin (m - 2)) (S : Finset (Fin w))
    (hcard : S.card = RestorationCovers.smallSize j.val)
    (hdisj : Disjoint S E₀) (e : Fin n ≃ S) :
    (18 / 25 : ℝ) ≤
      (κ.iid n).prob (· ∈ ReferenceCapacity.selectedColumns
        (fun a => (e a).val) Y') :=
  selectedColumns_mass_ge κ Y' S e (18 / 25) (hcover j S hcard hdisj)

end Paper2.ReferenceProjectionMass

#print axioms Paper2.ReferenceProjectionMass.projectionMass_eq_selectedColumns
#print axioms Paper2.ReferenceProjectionMass.projectionMass_eq_selectedColumns_of_injective
#print axioms Paper2.ReferenceProjectionMass.selectedColumns_mass_ge
#print axioms Paper2.ReferenceProjectionMass.iid_two_pair_prob
#print axioms Paper2.ReferenceProjectionMass.iid_one_coordinate_prob
#print axioms Paper2.ReferenceProjectionMass.singleton_image_mass_eq_projectionMass
#print axioms Paper2.ReferenceProjectionMass.singleton_image_mass_ge
#print axioms Paper2.ReferenceProjectionMass.pair_image_mass_eq_projectionMass
#print axioms Paper2.ReferenceProjectionMass.pair_image_mass_ge
#print axioms Paper2.ReferenceProjectionMass.singleton_good_of_public_cover
#print axioms Paper2.ReferenceProjectionMass.pair_good_of_public_cover
#print axioms Paper2.ReferenceProjectionMass.dyadic_good_of_public_cover
