import Mathlib
import Paper2.RankWitness

/-!
# Actual-row leaf constraints

Paper 2, frozen v12, Section 2, `thm:rank-count`, leaf-count part.
The coordinate-injection proof follows the checked construction in
`Workspace.LogRankBound.distinctCols_card_le_two_pow_rank`, transposed and
stated for all row values (so labelled duplicate inputs are allowed).
No linear combination is substituted for an input.
-/

namespace Paper2.RankLeaves

open Matrix

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def realMatrix (F : X → Y → Bool) : Matrix X Y ℝ :=
  fun x y => if F x y then 1 else 0

noncomputable def rowValues (F : X → Y → Bool) : Finset (Y → Bool) := by
  classical
  exact Finset.univ.image F

noncomputable def leafDomain (F : X → Y → Bool) (U : Finset X) (b : Bool) :
    Finset Y := by
  classical
  exact Finset.univ.filter fun y => ∀ x ∈ U, F x y = b

@[simp] theorem mem_leafDomain (F : X → Y → Bool) (U : Finset X) (b : Bool)
    (y : Y) : y ∈ leafDomain F U b ↔ ∀ x ∈ U, F x y = b := by
  classical
  simp [leafDomain]

theorem distinct_row_values_card_le (F : X → Y → Bool) :
    (rowValues F).card ≤ 2 ^ (realMatrix F).rank := by
  classical
  let A := realMatrix F
  obtain ⟨g, hgmem, hgspan, _hgli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range A.col)
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℝ
      ↥(Submodule.span ℝ (Set.range A.col))) → Y,
      ∀ i, g i = A.col (c i) := by
    have h : ∀ i, ∃ y, g i = A.col y := by
      intro i
      obtain ⟨y, hy⟩ := hgmem i
      exact ⟨y, hy.symm⟩
    exact Classical.axiomOfChoice h
  let project : ↥(rowValues F) →
      (Fin (Module.finrank ℝ ↥(Submodule.span ℝ (Set.range A.col))) → Bool) :=
    fun v i => v.val (c i)
  have hproject : Function.Injective project := by
    intro v w hp
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp v.property
    obtain ⟨z, _, hz⟩ := Finset.mem_image.mp w.property
    apply Subtype.ext
    rw [← hx, ← hz]
    funext y
    let φ : (X → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun q => q x - q z
        map_add' := by intros; simp; ring
        map_smul' := by intros; simp; ring }
    have hφ : Set.EqOn (⇑φ) (⇑(0 : (X → ℝ) →ₗ[ℝ] ℝ)) (Set.range g) := by
      rintro q ⟨i, rfl⟩
      have hi : F x (c i) = F z (c i) := by
        have hi := congrFun hp i
        change v.val (c i) = w.val (c i) at hi
        simpa [← hx, ← hz] using hi
      simp [φ, hc, Matrix.col, A, realMatrix, hi]
    have hmem : A.col y ∈ Submodule.span ℝ (Set.range g) := by
      rw [hgspan]
      exact Submodule.subset_span ⟨y, rfl⟩
    have he := LinearMap.eqOn_span hφ hmem
    change (if F x y then (1 : ℝ) else 0) -
      (if F z y then (1 : ℝ) else 0) = 0 at he
    cases hxy : F x y <;> cases hzy : F z y <;> simp_all
  have hcard := Fintype.card_le_of_injective project hproject
  simpa [Fintype.card_coe, Fintype.card_pi_const, Fintype.card_bool,
    ← Matrix.rank_eq_finrank_span_cols, A] using hcard

theorem exists_minimal_leaf_constraints (F : X → Y → Bool) (U : Finset X)
    (b : Bool) : ∃ V : Finset X,
    V ⊆ U ∧ leafDomain F V b = leafDomain F U b ∧
      ∀ x ∈ V, ∃ y : Y, F x y ≠ b ∧ ∀ z ∈ V, z ≠ x → F z y = b := by
  classical
  let candidates := U.powerset.filter fun V => leafDomain F V b = leafDomain F U b
  have hnonempty : candidates.Nonempty := by
    refine ⟨U, ?_⟩
    simp [candidates]
  obtain ⟨V, hV, hmin⟩ := candidates.exists_min_image Finset.card hnonempty
  have hVU : V ⊆ U := (Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1)
  refine ⟨V, hVU, (Finset.mem_filter.mp hV).2, ?_⟩
  intro x hx
  have hne : leafDomain F (V.erase x) b ≠ leafDomain F V b := by
    intro he
    have herase : V.erase x ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.erase_subset _ _) hVU), ?_⟩
      exact he.trans (Finset.mem_filter.mp hV).2
    have hle := hmin _ herase
    have hlt := Finset.card_erase_lt_of_mem hx
    omega
  have hsub : leafDomain F V b ⊆ leafDomain F (V.erase x) b := by
    intro y hy
    exact (mem_leafDomain F (V.erase x) b y).mpr fun z hz =>
      (mem_leafDomain F V b y).mp hy z (Finset.mem_of_mem_erase hz)
  obtain ⟨y, hy, hny⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩)
  have hrest : ∀ z ∈ V, z ≠ x → F z y = b := by
    intro z hz hzx
    exact (mem_leafDomain F (V.erase x) b y).mp hy z (Finset.mem_erase.mpr ⟨hzx, hz⟩)
  refine ⟨y, ?_, hrest⟩
  intro hxy
  apply hny
  apply (mem_leafDomain F V b y).mpr
  intro z hz
  by_cases hzx : z = x
  · simpa [hzx] using hxy
  · exact hrest z hz hzx

theorem exists_small_leaf_constraints (F : X → Y → Bool) (r : ℕ)
    (hr : 1 ≤ r) (hrank : (realMatrix F).rank ≤ r)
    (U : Finset X) (b : Bool) : ∃ V : Finset X,
    V ⊆ U ∧ V.card ≤ r ∧ leafDomain F V b = leafDomain F U b := by
  classical
  obtain ⟨V, hVU, hdom, hw⟩ := exists_minimal_leaf_constraints F U b
  refine ⟨V, hVU, ?_, hdom⟩
  obtain ⟨c, hc⟩ : ∃ c : ↥V → Y,
      ∀ i : ↥V, F i.val (c i) ≠ b ∧
        ∀ z ∈ V, z ≠ i.val → F z (c i) = b := by
    exact Classical.axiomOfChoice fun i : ↥V => hw i.val i.property
  cases b with
  | false =>
    have hd (i : ↥V) : realMatrix F i.val (c i) = 1 := by
      have hi := (hc i).1
      cases he : F i.val (c i) <;> simp_all [realMatrix]
    have ho (i j : ↥V) (hne : i ≠ j) : realMatrix F i.val (c j) = 0 := by
      have he := (hc j).2 i.val i.property (fun h => hne (Subtype.ext h))
      simp [realMatrix, he]
    have h := card_le_rank_of_zero_witness (realMatrix F) Subtype.val c hd ho
    exact (by simpa using h : V.card ≤ (realMatrix F).rank).trans hrank
  | true =>
    by_cases hcard : V.card = 1
    · omega
    have hd (i : ↥V) : realMatrix F i.val (c i) = 0 := by
      have hi := (hc i).1
      cases he : F i.val (c i) <;> simp_all [realMatrix]
    have ho (i j : ↥V) (hne : i ≠ j) : realMatrix F i.val (c j) = 1 := by
      have he := (hc j).2 i.val i.property (fun h => hne (Subtype.ext h))
      simp [realMatrix, he]
    have h := card_le_rank_of_one_witness (realMatrix F) Subtype.val c
      (by simpa using hcard) hd ho
    exact (by simpa using h : V.card ≤ (realMatrix F).rank).trans hrank

/-- A code lists at most `r` actual row values, with blanks allowed. -/
noncomputable def codeDomain (F : X → Y → Bool) (r : ℕ)
    (code : Bool × (Fin r → Option ↥(rowValues F))) : Finset Y := by
  classical
  exact Finset.univ.filter fun y => ∀ i v, code.2 i = some v → v.val y = code.1

theorem small_leaf_has_code (F : X → Y → Bool) (r : ℕ) (V : Finset X)
    (hcard : V.card ≤ r) (b : Bool) :
    ∃ code : Bool × (Fin r → Option ↥(rowValues F)),
      codeDomain F r code = leafDomain F V b := by
  classical
  let code : Fin r → Option ↥(rowValues F) := fun i =>
    if hi : i.val < V.card then
      some ⟨F (V.equivFin.symm ⟨i.val, hi⟩),
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
    else none
  refine ⟨(b, code), ?_⟩
  ext y
  simp only [codeDomain, Finset.mem_filter, Finset.mem_univ, true_and, mem_leafDomain]
  constructor
  · intro h x hx
    let i : Fin r := ⟨(V.equivFin ⟨x, hx⟩).val,
      lt_of_lt_of_le (V.equivFin ⟨x, hx⟩).isLt hcard⟩
    have hi : i.val < V.card := (V.equivFin ⟨x, hx⟩).isLt
    have hc : code i = some ⟨F x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩ := by
      dsimp [code]
      rw [dif_pos hi]
      apply congrArg some
      apply Subtype.ext
      change F (V.equivFin.symm (V.equivFin ⟨x, hx⟩)).val = F x
      simp
    exact h i _ hc
  · intro h i v hv
    dsimp [code] at hv
    split_ifs at hv with hi
    · cases hv
      exact h _ (V.equivFin.symm ⟨i.val, hi⟩).property

noncomputable def leafDomains (F : X → Y → Bool) : Finset (Finset Y) := by
  classical
  exact Finset.univ.image fun p : Finset X × Bool => leafDomain F p.1 p.2

theorem leafDomains_card_le_of_pos (F : X → Y → Bool) (r : ℕ)
    (hr : 1 ≤ r) (hrank : (realMatrix F).rank ≤ r) :
    (leafDomains F).card ≤ 2 ^ (r * (r + 1) + 1) := by
  classical
  let codes : Finset (Finset Y) := Finset.univ.image (codeDomain F r)
  have hsub : leafDomains F ⊆ codes := by
    intro S hS
    obtain ⟨⟨U, b⟩, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨V, _, hcard, hdom⟩ := exists_small_leaf_constraints F r hr hrank U b
    obtain ⟨code, hc⟩ := small_leaf_has_code F r V hcard b
    exact Finset.mem_image.mpr ⟨code, Finset.mem_univ _, hc.trans hdom⟩
  have hrows : (rowValues F).card ≤ 2 ^ r :=
    (distinct_row_values_card_le F).trans (Nat.pow_le_pow_right (by omega) hrank)
  have hbase : (rowValues F).card + 1 ≤ 2 ^ (r + 1) := by
    have hpos : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
    rw [pow_succ]
    omega
  calc
    (leafDomains F).card ≤ codes.card := Finset.card_le_card hsub
    _ ≤ Fintype.card (Bool × (Fin r → Option ↥(rowValues F))) :=
      (Finset.card_image_le).trans (by simp)
    _ = 2 * ((rowValues F).card + 1) ^ r := by simp
    _ ≤ 2 * (2 ^ (r + 1)) ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase r)
    _ = 2 ^ (r * (r + 1) + 1) := by rw [← pow_mul]; ring

omit [Fintype X] in
theorem eq_false_of_rank_zero (F : X → Y → Bool)
    (hrank : (realMatrix F).rank = 0) (x : X) (y : Y) : F x y = false := by
  by_contra h
  have he : realMatrix F x y = 1 := by
    cases hf : F x y <;> simp_all [realMatrix]
  have hbound := card_le_rank_of_zero_witness (realMatrix F)
    (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) (fun _ => he)
    (by intro i j hne; exact False.elim (hne (Subsingleton.elim i j)))
  simp [hrank] at hbound

theorem leafDomains_card_le_zero (F : X → Y → Bool)
    (hrank : (realMatrix F).rank = 0) : (leafDomains F).card ≤ 2 := by
  classical
  have hsub : leafDomains F ⊆ ({Finset.univ, ∅} : Finset (Finset Y)) := by
    intro S hS
    obtain ⟨⟨U, b⟩, _, rfl⟩ := Finset.mem_image.mp hS
    cases b with
    | false =>
      have heq : leafDomain F U false = Finset.univ := by
        ext y
        simp [eq_false_of_rank_zero F hrank]
      simp [heq]
    | true =>
      by_cases hU : U = ∅
      · simp [hU, leafDomain]
      · have heq : leafDomain F U true = ∅ := by
          ext y
          obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hU
          simp only [mem_leafDomain, Finset.notMem_empty, iff_false]
          intro hy
          have := hy x hx
          simp [eq_false_of_rank_zero F hrank] at this
        simp [heq]
  calc
    (leafDomains F).card ≤ ({Finset.univ, ∅} : Finset (Finset Y)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- The exact leaf-alphabet bound used in Paper 2's rank-sensitive count.
All row restrictions and both leaf output bits are counted together. -/
theorem leafDomains_card_le (F : X → Y → Bool) (r : ℕ)
    (hrank : (realMatrix F).rank ≤ r) :
    (leafDomains F).card ≤ 2 ^ (r * (r + 1) + 1) := by
  by_cases hr : r = 0
  · subst r
    simpa using leafDomains_card_le_zero F (Nat.eq_zero_of_le_zero hrank)
  · exact leafDomains_card_le_of_pos F r (Nat.one_le_iff_ne_zero.mpr hr) hrank

#print axioms distinct_row_values_card_le
#print axioms exists_small_leaf_constraints
#print axioms leafDomains_card_le

end Paper2.RankLeaves
