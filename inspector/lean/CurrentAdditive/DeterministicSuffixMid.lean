import CurrentAdditive.DeterministicSuffixSmall
import Paper2.AAvgProjectionJ
import Paper2.ProductProjections
import Paper2.ReferenceProjectionMass

/-! Private v27 Appendix H `det:suffix`, the intermediate short cases. -/

namespace CurrentAdditive.SuffixMid

open Paper2
open Workspace.Types.CommComplexity

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- Four explicitly disjoint pairs of the eight original coordinates. -/
def pairIndex (i : Fin 4) (j : Fin 2) : Fin 8 :=
  ⟨2 * i.val + j.val, by omega⟩

def pairBlock (i : Fin 4) : Finset (Fin 8) :=
  Finset.univ.image (pairIndex i)

private theorem pairIndex_injective (i : Fin 4) :
    Function.Injective (pairIndex i) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [pairIndex] at hv
  omega

private theorem pairBlock_injective : Function.Injective pairBlock := by
  intro i j hij
  have hmem : pairIndex i 0 ∈ pairBlock j := by
    rw [← hij]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
  apply Fin.ext
  have hv := congrArg Fin.val hk
  dsimp [pairIndex] at hv
  omega

private theorem pairBlock_disjoint :
    Pairwise (fun i j : Fin 4 => Disjoint (pairBlock i) (pairBlock j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro a hai haj
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hai
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp haj
  have hval := congrArg Fin.val (hu.trans hv.symm)
  dsimp [pairIndex] at hval
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  omega

/-- The four disjoint original-coordinate pairs cannot all have image mass
below `9/25` if the eight-coordinate event exceeds `(9/25)^4`. -/
theorem heavy_pair_of_eight (ν : FiniteLaw Z) (C : Set (Fin 8 → Z))
    (hC : (9 / 25 : ℝ) ^ 4 < (ν.iid 8).prob (· ∈ C)) :
    ∃ i : Fin 4, (9 / 25 : ℝ) < (ν.iid 2).prob
      (· ∈ (fun c j => c (pairIndex i j)) '' C) := by
  classical
  let mass : Fin 4 → ℝ := fun i =>
    ProductProjections.projectionMass (fun _ : Fin 8 => ν) (· ∈ C) (pairBlock i)
  have hprod : (ν.iid 8).prob (· ∈ C) ≤ ∏ i : Fin 4, mass i := by
    calc
      _ ≤ (ν.iid 8).prob (fun c => ∀ i : Fin 4,
            ProductProjections.projected (· ∈ C) (pairBlock i)
              (fun j => c j.val)) := by
        apply FiniteLaw.prob_mono
        intro c hc i
        exact ⟨c, hc, rfl⟩
      _ = ∏ i : Fin 4, mass i := by
        simpa only [mass, FiniteLaw.iid] using
          (ProductProjections.prob_disjoint_blocks
            (fun _ : Fin 8 => ν) pairBlock pairBlock_disjoint
            (fun i => ProductProjections.projected (· ∈ C) (pairBlock i)))
  have hex : ∃ i : Fin 4, (9 / 25 : ℝ) < mass i := by
    by_contra hn
    push Not at hn
    have hle : (∏ i : Fin 4, mass i) ≤ (9 / 25 : ℝ) ^ 4 := by
      calc
        _ ≤ ∏ _i : Fin 4, (9 / 25 : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _
            exact ProductProjections.projectionMass_nonneg
              (fun _ : Fin 8 => ν) (· ∈ C) (pairBlock i)
          · intro i _
            exact hn i
        _ = _ := by simp [div_pow]
    linarith
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  have heq := Paper2.ReferenceProjectionMass.projectionMass_eq_selectedColumns_of_injective
    ν C (pairBlock i) (pairIndex i) (pairIndex_injective i) rfl
  dsimp only [mass] at hi
  rw [heq] at hi
  simpa only [mass, Paper2.ReferenceCapacity.selectedColumns] using hi

private theorem nine_25_lt_tenth_rpow :
    (9 / 25 : ℝ) < (1 / 10 : ℝ) ^ ((2 : ℝ) / 5) := by
  have hx : (0 : ℝ) ≤ (9 / 25 : ℝ) ^ (5 : ℝ) := by positivity
  have hy : (0 : ℝ) ≤ (1 / 10 : ℝ) ^ (2 : ℝ) := by positivity
  have hpow : (9 / 25 : ℝ) ^ (5 : ℝ) < (1 / 10 : ℝ) ^ (2 : ℝ) := by
    norm_num [Real.rpow_natCast]
  have hroot := (Real.rpow_lt_rpow_iff hx hy (by norm_num : (0 : ℝ) < 1 / 5)).2 hpow
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9 / 25),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 10)] at hroot
  convert hroot using 1 <;> norm_num

/-- A concrete two-coordinate image of retained indexed source columns
inherits the two-copy lower bound. This theorem does not assume a desired
protocol lower bound. -/
theorem actual_pair_cost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) {q : ℕ} (decode : S → Fin q → Z)
    (e : Fin 2 → Fin q) (R : Set (Fin q × X)) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 2, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hmass : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c)) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  classical
  let SR : Set (Fin 2 × X) := {a | (e a.1, a.2) ∈ R}
  let C : Set (Fin 2 → Z) :=
    (fun s j => decode s (e j)) '' K
  have hr : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      2 * x ≤ μ.toFiniteLaw.prob (fun a => (j, a) ∈ SR.toFinset) := by
    intro j _
    simpa [SR] using hrow j
  have hQ : 2 ≤ (Finset.univ : Finset (Fin 2)).card := by simp
  have hc : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob (· ∈ C.toFinset) := by
    simpa only [C, Set.mem_image, Set.mem_toFinset, exists_prop] using hmass
  have hh := Paper2.RationalRowEstimates.small_capacity_two
    μ ν F d 2 hd hx hscale hprofile Finset.univ hQ
    SR.toFinset C.toFinset hr hc
  have heq : D (NPCC.subgame (Paper2.fullInterlace F 2)
      SR.toFinset C.toFinset) =
      Paper2.Compression.restrictionD (Paper2.fullInterlace F 2) SR C := by
    have hSR : {a | a ∈ SR.toFinset} = SR := by ext a; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hSR, ← hC]
    rfl
  rw [heq] at hh
  exact hh.trans (SuffixSmall.selected_projection_cost_le_indexed F decode e R K)

/-- The five-good-coordinate case `b=2`: mass `1/8 - ε > 1/10`
forces a two-coordinate image heavier than `9/25`, then a real
restriction of the original indexed matrix needs `d+1` bits. -/
theorem suffix_two
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z) (e : Fin 5 → Fin q)
    (_he : Function.Injective e)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x) (hscale : 8 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 5, 8 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1 / 8 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε < 1 / 40)
    (hgood : ∀ P : (Fin 5 → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid 5).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  classical
  let p : S → Fin 5 → Z := fun s j => decode s (e j)
  let C : Set (Fin 5 → Z) := p '' K
  have hmass : source.prob (· ∈ K) / source.prob (· ∈ Y) - ε ≤
      (ν.toFiniteLaw.iid 5).prob (· ∈ C) := by
    have h := ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
      source (ν.toFiniteLaw.iid 5) p (· ∈ Y) (· ∈ K) ε hY
      (fun _ hs => hK hs) (by simpa [p] using hgood)
    simpa only [C, p, ProjectionMass.imageEvent, Set.mem_image] using h
  have hten : (1 / 10 : ℝ) < (ν.toFiniteLaw.iid 5).prob (· ∈ C) := by
    linarith
  obtain ⟨J, hJ, hproj⟩ :=
    Paper2.AveragedProjection.rational_averaged_projection_mass ν 5 2
      (by omega) (by omega) C.toFinset
  let j : Fin 2 → Fin 5 := J.orderEmbOfFin hJ
  have hpair : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (fun c => ∃ s ∈ K, (fun i => decode s (e (j i))) = c) := by
    have hpow : (1 / 10 : ℝ) ^ ((2 : ℝ) / 5) <
        ((ν.toFiniteLaw.iid 5).prob (· ∈ C)) ^ ((2 : ℝ) / 5) :=
      Real.rpow_lt_rpow (by norm_num) hten (by norm_num)
    have hC : (ν.toFiniteLaw.iid 5).prob (· ∈ C.toFinset) =
        (ν.toFiniteLaw.iid 5).prob (· ∈ C) := by simp
    rw [hC] at hproj
    have himage : C.toFinset.image (fun c : Fin 5 → Z =>
        fun i : Fin 2 => c (J.orderEmbOfFin hJ i)) =
        {c : Fin 2 → Z | ∃ s ∈ K, (fun i => decode s (e (j i))) = c}.toFinset := by
      ext c
      simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨p s, ⟨s, hs, rfl⟩, rfl⟩
    have hp := le_trans (le_of_lt (nine_25_lt_tenth_rpow.trans hpow)) hproj
    simpa only [himage, Set.mem_toFinset] using hp
  apply actual_pair_cost μ ν F decode (fun i => e (j i)) R K d x hd hx
    (by linarith) hprofile
  · intro i
    have hi := hrow (j i)
    linarith
  · simpa only using hpair

/-- Shared eight-coordinate argument for the `b=3,4` cases. The source
gives stronger row thresholds, which the two wrappers below instantiate. -/
theorem suffix_eight
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z) (e : Fin 8 → Fin q)
    (_he : Function.Injective e)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 8, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1 / 32 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 1 / 100)
    (hgood : ∀ P : (Fin 8 → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid 8).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  classical
  let p : S → Fin 8 → Z := fun s j => decode s (e j)
  let C : Set (Fin 8 → Z) := p '' K
  have hmass : source.prob (· ∈ K) / source.prob (· ∈ Y) - ε ≤
      (ν.toFiniteLaw.iid 8).prob (· ∈ C) := by
    have h := ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
      source (ν.toFiniteLaw.iid 8) p (· ∈ Y) (· ∈ K) ε hY
      (fun _ hs => hK hs) (by simpa [p] using hgood)
    simpa only [C, p, ProjectionMass.imageEvent, Set.mem_image] using h
  have hlarge : (9 / 25 : ℝ) ^ 4 <
      (ν.toFiniteLaw.iid 8).prob (· ∈ C) := by
    norm_num at hcond hε ⊢
    linarith
  obtain ⟨i, hi⟩ := heavy_pair_of_eight ν.toFiniteLaw C hlarge
  have hpair : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (fun z => ∃ s ∈ K,
        (fun j => decode s (e (pairIndex i j))) = z) := by
    have himage : (fun c j => c (pairIndex i j)) '' C =
        {z : Fin 2 → Z | ∃ s ∈ K,
          (fun j => decode s (e (pairIndex i j))) = z} := by
      ext z
      constructor
      · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨p s, ⟨s, hs, rfl⟩, rfl⟩
    rw [himage] at hi
    exact hi.le
  apply actual_pair_cost μ ν F decode (fun j => e (pairIndex i j)) R K
    d x hd hx hscale hprofile
  · intro j
    exact hrow (pairIndex i j)
  · exact hpair

/-- Source case `b=3`: conditional retained mass at least `1/16` and
eight of at least nine good blocks with row mass `16x`. -/
theorem suffix_three
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z) (e : Fin 8 → Fin q)
    (he : Function.Injective e)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x) (hscale : 16 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 8, 16 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1 / 16 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 1 / 100)
    (hgood : ∀ P : (Fin 8 → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid 8).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  apply suffix_eight μ ν F source decode e he R Y K d x ε hd hx
    (by linarith) hprofile
    (by intro j; have hj := hrow j; linarith)
    hY hK (by linarith) hε hgood

/-- Source case `b=4`: conditional retained mass at least `1/32` and
eight of at least seventeen good blocks with row mass `32x`. -/
theorem suffix_four
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z) (e : Fin 8 → Fin q)
    (he : Function.Injective e)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x) (hscale : 32 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 8, 32 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1 / 32 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 1 / 100)
    (hgood : ∀ P : (Fin 8 → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid 8).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  apply suffix_eight μ ν F source decode e he R Y K d x ε hd hx
    (by linarith) hprofile
    (by intro j; have hj := hrow j; linarith)
    hY hK hcond hε hgood

#print axioms actual_pair_cost
#print axioms suffix_two
#print axioms heavy_pair_of_eight
#print axioms suffix_three
#print axioms suffix_four

end CurrentAdditive.SuffixMid
