import CurrentAdditive.RareSuffixShort

/-! Private `det:exact` short-source bridge. The selected exact marginal is
stated as a probability identity, not as a desired communication bound. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2
open Workspace.Types.CommComplexity

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

private def exactSelectGood {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) : Fin n → Fin q :=
  fun j => Good.orderEmbOfFin rfl (Fin.castLE h j)

private theorem exactSelectGood_injective {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) : Function.Injective (exactSelectGood Good h) := by
  exact (Good.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective h)

private theorem exactSelectGood_mem {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) (j : Fin n) : exactSelectGood Good h j ∈ Good :=
  Good.orderEmbOfFin_mem rfl (Fin.castLE h j)

private theorem image_mass_ge_source_mass (source : FiniteLaw S)
    (ν : FiniteLaw Z) {q n : ℕ} (decode : S → Fin q → Z)
    (e : Fin n → Fin q) (K : Set S)
    (hsource : ∀ P : (Fin n → Z) → Prop,
      source.prob (fun s => P (fun j => decode s (e j))) =
        (ν.iid n).prob P) :
    source.prob (· ∈ K) ≤ (ν.iid n).prob
      (fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c) := by
  let P : (Fin n → Z) → Prop :=
    fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c
  have hm : source.prob (· ∈ K) ≤ source.prob (fun s => P (fun j => decode s (e j))) := by
    apply source.prob_mono
    intro s hs
    exact ⟨s, hs, rfl⟩
  exact hm.trans (by rw [hsource P])

/-- Exact source, two retained blocks, original column mass `9/25`. -/
theorem exact_suffix_zero
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 2 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : 2*x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, 2*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ) ≤ source.prob (· ∈ K))
    (hsource : ∀ (e : Fin 2 → Fin q), Function.Injective e →
      ∀ P : (Fin 2 → Z) → Prop,
      source.prob (fun s => P (fun j => decode s (e j))) =
        (ν.toFiniteLaw.iid 2).prob P) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  let e : Fin 2 → Fin q := exactSelectGood Good hGood
  apply SuffixMid.actual_pair_cost μ ν F decode e
    (rowRectangle Good Rows) K d x hd hx hscale hprofile
  · intro j
    rw [rowRectangle_fiber Good Rows _ (exactSelectGood_mem Good hGood j)]
    exact hrow (e j) (exactSelectGood_mem Good hGood j)
  · exact hK.trans (image_mass_ge_source_mass source ν.toFiniteLaw decode
      e K (hsource e (exactSelectGood_injective Good hGood)))

/-- Exact source, three retained blocks, original column mass `9/50`.
The second rung of the checked row ladder gives the extra suffix bit. -/
theorem exact_suffix_one
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 3 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : 4*x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, 4*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/50 : ℝ) ≤ source.prob (· ∈ K))
    (hsource : ∀ (e : Fin 3 → Fin q), Function.Injective e →
      ∀ P : (Fin 3 → Z) → Prop,
      source.prob (fun s => P (fun j => decode s (e j))) =
        (ν.toFiniteLaw.iid 3).prob P) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  classical
  let e : Fin 3 → Fin q := exactSelectGood Good hGood
  let SR : Set (Fin 3 × X) := {a | (e a.1, a.2) ∈ rowRectangle Good Rows}
  let C : Set (Fin 3 → Z) := (fun s j => decode s (e j)) '' K
  have hmass : (9/50 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob (· ∈ C) := by
    have hm := image_mass_ge_source_mass source ν.toFiniteLaw decode
      e K (hsource e (exactSelectGood_injective Good hGood))
    simpa only [C, Set.mem_image, exists_prop] using hK.trans hm
  have hr : ∀ j : Fin 3, (2 : ℝ)^2 * x ≤
      μ.toFiniteLaw.prob (fun a => (j,a) ∈ SR.toFinset) := by
    intro j
    have hh := hrow (e j) (exactSelectGood_mem Good hGood j)
    have heq : μ.toFiniteLaw.prob (fun a => (j,a) ∈ SR.toFinset) =
        μ.toFiniteLaw.prob (· ∈ Rows (e j)) := by
      simpa [SR] using rowRectangle_fiber Good Rows (e j)
        (exactSelectGood_mem Good hGood j) μ.toFiniteLaw
    rw [heq]
    norm_num
    exact hh
  have h₀ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x
      (3/5) (d : ℤ) := by simpa using hprofile (0 : Fin 3)
  have h₁ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x
      ((3/5)/2) ((d : ℤ)-1) := by
    simpa [show (3/5 : ℝ)*(1/2)^(1 : ℕ) = (3/5)/2 by norm_num]
      using hprofile (1 : Fin 3)
  have h₂ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x
      ((3/5)/4) ((d : ℤ)-2) := by
    convert hprofile (2 : Fin 3) using 1
    norm_num
  have hcol : ((3/5 : ℝ)^2 / (2 : ℝ)^(1 : ℕ)) ≤
      (ν.toFiniteLaw.iid 3).prob (· ∈ C.toFinset) := by
    convert hmass using 1 <;> norm_num
  have hh := Paper2.RationalRowEstimates.row_ladder μ ν F d 2 x (3/5)
    hd (by omega) hx (by norm_num) (by norm_num)
    (by norm_num; exact hscale) h₀ h₁ h₂ (1 : Fin 3)
    SR.toFinset C.toFinset hr (by simpa using hcol)
  have heq : D (NPCC.subgame (Paper2.fullInterlace F 3)
      SR.toFinset C.toFinset) =
      Paper2.Compression.restrictionD (Paper2.fullInterlace F 3) SR C := by
    have hSR : {a | a ∈ SR.toFinset} = SR := by ext a; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hSR, ← hC]
    rfl
  have hh' : d+2 ≤ 1 + D (NPCC.subgame (Paper2.fullInterlace F 3)
      SR.toFinset C.toFinset) := by simpa using hh
  rw [heq] at hh'
  have hlower : d+1 ≤ Paper2.Compression.restrictionD
      (Paper2.fullInterlace F 3) SR C := by omega
  exact hlower.trans (SuffixSmall.selected_projection_cost_le_indexed
    F decode e (rowRectangle Good Rows) K)

private theorem nine_25_lt_nine_100_rpow :
    (9/25 : ℝ) < (9/100 : ℝ)^((2 : ℝ)/5) := by
  have hx : (0 : ℝ) ≤ (9/25 : ℝ)^(5 : ℝ) := by positivity
  have hy : (0 : ℝ) ≤ (9/100 : ℝ)^(2 : ℝ) := by positivity
  have hpow : (9/25 : ℝ)^(5 : ℝ) < (9/100 : ℝ)^(2 : ℝ) := by
    norm_num [Real.rpow_natCast]
  have hroot := (Real.rpow_lt_rpow_iff hx hy
    (by norm_num : (0 : ℝ) < 1/5)).2 hpow
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9/25),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9/100)] at hroot
  convert hroot using 1 <;> norm_num

/-- Exact five-coordinate suffix, with original column mass `9/100`.
The averaged projection finds a heavy pair among five true coordinates. -/
theorem exact_suffix_two
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 5 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : 8*x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, 8*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/100 : ℝ) ≤ source.prob (· ∈ K))
    (hsource : ∀ (e : Fin 5 → Fin q), Function.Injective e →
      ∀ P : (Fin 5 → Z) → Prop,
      source.prob (fun s => P (fun j => decode s (e j))) =
        (ν.toFiniteLaw.iid 5).prob P) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  classical
  let e : Fin 5 → Fin q := exactSelectGood Good hGood
  let C : Set (Fin 5 → Z) := (fun s j => decode s (e j)) '' K
  have hmass : (9/100 : ℝ) ≤ (ν.toFiniteLaw.iid 5).prob (· ∈ C) := by
    have hm := image_mass_ge_source_mass source ν.toFiniteLaw decode
      e K (hsource e (exactSelectGood_injective Good hGood))
    simpa only [C, Set.mem_image, exists_prop] using hK.trans hm
  obtain ⟨J, hJ, hproj⟩ :=
    Paper2.AveragedProjection.rational_averaged_projection_mass ν 5 2
      (by omega) (by omega) C.toFinset
  let j : Fin 2 → Fin 5 := J.orderEmbOfFin hJ
  have hpair : (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (fun c => ∃ s ∈ K, (fun i => decode s (e (j i))) = c) := by
    have hpow : (9/100 : ℝ)^((2 : ℝ)/5) ≤
        ((ν.toFiniteLaw.iid 5).prob (· ∈ C))^((2 : ℝ)/5) :=
      Real.rpow_le_rpow (by norm_num) hmass (by norm_num)
    have hC : (ν.toFiniteLaw.iid 5).prob (· ∈ C.toFinset) =
        (ν.toFiniteLaw.iid 5).prob (· ∈ C) := by simp
    rw [hC] at hproj
    have himage : C.toFinset.image (fun c : Fin 5 → Z =>
        fun i : Fin 2 => c (J.orderEmbOfFin hJ i)) =
        {c : Fin 2 → Z | ∃ s ∈ K,
          (fun i => decode s (e (j i))) = c}.toFinset := by
      ext c
      simp only [Finset.mem_image, Set.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨fun i => decode s (e i), ⟨s, hs, rfl⟩, rfl⟩
    have hp := (nine_25_lt_nine_100_rpow.trans_le hpow).le.trans hproj
    simpa only [himage, Set.mem_toFinset] using hp
  apply SuffixMid.actual_pair_cost μ ν F decode (fun i => e (j i))
    (rowRectangle Good Rows) K d x hd hx (by linarith) hprofile
  · intro i
    rw [rowRectangle_fiber Good Rows _ (exactSelectGood_mem Good hGood (j i))]
    have hi := hrow (e (j i)) (exactSelectGood_mem Good hGood (j i))
    linarith
  · exact hpair

/-- Exact eight-coordinate suffix, with original column mass `9/200`.
Four disjoint pair projections cannot all be lighter than `9/25`. -/
theorem exact_suffix_three
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 8 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : 16*x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, 16*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/200 : ℝ) ≤ source.prob (· ∈ K))
    (hsource : ∀ (e : Fin 8 → Fin q), Function.Injective e →
      ∀ P : (Fin 8 → Z) → Prop,
      source.prob (fun s => P (fun j => decode s (e j))) =
        (ν.toFiniteLaw.iid 8).prob P) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  classical
  let e : Fin 8 → Fin q := exactSelectGood Good hGood
  let C : Set (Fin 8 → Z) := (fun s j => decode s (e j)) '' K
  have hmass : (9/200 : ℝ) ≤ (ν.toFiniteLaw.iid 8).prob (· ∈ C) := by
    have hm := image_mass_ge_source_mass source ν.toFiniteLaw decode
      e K (hsource e (exactSelectGood_injective Good hGood))
    simpa only [C, Set.mem_image, exists_prop] using hK.trans hm
  have hlarge : (9/25 : ℝ)^4 < (ν.toFiniteLaw.iid 8).prob (· ∈ C) := by
    have hnum : (9/25 : ℝ)^4 < 9/200 := by norm_num
    exact hnum.trans_le hmass
  obtain ⟨i, hi⟩ := SuffixMid.heavy_pair_of_eight ν.toFiniteLaw C hlarge
  have hpair : (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (fun z => ∃ s ∈ K,
        (fun j => decode s (e (SuffixMid.pairIndex i j))) = z) := by
    have himage : (fun c j => c (SuffixMid.pairIndex i j)) '' C =
        {z : Fin 2 → Z | ∃ s ∈ K,
          (fun j => decode s (e (SuffixMid.pairIndex i j))) = z} := by
      ext z
      constructor
      · rintro ⟨c, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨fun j => decode s (e j), ⟨s, hs, rfl⟩, rfl⟩
    rw [himage] at hi
    exact hi.le
  apply SuffixMid.actual_pair_cost μ ν F decode
    (fun j => e (SuffixMid.pairIndex i j))
    (rowRectangle Good Rows) K d x hd hx (by linarith) hprofile
  · intro j
    rw [rowRectangle_fiber Good Rows _
      (exactSelectGood_mem Good hGood (SuffixMid.pairIndex i j))]
    have hj := hrow (e (SuffixMid.pairIndex i j))
      (exactSelectGood_mem Good hGood (SuffixMid.pairIndex i j))
    linarith
  · exact hpair

#print axioms CurrentAdditive.ArbitraryPrefix.exact_suffix_zero
#print axioms CurrentAdditive.ArbitraryPrefix.exact_suffix_one
#print axioms CurrentAdditive.ArbitraryPrefix.exact_suffix_two
#print axioms CurrentAdditive.ArbitraryPrefix.exact_suffix_three

end CurrentAdditive.ArbitraryPrefix
