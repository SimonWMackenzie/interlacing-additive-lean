import CurrentAdditive.V38RareProjectedMass
import CurrentAdditive.V38IndexedTwoHigh
import CurrentAdditive.V38ThreeMiddle
import CurrentAdditive.PrefixSuffixGlue
import CurrentAdditive.DeterministicSuffixMid

/-! v39 `det:suffix`, all five short cases. The only base profile has two
thresholds. A single projection lemma also supplies the short `det:exact`
cases, always on the actual indexed retained matrix. -/

namespace V38RareBoost

open Paper2 CurrentAdditive CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

private def shortSelect {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) : Fin n → Fin q :=
  fun j => Good.orderEmbOfFin rfl (Fin.castLE h j)

private theorem shortSelect_injective {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) : Function.Injective (shortSelect Good h) := by
  exact (Good.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective h)

private theorem shortSelect_mem {q n : ℕ} (Good : Finset (Fin q))
    (h : n ≤ Good.card) (j : Fin n) : shortSelect Good h j ∈ Good :=
  Good.orderEmbOfFin_mem rfl (Fin.castLE h j)

theorem indexed_three_block_middle
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) {q : ℕ} (decode : S → Fin q → Z)
    (e : Fin 3 → Fin q) (R : Set (Fin q × X)) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 3, 4*x ≤ μ.prob (fun a => (e j,a) ∈ R))
    (hmass : (9/50 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob
      (fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c)) :
    d+1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  have hfull := Paper2.V38SmallBlocks.three_block_middle F μ ν x d hd hx hprofile
    {a | (e a.1,a.2) ∈ R} ((fun s j => decode s (e j)) '' K) hrow
    (by simpa only [Set.mem_image] using hmass)
  exact hfull.trans
    (SuffixSmall.selected_projection_cost_le_indexed F decode e R K)

/-- The common small-coordinate argument. The hypothesis here is only a
lower bound on actual product projection mass, not a communication claim. -/
theorem short_suffix_of_projected_mass
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) {q b : ℕ} (hb : b ≤ 4)
    (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 2^b+1 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S) (d : ℕ) (x : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.prob (· ∈ Rows i))
    (hproj : ∀ {n : ℕ}, n ≤ 8 → (e : Fin n → Fin q) →
      Function.Injective e → (∀ i, e i ∈ Good) →
      (9/25 : ℝ)/(2 : ℝ)^b ≤ (ν.toFiniteLaw.iid n).prob
        (fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c)) :
    d+1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  classical
  have hrow2 : ∀ i ∈ Good, 2*x ≤ μ.prob (· ∈ Rows i) := by
    intro i hi
    have hp : (2 : ℝ) ≤ (2 : ℝ)^(b+1) := by
      calc
        (2 : ℝ) = (2 : ℝ)^1 := by norm_num
        _ ≤ (2 : ℝ)^(b+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans (hrow i hi)
  by_cases hb0 : b = 0
  · subst b
    have hc : 2 ≤ Good.card := by simpa using hGood
    let e : Fin 2 → Fin q := shortSelect Good hc
    apply indexed_two_block_high μ ν.toFiniteLaw F decode e
      (rowRectangle Good Rows) K d x hd hx hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (shortSelect_mem Good hc j) μ]
      exact hrow2 _ (shortSelect_mem Good hc j)
    · simpa using hproj (by omega) e (shortSelect_injective Good hc)
        (shortSelect_mem Good hc)
  by_cases hb1 : b = 1
  · subst b
    have hc : 3 ≤ Good.card := by simpa using hGood
    let e : Fin 3 → Fin q := shortSelect Good hc
    apply indexed_three_block_middle μ ν F decode e
      (rowRectangle Good Rows) K d x hd hx hprofile
    · intro j
      rw [rowRectangle_fiber Good Rows _ (shortSelect_mem Good hc j) μ]
      convert hrow _ (shortSelect_mem Good hc j) using 1 <;> norm_num
    · convert hproj (by omega) e (shortSelect_injective Good hc)
        (shortSelect_mem Good hc) using 1 <;> norm_num
  by_cases hb2 : b = 2
  · subst b
    have hc : 5 ≤ Good.card := by simpa using hGood
    let e : Fin 5 → Fin q := shortSelect Good hc
    let C : Set (Fin 5 → Z) := (fun s j => decode s (e j)) '' K
    have hmass : (9/100 : ℝ) ≤ (ν.toFiniteLaw.iid 5).prob (· ∈ C) := by
      have hm := hproj (by omega : 5 ≤ 8) e
        (shortSelect_injective Good hc) (shortSelect_mem Good hc)
      norm_num at hm
      simpa only [C, Set.mem_image] using hm
    obtain ⟨J, hJ, hproject⟩ := Paper2.V38SmallBlocks.rational_projected_mass ν
      5 2 (by omega) (by omega) C
    let j : Fin 2 → Fin 5 := J.orderEmbOfFin hJ
    have hpair : (9/25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
        (· ∈ (fun c : Fin 5 → Z => fun i : Fin 2 => c (j i)) '' C) := by
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 9/100)
        hmass (by norm_num : (0 : ℝ) ≤ (2 : ℝ)/5)
      exact (Paper2.V38SmallBlocks.five_pair_numeric.trans hpow).trans hproject
    have himage : (fun c : Fin 5 → Z => fun i : Fin 2 => c (j i)) '' C =
        {c : Fin 2 → Z | ∃ s ∈ K, (fun i => decode s (e (j i))) = c} := by
      ext c
      constructor
      · rintro ⟨a, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨fun i => decode s (e i), ⟨s, hs, rfl⟩, rfl⟩
    apply indexed_two_block_high μ ν.toFiniteLaw F decode (fun i => e (j i))
      (rowRectangle Good Rows) K d x hd hx hprofile
    · intro i
      rw [rowRectangle_fiber Good Rows _ (shortSelect_mem Good hc (j i)) μ]
      exact hrow2 _ (shortSelect_mem Good hc (j i))
    · simpa only [himage, Set.mem_setOf_eq] using hpair
  have hb34 : b = 3 ∨ b = 4 := by omega
  have hc : 8 ≤ Good.card := by rcases hb34 with rfl | rfl <;> norm_num at hGood <;> omega
  let e : Fin 8 → Fin q := shortSelect Good hc
  let C : Set (Fin 8 → Z) := (fun s j => decode s (e j)) '' K
  have hmass0 := hproj (by omega : 8 ≤ 8) e
    (shortSelect_injective Good hc) (shortSelect_mem Good hc)
  have hmass : (9/400 : ℝ) ≤ (ν.toFiniteLaw.iid 8).prob (· ∈ C) := by
    rcases hb34 with rfl | rfl <;> norm_num at hmass0 <;>
      simpa only [C, Set.mem_image] using (show (9/400 : ℝ) ≤
        (ν.toFiniteLaw.iid 8).prob
          (fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c) by linarith)
  have hlarge : (9/25 : ℝ)^4 < (ν.toFiniteLaw.iid 8).prob (· ∈ C) := by
    have hnum : (9/25 : ℝ)^4 < 9/400 := by norm_num
    exact hnum.trans_le hmass
  obtain ⟨i, hi⟩ := SuffixMid.heavy_pair_of_eight ν.toFiniteLaw C hlarge
  have himage : (fun c j => c (SuffixMid.pairIndex i j)) '' C =
      {c : Fin 2 → Z | ∃ s ∈ K,
        (fun j => decode s (e (SuffixMid.pairIndex i j))) = c} := by
    ext c
    constructor
    · rintro ⟨a, ⟨s, hs, rfl⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨fun j => decode s (e j), ⟨s, hs, rfl⟩, rfl⟩
  apply indexed_two_block_high μ ν.toFiniteLaw F decode
    (fun j => e (SuffixMid.pairIndex i j))
    (rowRectangle Good Rows) K d x hd hx hprofile
  · intro j
    rw [rowRectangle_fiber Good Rows _ (shortSelect_mem Good hc (SuffixMid.pairIndex i j)) μ]
    exact hrow2 _ (shortSelect_mem Good hc (SuffixMid.pairIndex i j))
  · simpa only [himage, Set.mem_setOf_eq] using hi.le

theorem short_epsilon (v τ : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    V38Moments.epsilon v τ ≤ 1/1000 := by
  have hp : v^((1 : ℝ)/256) ≤ 1 :=
    Real.rpow_le_one hv.le hv1 (by norm_num)
  unfold V38Moments.epsilon
  calc
    _ ≤ (2 : ℝ)^(-30 : ℤ)*v^((1 : ℝ)/256) := min_le_right _ _
    _ ≤ (2 : ℝ)^(-30 : ℤ) := by
      simpa using mul_le_mul_of_nonneg_left hp
        (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(-30 : ℤ))
    _ ≤ 1/1000 := by norm_num

theorem rare_suffix_short_fixed_E
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (hb : b ≤ 4) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q))
    (hGood : 2^b+1 ≤ Good.card) (hOutside : ∀ i ∈ Good, i ∉ E)
    (Rows : Fin q → Set X) (Y K : Set S)
    (d : ℕ) (x v τ : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1/(2 : ℝ)^(b+1) ≤ source.prob (· ∈ K)/source.prob (· ∈ Y))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ V38Moments.epsilon v τ) :
    d+1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  apply short_suffix_of_projected_mass μ ν F hb decode Good hGood Rows K d x
    hd hx hprofile hrow
  intro n hn e he hmem
  have hm := good_projected_mass source ν.toFiniteLaw decode Y K
    (hv.trans_le hY) hK E Good hOutside (V38Moments.epsilon v τ)
    hTV hn e he hmem
  have hε := short_epsilon v τ hv hv1
  have harith : (9/25 : ℝ)/(2 : ℝ)^b ≤ 1/(2 : ℝ)^(b+1)-1/1000 := by
    interval_cases b <;> norm_num
  exact harith.trans (by simpa only [Set.mem_image] using
    (show 1/(2 : ℝ)^(b+1)-1/1000 ≤ (ν.toFiniteLaw.iid n).prob
      (· ∈ (fun s j => decode s (e j)) '' K) by linarith))

theorem short_exact_selected
    (source : FiniteLaw S) (ν : FiniteLaw Z) {q n : ℕ}
    (decode : S → Fin q → Z) (hwise : IsDWise 8 source decode ν)
    (hn : n ≤ 8) (e : Fin n → Fin q) (he : Function.Injective e)
    (P : (Fin n → Z) → Prop) :
    source.prob (fun s => P (fun j => decode s (e j))) = (ν.iid n).prob P := by
  classical
  let J : Finset (Fin q) := Finset.univ.image e
  have hJcard : J.card ≤ 8 :=
    Finset.card_image_le.trans (by simpa [J] using hn)
  have hmem (j : Fin n) : e j ∈ J :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let E : (J → Z) → Prop := fun z => P (fun j => z ⟨e j,hmem j⟩)
  have hs := hwise J hJcard E
  have hr := FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν)
    (fun j : J => j.val) Subtype.val_injective E
  have hs' : source.prob (fun s => P (fun j => decode s (e j))) =
      (ν.iid q).prob (fun c => P (fun j => c (e j))) := by
    calc
      _ = source.prob (fun s => E (fun j : J => decode s j.val)) := rfl
      _ = (FiniteLaw.pi (fun _ : J => ν)).prob E := hs
      _ = _ := by simpa only [FiniteLaw.iid,E] using hr.symm
  exact hs'.trans (by simpa only [FiniteLaw.iid] using
    FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν) e he P)

/-- Exact-source short continuation with precisely the two current rungs. -/
theorem exact_suffix_short_two_threshold
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (hb : b ≤ 4) (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Good : Finset (Fin q)) (hGood : 2^b+1 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S) (d : ℕ) (x : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ)/(2 : ℝ)^b ≤ source.prob (· ∈ K)) :
    d+1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  apply short_suffix_of_projected_mass μ ν F hb decode Good hGood Rows K d x
    hd hx hprofile hrow
  intro n hn e he _
  let P : (Fin n → Z) → Prop :=
    fun c => ∃ s ∈ K, (fun j => decode s (e j)) = c
  have hm : source.prob (· ∈ K) ≤ source.prob
      (fun s => P (fun j => decode s (e j))) := by
    apply source.prob_mono
    intro s hs
    exact ⟨s,hs,rfl⟩
  exact hK.trans (hm.trans (by
    rw [short_exact_selected source ν.toFiniteLaw decode hwise hn e he P]))

#print axioms indexed_three_block_middle
#print axioms short_suffix_of_projected_mass
#print axioms rare_suffix_short_fixed_E
#print axioms exact_suffix_short_two_threshold

end V38RareBoost
