import CurrentAdditive.FullPrefixState
import CurrentAdditive.RareSuffixGoodTV
import CurrentAdditive.ProjectionMass
import Paper2.SourceProjection

/-! Appendix H `det:fullboost`: the zero-Bob prefix uses the actual
surviving column image and its full conditional mass. -/

namespace CurrentAdditive.FullBoost

open Paper2
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- If Bob sends no prefix message, conditional mass one of the surviving
columns is enough for a near-full original-coordinate projection. This
does not assert that the surviving set equals `Y` pointwise. -/
theorem zero_bob_suffix
    (μ : FiniteLaw X) (ν : FiniteLaw Z) (F : X → Z → Bool)
    (source : FiniteLaw S) {q : ℕ} (decode : S → Fin q → Z)
    (Good : Finset (Fin q)) (hGood : 1 ≤ Good.card)
    (Rows : Fin q → Set X) (Y K : Set S)
    (C : ℕ) (x δ ε : ℝ)
    (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hMass : 1 ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hrow : ∀ i ∈ Good, x ≤ μ.prob (· ∈ Rows i))
    (hεδ : ε ≤ δ)
    (hgoodOne : ∀ i ∈ Good, ∀ P : Z → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (decode s i)) /
        source.prob (· ∈ Y) - ν.prob P| ≤ ε)
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      x ≤ μ.prob (· ∈ A) → 1-δ ≤ ν.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B) :
    C ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1))
      (rowRectangle Good Rows) K := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < Good.card)
  let p : S → Z := fun s => decode s i
  let B : Set Z := p '' K
  have himage : (fun z => z ∈ B) =
      ProjectionMass.imageEvent p (· ∈ K) := by
    funext z
    apply propext
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hproj := ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
    source ν p (· ∈ Y) (· ∈ K) ε hY
    (fun s hs => hK hs) (hgoodOne i hi)
  have hB : 1-δ ≤ ν.prob (· ∈ B) := by
    rw [himage]
    linarith
  have hbase : C ≤ Compression.restrictionD F (Rows i) B :=
    hnear (Rows i) B (hrow i hi) hB
  have hpull : Compression.restrictionD F (Rows i) B ≤
      Compression.restrictionD
        (fun a s => F a.2 (decode s a.1))
        (rowRectangle Good Rows) K := by
    apply SourceProjection.restrictionD_projected_le
      (fun a s => F a.2 (decode s a.1)) F
      (fun u : X => (i,u)) p (rowRectangle Good Rows) K (Rows i)
    · intro u hu
      exact ⟨hi, hu⟩
    · intro u hu s hs
      rfl
  exact hbase.trans hpull

#print axioms zero_bob_suffix

/-- Full-strength amplification from the actual fixed-length arbitrary
speaker prefix. The zero-Bob branch uses near-full base restrictions;
every positive-Bob branch uses the checked common suffix obstruction. -/
theorem fullboost_of_good_tv
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (Rows : Fin q → Set X) (Y : Set S)
    (C a : ℕ) (x v δ ε : ℝ)
    (hC : 3 ≤ C) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hcount : (if a = 0 then 1 else 2^(a-1)+1) ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good,
      (2 : ℝ)^a * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y))
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      x ≤ μ.toFiniteLaw.prob (· ∈ A) →
      1-δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x
      ((C-1 : ℕ) : ℤ))
    (hεδ : ε ≤ δ)
    (hεpos : 0 < ε) (hεshort : ε ≤ 1/1000)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hgood : ∀ (n : ℕ) (_hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good) →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε)
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    C+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1))
      (rowRectangle Good Rows) Y := by
  let G : (Fin q × X) → S → Bool := fun a s => F a.2 (decode s a.1)
  let D := Compression.restrictionD G (rowRectangle Good Rows) Y
  by_contra hn
  change ¬ (C+a ≤ D) at hn
  have hD : D ≤ C+a-1 := by omega
  obtain ⟨A, B, Good', Rows', K, P', hab, hGoodOne, hGoodMany,
      hrow', hcond, hGoodsub, hRowsSub, hKsub, hcost, heval⟩ :=
    full_prefix_state μ.toFiniteLaw source G Good Rows Y C a x
      (by omega) hx hcount hrow (hv.trans_le hY) hD
  have hupper : Compression.restrictionD G
      (rowRectangle Good' Rows') K ≤ C-1 :=
    residual_restriction_upper G Good' Rows' K P' (C-1) hcost heval
  have hOutside' : ∀ i ∈ Good', i ∉ E := by
    intro i hi
    exact hOutside i (hGoodsub hi)
  have hgood' : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good') →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε := by
    intro n hn e he hmem P
    exact hgood n hn e he (fun j => hGoodsub (hmem j)) P
  by_cases hB0 : B = 0
  · have hrow0 : ∀ i ∈ Good', x ≤ μ.toFiniteLaw.prob (· ∈ Rows' i) := by
      intro i hi
      simpa [hB0] using hrow' i hi
    have hmass : 1 ≤ source.prob (· ∈ K) / source.prob (· ∈ Y) := by
      simpa [hB0] using hcond
    have hgoodOne : ∀ i ∈ Good', ∀ P : Z → Prop,
        |source.prob (fun s => s ∈ Y ∧ P (decode s i)) /
          source.prob (· ∈ Y) - ν.toFiniteLaw.prob P| ≤ ε := by
      intro i hi P
      let e1 : Fin 1 → Fin q := fun _ => i
      have he1 : Function.Injective e1 := by
        intro j k _
        exact Subsingleton.elim j k
      have hh := hgood' 1 (by omega) e1 he1 (fun _ => hi)
        (fun z => P (z 0))
      simpa only [e1, ReferenceProjectionMass.iid_one_coordinate_prob]
        using hh
    have hlow := zero_bob_suffix μ.toFiniteLaw ν.toFiniteLaw F
      source decode Good' hGoodOne Rows' Y K C x δ ε
      (hv.trans_le hY) hKsub hmass hrow0 hεδ hgoodOne hnear
    change C ≤ Compression.restrictionD G (rowRectangle Good' Rows') K at hlow
    omega
  · have hBpos : 1 ≤ B := by omega
    have hscaleB : (2 : ℝ)^B * x ≤ 1 := by
      have hpow : (2 : ℝ)^B ≤ (2 : ℝ)^a :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact (mul_le_mul_of_nonneg_right hpow hx.le).trans hscale
    have hlow := rare_suffix_all_good_tv μ ν F source decode hwise
      Good' E (hGoodMany hBpos) hOutside' Rows' Y K
      (C-1) x v ε (by omega) hx
      (by simpa only [show (B-1)+1 = B by omega] using hscaleB)
      hprofile
      (by
        intro i hi
        simpa only [show (B-1)+1 = B by omega] using hrow' i hi)
      hv hv1 hY hKsub
      (by simpa only [show (B-1)+1 = B by omega] using hcond)
      hεpos hεshort hεcap hgood' hTV
    change (C-1)+1 ≤ Compression.restrictionD G (rowRectangle Good' Rows') K at hlow
    omega

#print axioms fullboost_of_good_tv

end CurrentAdditive.FullBoost
