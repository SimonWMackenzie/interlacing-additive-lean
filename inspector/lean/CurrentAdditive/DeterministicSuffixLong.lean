import CurrentAdditive.DeterministicSuffixMid
import CurrentAdditive.FourthMoment

/-! Private Appendix H `det:suffix` long-prefix packet. This file keeps
the conditional fourth- and high-moment inputs explicit until their
separate kernel-checked source theorems are available. -/

namespace CurrentAdditive.SuffixLong

open Paper2
open Workspace.Types.CommComplexity

/-- For the paper's fixed moment order `R=1024`, the range where the
conditional fourth moment is strong enough reaches the range where the
unconditioned high moment takes over. -/
theorem moment_ranges_overlap_1024 (v ε : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hε : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ) ^ (-20 : ℤ) / 1024 * v ^ ((1 : ℝ) / 256)) :
    16 * 1024 * v ^ (-(1 / 511 : ℝ)) ≤ 1 / (128 * ε) := by
  have hw : 1 ≤ v⁻¹ := (one_le_inv₀ hv).2 hv1
  have hexp : (1 / 511 : ℝ) ≤ 1 / 256 := by norm_num
  have hmono : v ^ (-(1 / 511 : ℝ)) ≤ v ^ (-(1 / 256 : ℝ)) := by
    simpa only [Real.rpow_neg_eq_inv_rpow] using
      (Real.rpow_le_rpow_of_exponent_le hw hexp)
  have ht : 0 < v ^ ((1 : ℝ) / 256) := Real.rpow_pos_of_pos hv _
  have hcap : ε ≤ v ^ ((1 : ℝ) / 256) / (2 : ℝ) ^ (30 : ℕ) := by
    convert hεcap using 1
    norm_num
    ring
  have hfirst : (2 : ℝ) ^ (23 : ℕ) / v ^ ((1 : ℝ) / 256) ≤
      1 / (128 * ε) := by
    apply (div_le_div_iff₀ ht (by positivity : 0 < 128 * ε)).2
    nlinarith [hcap]
  have hrewrite : v ^ (-(1 / 256 : ℝ)) =
      1 / v ^ ((1 : ℝ) / 256) := by
    rw [Real.rpow_neg hv.le]
    ring
  calc
    16 * 1024 * v ^ (-(1 / 511 : ℝ)) ≤
        16 * 1024 * v ^ (-(1 / 256 : ℝ)) := by nlinarith
    _ ≤ (2 : ℝ) ^ (23 : ℕ) / v ^ ((1 : ℝ) / 256) := by
      rw [hrewrite]
      have hnonneg : 0 ≤ 1 / v ^ ((1 : ℝ) / 256) := by positivity
      calc
        16 * 1024 * (1 / v ^ ((1 : ℝ) / 256)) ≤
            (2 : ℝ) ^ (23 : ℕ) * (1 / v ^ ((1 : ℝ) / 256)) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hnonneg
        _ = _ := by ring
    _ ≤ 1 / (128 * ε) := hfirst

/-- The numerical high-pair-tail comparison at the fixed even moment order
`R=1024`: the manuscript's threshold on `m` makes its moment bound strictly
smaller than `1/(8m)`. No probability-tail assertion is assumed here. -/
theorem high_pair_tail_constant_1024 (v m : ℝ)
    (hv : 0 < v) (hm : 0 < m)
    (hthreshold : 16 * 1024 * v ^ (-(1 / 511 : ℝ)) ≤ m) :
    2 * (625 : ℝ) ^ (512 : ℕ) / (v * m ^ (512 : ℕ)) < 1 / (8 * m) := by
  have hvpow : (v ^ (-(1 / 511 : ℝ))) ^ (511 : ℕ) = v⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
    norm_num
    exact Real.rpow_neg_one v
  have hpow : (16 * 1024 * v ^ (-(1 / 511 : ℝ))) ^ (511 : ℕ) ≤
      m ^ (511 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hthreshold _
  have hconst : 16 * (625 : ℝ) ^ (512 : ℕ) <
      (16 * 1024 : ℝ) ^ (511 : ℕ) := by
    have hbase : (625 : ℝ) ^ (512 : ℕ) ≤
        (1024 : ℝ) ^ (512 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    have hsmall : (16 : ℝ) * 1024 < 16 ^ (511 : ℕ) := by
      have h4 : (16 : ℝ) ^ (4 : ℕ) ≤ 16 ^ (511 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have ht : (16 : ℝ) * 1024 < 16 ^ (4 : ℕ) := by norm_num
      exact ht.trans_le h4
    calc
      16 * (625 : ℝ) ^ (512 : ℕ) ≤
          16 * (1024 : ℝ) ^ (512 : ℕ) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = ((16 : ℝ) * 1024) * (1024 : ℝ) ^ (511 : ℕ) := by
        rw [show (512 : ℕ) = 511 + 1 by omega, pow_succ]
        ac_rfl
      _ < (16 : ℝ) ^ (511 : ℕ) * (1024 : ℝ) ^ (511 : ℕ) :=
        mul_lt_mul_of_pos_right hsmall (by positivity)
      _ = (16 * 1024 : ℝ) ^ (511 : ℕ) := by rw [mul_pow]
  have hmain : 16 * (625 : ℝ) ^ (512 : ℕ) < v * m ^ (511 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hpow hv.le
    rw [mul_pow, hvpow] at hscaled
    have hident : v * ((16 * 1024 : ℝ) ^ (511 : ℕ) * v⁻¹) =
        (16 * 1024 : ℝ) ^ (511 : ℕ) := by
      field_simp
    rw [hident] at hscaled
    exact hconst.trans_le hscaled
  apply (div_lt_div_iff₀ (by positivity : 0 < v * m ^ (512 : ℕ))
    (by positivity : 0 < 8 * m)).2
  have hmul := mul_lt_mul_of_pos_right hmain hm
  rw [pow_succ] at hmul ⊢
  nlinarith

variable {Ω : Type*} [Fintype Ω]

/-- Finite expectation of a moment under the original indexed source. -/
noncomputable def sourceMoment (ν : FiniteLaw Ω) (S : Ω → ℝ) (r : ℕ) : ℝ :=
  ∑ ω, ν.weight ω * (S ω) ^ r

/-- Markov's inequality for the actual indexed source at the paper's even
moment order. The event and centered sum may have arbitrary dependence. -/
theorem event_le_1024_moment (ν : FiniteLaw Ω) (K : Set Ω)
    (S : Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hK : ∀ ω ∈ K, a ≤ S ω) :
    a ^ (1024 : ℕ) * ν.prob (· ∈ K) ≤ sourceMoment ν S 1024 := by
  classical
  unfold FiniteLaw.prob sourceMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ω ∈ K
  · simp only [h, ↓reduceIte]
    have hpow : a ^ (1024 : ℕ) ≤ (S ω) ^ (1024 : ℕ) :=
      pow_le_pow_left₀ ha.le (hK ω h) _
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow (ν.nonneg ω)
  · simp only [h, ↓reduceIte, mul_zero]
    exact mul_nonneg (ν.nonneg ω) (Even.pow_nonneg (by decide : Even 1024) _)

private theorem moment_factor_1024 (m : ℝ) (hm : 0 < m) :
    ((16 / 25 : ℝ) * m) ^ (1024 : ℕ) *
      ((625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ)) =
        (256 * m) ^ (512 : ℕ) := by
  have hbase : (((16 / 25 : ℝ) * m) ^ 2) * (625 / m) = 256 * m := by
    field_simp
    ring
  rw [← div_pow]
  rw [show (1024 : ℕ) = 2 * 512 by omega, pow_mul, ← mul_pow, hbase]

/-- The high-moment branch of `det:high-pair-tail`, conditional on the
separate source theorem establishing the exact even-moment estimate. The
premise is a moment of the original indexed law, not the desired tail bound. -/
theorem high_pair_tail_from_source_moment_1024 (ν : FiniteLaw Ω)
    (Y K : Set Ω) (S : Ω → ℝ) (v m : ℝ)
    (hv : 0 < v) (hY : v ≤ ν.prob (· ∈ Y)) (hm : 0 < m)
    (_hKsub : K ⊆ Y)
    (hpoint : ∀ ω ∈ K, (16 / 25 : ℝ) * m ≤ S ω)
    (hMoment : sourceMoment ν S 1024 ≤
      2 * (256 * m) ^ (512 : ℕ))
    (hthreshold : 16 * 1024 * v ^ (-(1 / 511 : ℝ)) ≤ m) :
    ν.prob (· ∈ K) / ν.prob (· ∈ Y) < 1 / (8 * m) := by
  have hden : 0 < ((16 / 25 : ℝ) * m) ^ (1024 : ℕ) := by positivity
  have hYpos : 0 < ν.prob (· ∈ Y) := hv.trans_le hY
  have hmarkov := event_le_1024_moment ν K S ((16 / 25 : ℝ) * m)
    (by positivity) hpoint
  have hfactor := moment_factor_1024 m hm
  have hnum : ν.prob (· ∈ K) ≤
      2 * (625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ) := by
    apply (mul_le_mul_iff_right₀ hden).mp
    calc
      _ ≤ sourceMoment ν S 1024 := hmarkov
      _ ≤ 2 * (256 * m) ^ (512 : ℕ) := hMoment
      _ = ((16 / 25 : ℝ) * m) ^ (1024 : ℕ) *
          (2 * (625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ)) := by
        rw [← hfactor]
        calc
          2 * (((16 / 25 : ℝ) * m) ^ (1024 : ℕ) *
              ((625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ))) =
              ((16 / 25 : ℝ) * m) ^ (1024 : ℕ) *
                (2 * ((625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ))) := by ac_rfl
          _ = _ := by rw [mul_div_assoc]
  have hnumpos : 0 ≤ 2 * (625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ) := by
    positivity
  have hquot : ν.prob (· ∈ K) / ν.prob (· ∈ Y) ≤
      (2 * (625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ)) / v := by
    apply (div_le_div_iff₀ hYpos hv).2
    have hleft := mul_le_mul_of_nonneg_right hnum hv.le
    have hright := mul_le_mul_of_nonneg_left hY hnumpos
    nlinarith
  have htail := high_pair_tail_constant_1024 v m hv hm hthreshold
  have hquotEq : (2 * (625 : ℝ) ^ (512 : ℕ) / m ^ (512 : ℕ)) / v =
      2 * (625 : ℝ) ^ (512 : ℕ) / (v * m ^ (512 : ℕ)) := by
    field_simp
  rw [hquotEq] at hquot
  exact hquot.trans_lt htail

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- Position of a member of the `i`th disjoint pair among `2m` selected
original good coordinates. -/
def pairPosition {m : ℕ} (i : Fin m) (j : Fin 2) : Fin (2 * m) :=
  ⟨2 * i.val + j.val, by omega⟩

theorem pairPosition_injective {m : ℕ} :
    Function.Injective (fun ij : Fin m × Fin 2 => pairPosition ij.1 ij.2) := by
  intro a b hab
  apply Prod.ext
  · apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [pairPosition] at hv
    omega
  · apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [pairPosition] at hv
    omega

/-- All selected pairs occupy disjoint original blocks; this is the
literal coordinate property needed by the product and moment estimates. -/
theorem selected_pairs_disjoint {m q : ℕ} (e : Fin (2*m) → Fin q)
    (he : Function.Injective e) :
    Pairwise (fun i j : Fin m => Disjoint
      (Finset.univ.image (fun t : Fin 2 => e (pairPosition i t)))
      (Finset.univ.image (fun t : Fin 2 => e (pairPosition j t)))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro a hai haj
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hai
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp haj
  have hpos := he (hu.trans hv.symm)
  have hval := congrArg Fin.val hpos
  dsimp [pairPosition] at hval
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  omega

/-- Choose `2m` distinct original coordinates from the surviving good
blocks. The paper retains at least `2m+1`, so one block remains unused. -/
def selectGoodPairs {m q : ℕ} (Q : Finset (Fin q))
    (hQ : 2*m ≤ Q.card) : Fin (2*m) → Fin q :=
  fun j => Q.orderEmbOfFin rfl (Fin.castLE hQ j)

theorem selectGoodPairs_injective {m q : ℕ} (Q : Finset (Fin q))
    (hQ : 2*m ≤ Q.card) :
    Function.Injective (selectGoodPairs Q hQ) := by
  exact (Q.orderEmbOfFin rfl).injective.comp (Fin.castLE_injective hQ)

theorem selectGoodPairs_mem {m q : ℕ} (Q : Finset (Fin q))
    (hQ : 2*m ≤ Q.card) (j : Fin (2*m)) :
    selectGoodPairs Q hQ j ∈ Q :=
  Q.orderEmbOfFin_mem rfl (Fin.castLE hQ j)

theorem long_suffix_block_arithmetic (b : ℕ) (hb : 5 ≤ b) :
    16 ≤ 2 ^ (b-1) ∧
    2 * 2 ^ (b-1) = 2 ^ b ∧
    4 * 2 ^ (b-1) = 2 ^ (b+1) := by
  have hb4 : 4 ≤ b-1 := by omega
  have hm : 2 ^ 4 ≤ 2 ^ (b-1) :=
    pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hb4
  have hsucc : b-1+1=b := by omega
  have htwo : 2 * 2 ^ (b-1) = 2 ^ b := by
    calc
      2 * 2 ^ (b-1) = 2 ^ (b-1) * 2 := Nat.mul_comm _ _
      _ = 2 ^ ((b-1)+1) := (pow_succ 2 (b-1)).symm
      _ = 2 ^ b := by rw [hsucc]
  constructor
  · norm_num at hm ⊢
    exact hm
  constructor
  · exact htwo
  · calc
      4 * 2 ^ (b-1) = 2 * (2 * 2 ^ (b-1)) := by ring
      _ = 2 * 2 ^ b := by rw [htwo]
      _ = 2 ^ (b+1) := by rw [pow_succ]; omega

/-- The iid ambient law sends an injectively selected original pair to
the exact two-copy law, for an arbitrary joint event on that pair. -/
theorem iid_selected_pair_prob (ν : FiniteLaw Z) {m q : ℕ}
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (i : Fin m) (P : Set (Fin 2 → Z)) :
    (ν.iid q).prob
      (fun c => (fun j => c (e (pairPosition i j))) ∈ P) =
    (ν.iid 2).prob (· ∈ P) := by
  let f : Fin 2 → Fin q := fun j => e (pairPosition i j)
  have hf : Function.Injective f := by
    intro a b hab
    have hp := he hab
    apply Fin.ext
    have hv := congrArg Fin.val hp
    dsimp [pairPosition] at hv
    omega
  simpa only [FiniteLaw.iid, f] using
    (FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν) f hf (· ∈ P))

def pairImage {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S) (i : Fin m) :
    Set (Fin 2 → Z) :=
  (fun s j => decode s (e (pairPosition i j))) '' K

/-- The pair indicator used in both moment arguments tests membership in
the actual retained indexed projection, rather than independent singleton
projections. -/
noncomputable def pairHit {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S)
    (i : Fin m) (c : Fin q → Z) : Bool := by
  classical
  exact decide ((fun j => c (e (pairPosition i j))) ∈ pairImage decode e K i)

noncomputable def pairBaseMass (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (K : Set S) (i : Fin m) : ℝ :=
  (ν.iid q).prob (fun c => pairHit decode e K i c)

noncomputable def centeredPairAmbient (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (K : Set S) : Fin m → (Fin q → Z) → ℝ :=
  FourthMoment.centeredPair
    (pairHit decode e K) (pairBaseMass ν decode e K)

noncomputable def centeredPairSourceSum (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (K : Set S) (s : S) : ℝ :=
  ∑ i : Fin m, FourthMoment.centeredPair
    (pairHit decode e K) (pairBaseMass ν decode e K) i (decode s)

noncomputable def conditionedIndexedLaw (source : FiniteLaw S)
    (Y : Set S) (hY : 0 < source.prob (· ∈ Y)) : FiniteLaw S := by
  classical
  exact FourthMoment.conditional source (· ∈ Y) hY

omit [Fintype Z] [Fintype S] in
theorem pairHit_of_retained {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S) (i : Fin m)
    (s : S) (hs : s ∈ K) :
    pairHit decode e K i (decode s) = true := by
  classical
  simp only [pairHit, decide_eq_true_eq]
  exact ⟨s, hs, rfl⟩

omit [Fintype S] in
theorem pairHit_ambient_mass (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (he : Function.Injective e) (K : Set S) (i : Fin m) :
    (ν.iid q).prob (fun c => pairHit decode e K i c) =
      (ν.iid 2).prob (· ∈ pairImage decode e K i) := by
  classical
  simpa only [pairHit, decide_eq_true_eq] using
    (iid_selected_pair_prob ν e he i (pairImage decode e K i))

omit [Fintype S] in
/-- If all actual pair projections are light, every retained source index
has centered pair-indicator sum at least `(16/25)m`. This is the pointwise
input to both moment branches. -/
theorem retained_centered_pair_sum_large (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (he : Function.Injective e) (K : Set S)
    (hpSmall : ∀ i : Fin m,
      (ν.iid 2).prob (· ∈ pairImage decode e K i) < 9 / 25)
    (s : S) (hs : s ∈ K) :
    (16 / 25 : ℝ) * m ≤
      ∑ i : Fin m, ((if pairHit decode e K i (decode s) then (1 : ℝ) else 0) -
        (ν.iid q).prob (fun c => pairHit decode e K i c)) := by
  classical
  have hi (i : Fin m) : (16 / 25 : ℝ) ≤
      (if pairHit decode e K i (decode s) then (1 : ℝ) else 0) -
        (ν.iid q).prob (fun c => pairHit decode e K i c) := by
    rw [pairHit_of_retained decode e K i s hs]
    simp only [↓reduceIte]
    rw [pairHit_ambient_mass ν decode e he K i]
    linarith [hpSmall i]
  calc
    (16 / 25 : ℝ) * m = ∑ _i : Fin m, (16 / 25 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ i : Fin m, ((if pairHit decode e K i (decode s) then (1 : ℝ) else 0) -
        (ν.iid q).prob (fun c => pairHit decode e K i c)) :=
      Finset.sum_le_sum (fun i _ => hi i)

omit [Fintype Z] [Fintype S] in
/-- A source index in `K` lies in every actual pair image. -/
theorem retained_in_pairImage {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S) (s : S) (hs : s ∈ K)
    (i : Fin m) :
    (fun j => decode s (e (pairPosition i j))) ∈ pairImage decode e K i :=
  ⟨s, hs, rfl⟩

/-- Once the moment argument rules out all pairs being light, the selected
heavy pair is an actual restriction of the original indexed protocol. This
consumer exposes the still-required conditional pair-tail bridge. -/
theorem suffix_many_of_conditional_pair_tail
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {m q : ℕ} (_hm : 16 ≤ m)
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (_he : Function.Injective e)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin (2*m), 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (_hY : 0 < source.prob (· ∈ Y)) (_hK : K ⊆ Y)
    (hcond : 1 / (4 * (m : ℝ)) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hTail : (∀ i : Fin m,
        (ν.toFiniteLaw.iid 2).prob (· ∈ pairImage decode e K i) < 9 / 25) →
      source.prob (· ∈ K) / source.prob (· ∈ Y) < 1 / (4 * (m : ℝ))) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  have hex : ∃ i : Fin m, (9 / 25 : ℝ) ≤
      (ν.toFiniteLaw.iid 2).prob (· ∈ pairImage decode e K i) := by
    by_contra hn
    push Not at hn
    have hlt : ∀ i : Fin m,
        (ν.toFiniteLaw.iid 2).prob (· ∈ pairImage decode e K i) < 9 / 25 := by
      intro i
      exact hn i
    exact (not_lt_of_ge hcond) (hTail hlt)
  obtain ⟨i, hi⟩ := hex
  apply SuffixMid.actual_pair_cost μ ν F decode
    (fun j => e (pairPosition i j)) R K d x hd hx hscale hprofile
  · intro j
    exact hrow (pairPosition i j)
  · simpa only [pairImage, Set.mem_image] using hi

/-- The `b≥5` suffix after the two moment inputs have been established.
The first explicit premise is four-factor product independence for actual
disjoint pairs; the second is the good-coordinate quartic TV comparison;
the third is the original indexed-law 1024th moment. None is a desired
tail or protocol lower bound. -/
theorem suffix_many_from_moments_1024
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {m q : ℕ} (hm : 16 ≤ m)
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (he : Function.Injective e)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x v ε : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin (2*m), 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1 / (4 * (m : ℝ)) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ) ^ (-20 : ℤ) / 1024 * v ^ ((1 : ℝ) / 256))
    (hcross : FourthMoment.PairCrossMoments (ν.toFiniteLaw.iid q)
      (centeredPairAmbient ν.toFiniteLaw decode e K))
    (hterms : ∀ i j k l : Fin m,
      FourthMoment.expect
        (conditionedIndexedLaw source Y (hv.trans_le hY))
        (fun s => centeredPairAmbient ν.toFiniteLaw decode e K l (decode s) *
          centeredPairAmbient ν.toFiniteLaw decode e K k (decode s) *
          centeredPairAmbient ν.toFiniteLaw decode e K j (decode s) *
          centeredPairAmbient ν.toFiniteLaw decode e K i (decode s)) ≤
      FourthMoment.expect (ν.toFiniteLaw.iid q)
        (fun c => centeredPairAmbient ν.toFiniteLaw decode e K l c *
          centeredPairAmbient ν.toFiniteLaw decode e K k c *
          centeredPairAmbient ν.toFiniteLaw decode e K j c *
          centeredPairAmbient ν.toFiniteLaw decode e K i c) + 2 * ε)
    (hHighMoment : sourceMoment source
      (centeredPairSourceSum ν.toFiniteLaw decode e K) 1024 ≤
      2 * (256 * (m : ℝ)) ^ (512 : ℕ)) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  classical
  have hYpos : 0 < source.prob (· ∈ Y) := hv.trans_le hY
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
  have hoverlap := moment_ranges_overlap_1024 v ε hv hv1 hε hεcap
  apply suffix_many_of_conditional_pair_tail μ ν F source hm decode e he
    R Y K d x hd hx hscale hprofile hrow hYpos hK hcond
  intro hpSmall
  have hp : ∀ i : Fin m,
      pairBaseMass ν.toFiniteLaw decode e K i =
      (ν.toFiniteLaw.iid q).prob (fun c => pairHit decode e K i c) := by
    intro i
    rfl
  have hpSmall' : ∀ i : Fin m,
      pairBaseMass ν.toFiniteLaw decode e K i < 9 / 25 := by
    intro i
    rw [pairBaseMass, pairHit_ambient_mass ν.toFiniteLaw decode e he K i]
    exact hpSmall i
  have hKpoint : ∀ s, s ∈ K → s ∈ Y ∧
      ∀ i : Fin m, pairHit decode e K i (decode s) = true := by
    intro s hs
    exact ⟨hK hs, fun i => pairHit_of_retained decode e K i s hs⟩
  by_cases hmoderate : (m : ℝ) ≤ 1 / (128 * ε)
  · have htail := FourthMoment.conditional_pair_tail source
      (ν.toFiniteLaw.iid q) decode (· ∈ Y) (· ∈ K) hYpos
      (pairHit decode e K) (pairBaseMass ν.toFiniteLaw decode e K)
      ε hm0 hp hpSmall' hKpoint hcross (by
        intro i j k l
        simpa only [conditionedIndexedLaw, centeredPairAmbient] using
          hterms i j k l)
    have hnum := FourthMoment.conditional_pair_numeric
      (m : ℝ) ε (by exact_mod_cast hm) hε hmoderate
    exact htail.trans_lt hnum
  · have hthreshold : 16 * 1024 * v ^ (-(1 / 511 : ℝ)) ≤ (m : ℝ) :=
      hoverlap.trans (le_of_lt (lt_of_not_ge hmoderate))
    have hpoint : ∀ s ∈ K, (16 / 25 : ℝ) * (m : ℝ) ≤
        centeredPairSourceSum ν.toFiniteLaw decode e K s := by
      intro s hs
      simpa only [centeredPairSourceSum, FourthMoment.centeredPair,
        pairBaseMass] using retained_centered_pair_sum_large
          ν.toFiniteLaw decode e he K hpSmall s hs
    have htail := high_pair_tail_from_source_moment_1024 source Y K
      (centeredPairSourceSum ν.toFiniteLaw decode e K)
      v (m : ℝ) hv hY hmR hK hpoint hHighMoment hthreshold
    have hcomparison : (1 : ℝ) / (8 * (m : ℝ)) < 1 / (4 * (m : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 8 * m)
        (by positivity : (0 : ℝ) < 4 * m)).2
      nlinarith
    exact htail.trans hcomparison

#print axioms moment_ranges_overlap_1024
#print axioms high_pair_tail_constant_1024
#print axioms event_le_1024_moment
#print axioms high_pair_tail_from_source_moment_1024
#print axioms selected_pairs_disjoint
#print axioms selectGoodPairs_injective
#print axioms long_suffix_block_arithmetic
#print axioms iid_selected_pair_prob
#print axioms pairHit_ambient_mass
#print axioms retained_centered_pair_sum_large
#print axioms suffix_many_of_conditional_pair_tail
#print axioms suffix_many_from_moments_1024

end CurrentAdditive.SuffixLong
