import CurrentAdditive.ConditioningExceptionV35

/-!
Private selected-v38 readback for the probability arguments in
`source/appendices/moments.tex` and `source/sections/retained-tuples.tex`.
The law in the high moments is always the original indexed source law.
-/

namespace V38Moments

open Paper2 Paper2.FiniteLaw CurrentAdditive

set_option maxRecDepth 8192

private theorem loose1024 (m : ℕ) :
    2 * (256 * (m : ℝ)) ^ 512 ≤ (2 ^ (18 : ℕ) * (m : ℝ)) ^ 512 := by
  have hbase : 0 ≤ 256 * (m : ℝ) := by positivity
  have hfactor : (2 : ℝ) ≤ 2 ^ (512 : ℕ) := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ (512 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    2 * (256 * (m : ℝ)) ^ 512 ≤
        2 ^ (512 : ℕ) * (256 * (m : ℝ)) ^ 512 :=
          mul_le_mul_of_nonneg_right hfactor (pow_nonneg hbase _)
    _ = (512 * (m : ℝ)) ^ 512 := by rw [← mul_pow]; congr 1; ring
    _ ≤ (2 ^ (18 : ℕ) * (m : ℝ)) ^ 512 := by
      gcongr
      norm_num

private theorem loose256 (m : ℕ) :
    2 * (64 * (m : ℝ)) ^ 128 ≤ (2 ^ (14 : ℕ) * (m : ℝ)) ^ 128 := by
  have hbase : 0 ≤ 64 * (m : ℝ) := by positivity
  have hfactor : (2 : ℝ) ≤ 2 ^ (128 : ℕ) := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ (128 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    2 * (64 * (m : ℝ)) ^ 128 ≤
        2 ^ (128 : ℕ) * (64 * (m : ℝ)) ^ 128 :=
          mul_le_mul_of_nonneg_right hfactor (pow_nonneg hbase _)
    _ = (128 * (m : ℝ)) ^ 128 := by rw [← mul_pow]; congr 1; ring
    _ ≤ (2 ^ (14 : ℕ) * (m : ℝ)) ^ 128 := by
      gcongr
      norm_num

/-- The two v38 displayed moments for disjoint small-coordinate indicator
tests under the original 8192-wise indexed law. The paper's larger constants
follow from the older, sharper finite-law theorem. -/
theorem source_indicator_moments
    {Ω A : Type*} [Fintype Ω] [Fintype A]
    (ν : FiniteLaw Ω) (μ : FiniteLaw A)
    {q m : ℕ} (decode : Ω → Fin q → A)
    (hwise : IsDWise 8192 ν decode μ)
    (blocks : Fin m → Finset (Fin q))
    (hsize : ∀ i, (blocks i).card ≤ 8)
    (hdisj : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (H : ∀ i : Fin m, (blocks i → A) → Bool) :
    let F : Fin m → Ω → Bool :=
      fun i ω => H i (fun j => decode ω j)
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^1024) ≤
        (2 ^ (18 : ℕ) * (m : ℝ)) ^ 512 ∧
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^256) ≤
        (2 ^ (14 : ℕ) * (m : ℝ)) ^ 128 := by
  have h := FiniteV35.conditioning_moment_disjoint_source
    ν μ decode hwise blocks hsize hdisj H
  constructor
  · calc
      _ ≤ 2 * ((1024 : ℝ) * (m : ℝ) / 4) ^ 512 := h.1
      _ = 2 * (256 * (m : ℝ)) ^ 512 := by congr 1; congr 1; ring
      _ ≤ _ := loose1024 m
  · calc
      _ ≤ 2 * ((256 : ℝ) * (m : ℝ) / 4) ^ 128 := h.2
      _ = 2 * (64 * (m : ℝ)) ^ 128 := by congr 1; congr 1; ring
      _ ≤ _ := loose256 m

noncomputable def epsilon (v τ : ℝ) : ℝ :=
  min τ ((2 : ℝ)^(-30 : ℤ) * v^((1 : ℝ)/256))

noncomputable def exceptionCount (v τ : ℝ) : ℕ :=
  8 * ⌈(2 : ℝ)^(20 : ℕ) * (epsilon v τ)^(-(2 : ℝ)) *
    v^(-(1 : ℝ)/512)⌉₊

theorem epsilon_eq_old (v τ : ℝ) :
    epsilon v τ = FiniteV35Conditioning.paperEpsilon v τ := rfl

theorem exceptionCount_old_le (v τ : ℝ) (hv : 0 < v) (hτ : 0 < τ) :
    FiniteV35Conditioning.paperExceptionCount v τ ≤ exceptionCount v τ := by
  have hε : 0 < epsilon v τ := by
    unfold epsilon
    exact lt_min hτ (mul_pos (by positivity) (Real.rpow_pos_of_pos hv _))
  have hbase : 0 ≤ (epsilon v τ)^(-(2 : ℝ)) * v^(-(1 : ℝ)/512) := by
    positivity
  unfold FiniteV35Conditioning.paperExceptionCount exceptionCount
  rw [← epsilon_eq_old]
  apply Nat.mul_le_mul_left
  apply Nat.ceil_mono
  nlinarith

/-- The selected-v38 exceptional-coordinate conclusion, with its displayed
allowance and the actual conditional finite-law TV. -/
theorem conditioning_outside_exception
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (Y : Set S) (v τ : ℝ)
    (hv : 0 < v) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) :
    ∃ E : Finset (Fin q), E.card ≤ exceptionCount v τ ∧
      ∀ J : Finset (Fin q),
        J ⊆ Finset.univ \ E → J.card ≤ 8 →
          projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
            μ decode J ≤ epsilon v τ := by
  obtain ⟨E, hcard, hTV⟩ :=
    conditioning_exceptional_coordinates_R
      (by decide : Even 1024) (by decide : 8 ≤ 1024)
      source μ decode (· ∈ Y) v τ hv hY hτ
      (by simpa only [show 8 * 1024 = 8192 by norm_num] using hwise)
  refine ⟨E, ?_, ?_⟩
  · exact hcard.trans (by
      rw [← FiniteV35Conditioning.paperExceptionCount_eq]
      exact exceptionCount_old_le v τ hv hτ)
  · simpa only [epsilon_eq_old, FiniteV35Conditioning.paperEpsilon_eq] using hTV

/-- The selected-v38 exact eight-wise pair tail, under the original indexed
law, with the sharper first displayed numerical constant. -/
theorem exact_pair_tail
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 16 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (K : Set S)
    (hsmall : ∀ i : Fin m,
      (μ.iid 2).prob (· ∈ CurrentAdditive.SuffixLong.pairImage decode e K i) < 9/25) :
    source.prob (· ∈ K) < 2/(m : ℝ)^2 ∧
    source.prob (· ∈ K) < 9/(50*(m : ℝ)) := by
  obtain ⟨hbase, hfinal⟩ := FiniteV35.pair_projections_eight
    source μ (by omega) decode hwise e he K hsmall
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hden : (0 : ℝ) < (16/25 : ℝ)^4 * (m : ℝ)^4 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ)^2 := by positivity
  have hnum :
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
          ((16/25 : ℝ)^4*(m : ℝ)^4) < 2/(m : ℝ)^2 := by
    apply (div_lt_div_iff₀ hden hm2).2
    norm_num
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg ((m : ℝ) - 16)]
  exact ⟨hbase.trans_lt hnum, hfinal⟩

/-- Both explicit intermediate estimates in the v38 conditional pair proof.
The fourth-moment estimate uses TV only on good coordinates. The 1024th
moment estimate uses the *unconditioned* 8192-wise source and divides by
the probability of `Y` afterwards. -/
theorem conditional_pair_estimates
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {q m : ℕ} (hm : 16 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (Y K : Set S) (v τ : ℝ)
    (hv : 0 < v) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (E : Finset (Fin q))
    (hgood : ∀ t : Fin (2*m), e t ∉ E)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
          μ decode J ≤ epsilon v τ)
    (hsmall : ∀ i : Fin m,
      (μ.iid 2).prob
        (· ∈ CurrentAdditive.SuffixLong.pairImage decode e K i) < 9/25) :
    source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
      2/(m : ℝ)^2 + 16*epsilon v τ ∧
    source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
      (((2 : ℝ)^20)/(m : ℝ))^512/v := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hεpos : 0 < epsilon v τ := by
    unfold epsilon
    exact lt_min hτ (mul_pos (by positivity) (Real.rpow_pos_of_pos hv _))
  have hc : (0 : ℝ) < (16/25 : ℝ)^4 := by norm_num
  have hquartic := FiniteV35.pair_projections_conditional_fourth
    source μ (by omega : 0 < m) decode e he Y K hK
    (hv.trans_le hY) E (epsilon v τ) hgood hTV hsmall
  have hhigh := FiniteV35.pair_projections_conditional_high
    source μ (by omega : 0 < m) decode hwise e he Y K v hv hY hK hsmall
  have hden : (0 : ℝ) < (16/25 : ℝ)^4 * (m : ℝ)^4 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ)^2 := by positivity
  have hbase :
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
          ((16/25 : ℝ)^4*(m : ℝ)^4) ≤ 2/(m : ℝ)^2 := by
    apply (div_le_div_iff₀ hden hm2).2
    norm_num
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg ((m : ℝ) - 16)]
  have herror : 2*epsilon v τ/(16/25 : ℝ)^4 ≤ 16*epsilon v τ := by
    apply (div_le_iff₀ hc).2
    norm_num
    nlinarith [le_of_lt hεpos]
  have h2 : (2 : ℝ) ≤ 2 ^ (512 : ℕ) := by
    calc
      (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ (512 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hconst : 2*(625 : ℝ)^512 ≤ ((2 : ℝ)^20)^512 := by
    calc
      2*(625 : ℝ)^512 ≤ 2^512*(625 : ℝ)^512 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (1250 : ℝ)^512 := by rw [← mul_pow]; norm_num
      _ ≤ ((2 : ℝ)^20)^512 := by gcongr; norm_num
  constructor
  · linarith
  · calc
      _ ≤ 2*(625 : ℝ)^512/(v*(m : ℝ)^512) := hhigh
      _ ≤ ((2 : ℝ)^20)^512/(v*(m : ℝ)^512) := by
        apply div_le_div_of_nonneg_right hconst
        positivity
      _ = (((2 : ℝ)^20)/(m : ℝ))^512/v := by
        rw [div_pow]
        field_simp

/-- The conditional v38 pair tail uses one exceptional set selected from
the original law before choosing disjoint good pairs. The final ratio is
the actual law conditioned on the arbitrary event `Y`. -/
theorem conditional_pair_tail
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {q m : ℕ} (hm : 16 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (Y K : Set S) (v τ : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y) :
    ∃ E : Finset (Fin q), E.card ≤ exceptionCount v τ ∧
      ∀ (e : Fin (2*m) → Fin q), Function.Injective e →
        (∀ t : Fin (2*m), e t ∉ E) →
        (∀ i : Fin m,
          (μ.iid 2).prob
            (· ∈ CurrentAdditive.SuffixLong.pairImage decode e K i) < 9/25) →
        source.prob (· ∈ K) / source.prob (· ∈ Y) <
          1/(4*(m : ℝ)) := by
  obtain ⟨E, hcard, hTV⟩ := conditioning_outside_exception
    source μ decode hwise Y v τ hv hτ hY
  refine ⟨E, hcard, ?_⟩
  intro e he hgood hsmall
  by_contra hnot
  have hge : 1/(4*(m : ℝ)) ≤
      source.prob (· ∈ K) / source.prob (· ∈ Y) := le_of_not_gt hnot
  obtain ⟨i, hi⟩ := FiniteV35.pair_projections_good_source_epsilon
    source μ hm decode hwise e he Y K v τ hv hv1 hτ hY hK
    E hgood (by simpa only [epsilon_eq_old,
      FiniteV35Conditioning.paperEpsilon_eq] using hTV) hge
  exact (not_le.mpr (hsmall i)) hi

#print axioms source_indicator_moments
#print axioms conditioning_outside_exception
#print axioms exact_pair_tail
#print axioms conditional_pair_estimates
#print axioms conditional_pair_tail

end V38Moments
