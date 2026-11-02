import CurrentAdditive.GeneralProbabilityMoment

namespace V42GeneralWeightedMoment

open MeasureTheory ProbabilityTheory V39MomentCount V39GeneralProbabilityMoment
open scoped BigOperators ENNReal
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

/-- The product of the coefficients at the factor positions of a monomial. -/
def tupleWeight {n m : ℕ} (a : Fin m → ℝ) (f : Fin n → Fin m) : ℝ :=
  ∏ t, a (f t)

/-- A pattern names each factor position by one of `r` classes, and assigns
an original coordinate only to the classes that it actually uses. -/
def PatternCode (m r : ℕ) :=
  (b : Fin (2*r) → Fin r) × ({j // j ∈ support b} → Fin m)

noncomputable instance (m r : ℕ) : Fintype (PatternCode m r) := by
  classical
  unfold PatternCode
  infer_instance

def codeWeight {m r : ℕ} (a : Fin m → ℝ) (c : PatternCode m r) : ℝ :=
  ∏ j : {j // j ∈ support c.1}, a (c.2 j)

theorem tupleWeight_nonneg {n m : ℕ} (a : Fin m → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (f : Fin n → Fin m) : 0 ≤ tupleWeight a f := by
  exact Finset.prod_nonneg fun t _ => ha0 (f t)

theorem codeWeight_nonneg {m r : ℕ} (a : Fin m → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (c : PatternCode m r) : 0 ≤ codeWeight a c := by
  exact Finset.prod_nonneg fun j _ => ha0 (c.2 j)

theorem tupleWeight_comp_le {m r : ℕ} (a : Fin m → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (A : Fin r → Fin m) (b : Fin (2*r) → Fin r) :
    tupleWeight a (A ∘ b) ≤ ∏ j : {j // j ∈ support b}, a (A j.val) := by
  classical
  have heq : tupleWeight a (A ∘ b) =
      ∏ j : {j // j ∈ support b}, a (A j.val) ^ fiberCount b j.val := by
    exact monomial_fiberwise (fun j (_ : Unit) => a (A j)) b ()
  rw [heq]
  apply Finset.prod_le_prod
  · intro j _; exact pow_nonneg (ha0 _) _
  · intro j _
    have hpos := fiberCount_pos_of_mem b j.val j.property
    have hpow : a (A j.val) ^ fiberCount b j.val ≤ a (A j.val) ^ 1 :=
      pow_le_pow_of_le_one (ha0 _) (ha1 _) hpos
    simpa using hpow

theorem sum_codeWeight (m r : ℕ) (a : Fin m → ℝ)
    (hW : 1 ≤ ∑ i, a i) :
    ∑ c : PatternCode m r, codeWeight a c ≤
      (r : ℝ)^(2*r) * (∑ i, a i)^r := by
  classical
  change (∑ c : (b : Fin (2*r) → Fin r) × ({j // j ∈ support b} → Fin m), codeWeight a c) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ b : Fin (2*r) → Fin r, (∑ i, a i)^(support b).card := by
      apply Finset.sum_congr rfl
      intro b _
      change (∑ g : {j // j ∈ support b} → Fin m, ∏ j, a (g j)) = _
      rw [← Fintype.prod_sum]
      simp
    _ ≤ ∑ _b : Fin (2*r) → Fin r, (∑ i, a i)^r := by
      apply Finset.sum_le_sum
      intro b _
      apply pow_le_pow_right₀ hW
      simpa using (Finset.card_le_univ (support b))
    _ = _ := by simp

theorem goodTuples_weight_le (m r : ℕ) (_hr : 1 ≤ r)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hW : 1 ≤ ∑ i, a i) :
    ∑ f ∈ goodTuples m r, tupleWeight a f ≤
      (((r : ℝ)^2)*(∑ i, a i))^r := by
  classical
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst m
    norm_num at hW
  let G := {f // f ∈ goodTuples m r}
  have hfactor (f : G) : ∃ A : Fin r → Fin m, ∃ b : Fin (2*r) → Fin r,
      A ∘ b = f.val := by
    apply small_range_factor m r hm f.val
    exact support_card_le_half m r f.val (Finset.mem_filter.mp f.property).2
  choose A b hAb using hfactor
  let encode : G → PatternCode m r := fun f => ⟨b f, fun j => A f j.val⟩
  let decode : PatternCode m r → (Fin (2*r) → Fin m) :=
    fun c t => c.2 ⟨c.1 t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩
  have hdecode (f : G) : decode (encode f) = f.val := by
    exact hAb f
  have hinj : Function.Injective encode := by
    intro f g hfg
    apply Subtype.ext
    rw [← hdecode f, ← hdecode g, hfg]
  calc
    _ = ∑ f : G, tupleWeight a f.val := (Finset.sum_coe_sort _ _).symm
    _ ≤ ∑ f : G, codeWeight a (encode f) := by
      apply Finset.sum_le_sum
      intro f _
      rw [← hAb f]
      exact tupleWeight_comp_le a ha0 ha1 (A f) (b f)
    _ = ∑ c ∈ Finset.univ.image encode, codeWeight a c := by
      exact (Finset.sum_image hinj.injOn).symm
    _ ≤ ∑ c : PatternCode m r, codeWeight a c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun c _ _ => codeWeight_nonneg a ha0 c)
    _ ≤ (r : ℝ)^(2*r) * (∑ i, a i)^r := sum_codeWeight m r a hW
    _ = _ := by rw [mul_pow, pow_mul]

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
theorem weighted_monomial {n m : ℕ} (a : Fin m → ℝ)
    (X : Fin m → Ω → ℝ) (f : Fin n → Fin m) (ω : Ω) :
    monomial (fun i ω => a i * X i ω) f ω = tupleWeight a f * monomial X f ω := by
  exact Finset.prod_mul_distrib

omit [IsProbabilityMeasure μ] in
theorem weighted_coordinate_bound {m : ℕ} (a : Fin m → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (X : Fin m → Ω → ℝ) (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) :
    ∀ i, ∀ᵐ ω ∂μ, |a i * X i ω| ≤ 1 := by
  intro i
  filter_upwards [hbound i] with ω hω
  rw [abs_mul, abs_of_nonneg (ha0 i)]
  exact (mul_le_of_le_one_right (ha0 i) hω).trans (ha1 i)

/-- V42 `lem:conditioning-moment` on an arbitrary probability space.
Measurability and AE boundedness imply every integrability fact used here;
there is no moment or finite-space premise. -/
theorem bounded_wise_even_moment (m r : ℕ) (hr : 1 ≤ r)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hW : 1 ≤ ∑ i, a i)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 2*r → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, a i * X i ω|^(2*r) ∂μ ≤
      (((r : ℝ)^2)*(∑ i, a i))^r := by
  classical
  let Y : Fin m → Ω → ℝ := fun i ω => a i * X i ω
  have hY : ∀ i, AEMeasurable (Y i) μ := fun i => (hX i).const_mul _
  have hYbound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1 :=
    weighted_coordinate_bound μ a ha0 ha1 X hbound
  have hweighted (f : Fin (2*r) → Fin m) :
      (∫ ω, monomial Y f ω ∂μ) = tupleWeight a f * ∫ ω, monomial X f ω ∂μ := by
    simp_rw [show ∀ ω, monomial Y f ω = tupleWeight a f * monomial X f ω from
      weighted_monomial a X f]
    exact integral_const_mul _ _
  have hzero (f : Fin (2*r) → Fin m) (hf : f ∉ goodTuples m r) :
      ∫ ω, monomial Y f ω ∂μ = 0 := by
    have hng : ¬ NoSingleton f := by
      intro hg
      exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
    obtain ⟨j,hj⟩ := not_forall.mp hng
    rw [hweighted, monomial_integral_zero_of_singleton μ X hX hcenter hindep f j
      (not_not.mp hj), mul_zero]
  calc
    _ = ∫ ω, ∑ f : Fin (2*r) → Fin m, monomial Y f ω ∂μ := by
      congr 1
      funext ω
      exact even_power_expansion Y ω
    _ = ∑ f : Fin (2*r) → Fin m, ∫ ω, monomial Y f ω ∂μ :=
      integral_finsetSum Finset.univ fun f _ => monomial_integrable μ Y hY hYbound f
    _ = ∑ f ∈ goodTuples m r, ∫ ω, monomial Y f ω ∂μ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      exact hzero f hf
    _ ≤ ∑ f ∈ goodTuples m r, tupleWeight a f := by
      apply Finset.sum_le_sum
      intro f _
      rw [hweighted]
      exact (mul_le_mul_of_nonneg_left (monomial_integral_le_one μ X hX hbound f)
        (tupleWeight_nonneg a ha0 f)).trans_eq (mul_one _)
    _ ≤ _ := goodTuples_weight_le m r hr a ha0 ha1 hW

theorem bounded_wise_moment_256 (m : ℕ)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hW : 1 ≤ ∑ i, a i)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 256 → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, a i * X i ω|^256 ∂μ ≤
      ((2 : ℝ)^14*(∑ i, a i))^128 := by
  simpa only [show 2*128 = 256 by rfl,
    show ((128 : ℕ) : ℝ)^2 = (2 : ℝ)^14 by norm_num] using
      bounded_wise_even_moment μ m 128 (by omega) a ha0 ha1 hW X hX hcenter hbound hindep




theorem bounded_wise_moment_1024 (m : ℕ)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hW : 1 ≤ ∑ i, a i)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 1024 → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, a i * X i ω|^1024 ∂μ ≤
      ((2 : ℝ)^18*(∑ i, a i))^512 := by
  simpa only [show 2*512 = 1024 by rfl,
    show ((512 : ℕ) : ℝ)^2 = (2 : ℝ)^18 by norm_num] using
      bounded_wise_even_moment μ m 512 (by omega) a ha0 ha1 hW X hX hcenter hbound hindep

#print axioms goodTuples_weight_le
#print axioms bounded_wise_even_moment
#print axioms bounded_wise_moment_256
#print axioms bounded_wise_moment_1024

end V42GeneralWeightedMoment
