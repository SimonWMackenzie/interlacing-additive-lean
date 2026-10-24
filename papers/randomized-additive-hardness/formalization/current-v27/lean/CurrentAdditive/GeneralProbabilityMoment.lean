import CurrentAdditive.SingletonCount

/-! The v39 moment lemma on arbitrary probability spaces, with ordinary
bounded-wise independence and AE bounded centered real random variables. -/

namespace V39GeneralProbabilityMoment

open MeasureTheory ProbabilityTheory V39MomentCount
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

def monomial {n m : ℕ} (X : Fin m → Ω → ℝ) (f : Fin n → Fin m) : Ω → ℝ :=
  fun ω => ∏ t, X (f t) ω

theorem coordinate_integrable {m : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) (i : Fin m) :
    Integrable (X i) μ := by
  apply Integrable.of_bound (hX i).aestronglyMeasurable 1
  simpa only [Real.norm_eq_abs] using hbound i

theorem monomial_abs_le_one {n m : ℕ} (X : Fin m → Ω → ℝ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) (f : Fin n → Fin m) :
    ∀ᵐ ω ∂μ, |monomial X f ω| ≤ 1 := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, |X i ω| ≤ 1 := ae_all_iff.2 hbound
  filter_upwards [hall] with ω hω
  unfold monomial
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun t _ => hω (f t))

theorem monomial_integrable {n m : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) (f : Fin n → Fin m) :
    Integrable (monomial X f) μ := by
  have hmeas : AEStronglyMeasurable (monomial X f) μ :=
    Finset.aestronglyMeasurable_fun_prod Finset.univ
      (fun t _ => (hX (f t)).aestronglyMeasurable)
  exact Integrable.of_bound hmeas 1
    (by simpa only [Real.norm_eq_abs] using monomial_abs_le_one μ X hbound f)

theorem monomial_integral_le_one {n m : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) (f : Fin n → Fin m) :
    ∫ ω, monomial X f ω ∂μ ≤ 1 := by
  have hle : ∀ᵐ ω ∂μ, monomial X f ω ≤ 1 :=
    (monomial_abs_le_one μ X hbound f).mono fun ω h => (le_abs_self _).trans h
  simpa using integral_mono_ae (monomial_integrable μ X hX hbound f)
    (integrable_const (1 : ℝ)) hle

theorem monomial_fiberwise {n m : ℕ} (X : Fin m → Ω → ℝ)
    (f : Fin n → Fin m) (ω : Ω) :
    monomial X f ω =
      ∏ j : {j // j ∈ support f}, (X j.val ω) ^ fiberCount f j.val := by
  classical
  have h := Finset.prod_fiberwise_of_maps_to' (s := Finset.univ)
    (t := support f) (g := f)
    (fun t _ => Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)
    (fun j => X j ω)
  simp only [Finset.prod_const] at h
  calc
    monomial X f ω = ∏ j ∈ support f, (X j ω) ^ fiberCount f j := by
      simpa only [monomial, fiberCount] using h.symm
    _ = _ := (Finset.prod_coe_sort (s := support f)
      (f := fun j : Fin m => (X j ω) ^ fiberCount f j)).symm

theorem monomial_integral_zero_of_singleton {m r : ℕ}
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 2*r → iIndepFun (s.restrict X) μ)
    (f : Fin (2*r) → Fin m) (j : Fin m) (hj : fiberCount f j = 1) :
    ∫ ω, monomial X f ω ∂μ = 0 := by
  classical
  have hjS : j ∈ support f :=
    (Finset.fiber_card_ne_zero_iff_mem_image Finset.univ f j).1
      (by change fiberCount f j ≠ 0; omega)
  have hi := hindep (support f) (support_card_le (2*r) m f)
  have hprod := hi.integral_fun_prod_comp (fun i => hX i.val)
    (f := fun i (x : ℝ) => x ^ fiberCount f i.val)
    (fun _ => by fun_prop)
  change (∫ ω, ∏ i : {j // j ∈ support f}, X i.val ω ^ fiberCount f i.val ∂μ) =
    ∏ i : {j // j ∈ support f}, ∫ ω, X i.val ω ^ fiberCount f i.val ∂μ at hprod
  simp_rw [monomial_fiberwise]
  rw [hprod]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨j,hjS⟩ : {j // j ∈ support f}))
  simpa only [hj, pow_one] using hcenter j

theorem even_power_expansion {m r : ℕ} (X : Fin m → Ω → ℝ) (ω : Ω) :
    |∑ i, X i ω|^(2*r) = ∑ f : Fin (2*r) → Fin m, monomial X f ω := by
  rw [(show Even (2*r) by simp).pow_abs]
  exact Fintype.sum_pow (fun i => X i ω) (2*r)

theorem even_moment_integrable {m r : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1) :
    Integrable (fun ω => |∑ i, X i ω|^(2*r)) μ := by
  have hsum : Integrable (fun ω => ∑ f : Fin (2*r) → Fin m, monomial X f ω) μ :=
    integrable_finsetSum Finset.univ fun f _ => monomial_integrable μ X hX hbound f
  exact hsum.congr (ae_of_all μ fun ω => (even_power_expansion X ω).symm)

/-- The exact manuscript bound, without a finite-space restriction or an
assumed moment. Measurability and AE boundedness imply all integrability. -/
theorem bounded_wise_even_moment (m r : ℕ) (hr : 1 ≤ r)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 2*r → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, X i ω|^(2*r) ∂μ ≤ (((r : ℝ)^2)*m)^r := by
  classical
  have htarget := even_moment_integrable μ (r := r) X hX hbound
  have hzero (f : Fin (2*r) → Fin m) (hf : f ∉ goodTuples m r) :
      ∫ ω, monomial X f ω ∂μ = 0 := by
    have hng : ¬ NoSingleton f := by
      intro hg
      exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
    obtain ⟨j,hj⟩ := not_forall.mp hng
    exact monomial_integral_zero_of_singleton μ X hX hcenter hindep f j (not_not.mp hj)
  calc
    _ = ∫ ω, ∑ f : Fin (2*r) → Fin m, monomial X f ω ∂μ := by
      congr 1
      funext ω
      exact even_power_expansion X ω
    _ = ∑ f : Fin (2*r) → Fin m, ∫ ω, monomial X f ω ∂μ :=
      integral_finsetSum Finset.univ fun f _ => monomial_integrable μ X hX hbound f
    _ = ∑ f ∈ goodTuples m r, ∫ ω, monomial X f ω ∂μ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      exact hzero f hf
    _ ≤ ∑ _f ∈ goodTuples m r, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f _
      exact monomial_integral_le_one μ X hX hbound f
    _ = ((goodTuples m r).card : ℝ) := by simp
    _ ≤ _ := goodTuples_card_le_target m r hr

theorem bounded_wise_moment_1024 (m : ℕ)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 1024 → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, X i ω|^1024 ∂μ ≤ ((2 : ℝ)^18*m)^512 := by
  simpa only [show 2*512 = 1024 by rfl,
    show ((512 : ℕ) : ℝ)^2 = (2 : ℝ)^18 by norm_num] using
      bounded_wise_even_moment μ m 512 (by omega) X hX hcenter hbound hindep

theorem bounded_wise_moment_256 (m : ℕ)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 256 → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, X i ω|^256 ∂μ ≤ ((2 : ℝ)^14*m)^128 := by
  simpa only [show 2*128 = 256 by rfl,
    show ((128 : ℕ) : ℝ)^2 = (2 : ℝ)^14 by norm_num] using
      bounded_wise_even_moment μ m 128 (by omega) X hX hcenter hbound hindep

theorem moment_256_of_1024_independent (m : ℕ)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hindep : ∀ s : Finset (Fin m), s.card ≤ 1024 → iIndepFun (s.restrict X) μ) :
    ∫ ω, |∑ i, X i ω|^256 ∂μ ≤ ((2 : ℝ)^14*m)^128 :=
  bounded_wise_moment_256 μ m X hX hcenter hbound
    (fun s hs => hindep s (hs.trans (by decide)))

#print axioms monomial
#print axioms coordinate_integrable
#print axioms monomial_abs_le_one
#print axioms monomial_integrable
#print axioms monomial_integral_le_one
#print axioms monomial_fiberwise
#print axioms monomial_integral_zero_of_singleton
#print axioms even_power_expansion
#print axioms even_moment_integrable
#print axioms bounded_wise_even_moment
#print axioms bounded_wise_moment_1024
#print axioms bounded_wise_moment_256
#print axioms moment_256_of_1024_independent

end V39GeneralProbabilityMoment
