import CurrentAdditive.V38Moments
import CurrentAdditive.InjectiveProjectionTVCompatible
import Paper2.ReferenceProjectionMass

/-! One current conditioning witness for the common owner argument. All
singleton and pair conclusions concern images of the one original event
under original laws. No conditioned independence is asserted. -/

namespace CurrentAdditive.V39SharedConditioning

open Paper2

private def pairToFin2 {A : Type*} (z : A × A) : Fin 2 → A :=
  fun k => if k.val=0 then z.1 else z.2

private def fin2ToPair {A : Type*} (v : Fin 2 → A) : A × A := (v 0,v 1)

private def pairFin2Equiv {A : Type*} : (A × A) ≃ (Fin 2 → A) where
  toFun := pairToFin2
  invFun := fin2ToPair
  left_inv z := by cases z; rfl
  right_inv v := by funext k; fin_cases k <;> rfl

private theorem pair_prod_eq_iid2 {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (B : Set (A × A)) :
    (μ.prod μ).prob (· ∈ B) = (μ.iid 2).prob (fun v => fin2ToPair v ∈ B) := by
  classical
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv pairFin2Equiv
  intro z
  have hw : (μ.prod μ).weight z = (μ.iid 2).weight (pairFin2Equiv z) := by
    rcases z with ⟨a,b⟩
    simp [FiniteLaw.prod,FiniteLaw.iid,pairFin2Equiv,pairToFin2]
  change (if z ∈ B then (μ.prod μ).weight z else 0) =
    (if fin2ToPair (pairFin2Equiv z) ∈ B then (μ.iid 2).weight (pairFin2Equiv z) else 0)
  rw [show fin2ToPair (pairFin2Equiv z)=z from pairFin2Equiv.left_inv z,hw]

theorem epsilon_eq_R1024 (v τ : ℝ) :
    V38Moments.epsilon v τ = conditioningEpsilonR 1024 v τ :=
  (V38Moments.epsilon_eq_old v τ).trans (FiniteV35Conditioning.paperEpsilon_eq v τ)

theorem epsilon_lt_point01 (v τ : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    V38Moments.epsilon v τ < 1/100 := by
  have hp : v^((1 : ℝ)/256) ≤ 1 := Real.rpow_le_one hv hv1 (by norm_num)
  calc
    V38Moments.epsilon v τ ≤ (2 : ℝ)^(-30 : ℤ)*v^((1 : ℝ)/256) := min_le_right _ _
    _ ≤ (2 : ℝ)^(-30 : ℤ)*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ < 1/100 := by norm_num

variable {S A : Type*} [Fintype S] [Fintype A] {w : ℕ}

/-- An actual retained event has conditional mass one in its own image;
the singleton TV estimate therefore gives its original image mass. -/
theorem singleton_image_mass (ν : FiniteLaw S) (μ : FiniteLaw A)
    (draw : S → Fin w → A) (Y : Set S) (hY : 0 < ν.prob (· ∈ Y))
    (i : Fin w) (ε : ℝ)
    (hTV : projectionTV (condition ν (· ∈ Y) hY) μ draw
      (Finset.univ.image (fun _ : Fin 1 => i)) ≤ ε) :
    1-ε ≤ μ.prob (· ∈ (fun t => draw t i) '' Y) := by
  classical
  let B : Set A := (fun t => draw t i) '' Y
  let e : Fin 1 → Fin w := fun _ => i
  have he : Function.Injective e := by intro a b _; exact Subsingleton.elim a b
  have hconditional : (condition ν (· ∈ Y) hY).prob (fun t => draw t i ∈ B)=1 := by
    rw [condition_prob_event_eq_div]
    have hid : ν.prob (fun t => t ∈ Y ∧ draw t i ∈ B)=ν.prob (· ∈ Y) := by
      congr 1
      funext t
      apply propext
      exact ⟨And.left,fun ht => ⟨ht,⟨t,ht,rfl⟩⟩⟩
    rw [hid]
    exact div_self hY.ne'
  have ht := injective_projectionTV_event_abs (condition ν (· ∈ Y) hY)
    μ draw e he ε hTV (fun v => v 0 ∈ B)
  simp only [e] at ht
  rw [hconditional,ReferenceProjectionMass.iid_one_coordinate_prob] at ht
  have hh := (abs_le.mp ht).2
  change 1-ε ≤ μ.prob (· ∈ B)
  linarith

/-- Distinct origins give the original product law on the pair image,
even though the retained event itself is an arbitrary joint event. -/
theorem pair_image_mass (ν : FiniteLaw S) (μ : FiniteLaw A)
    (draw : S → Fin w → A) (Y : Set S) (hY : 0 < ν.prob (· ∈ Y))
    (i j : Fin w) (hij : i ≠ j) (ε : ℝ)
    (hTV : projectionTV (condition ν (· ∈ Y) hY) μ draw
      (Finset.univ.image (fun k : Fin 2 => if k.val=0 then i else j)) ≤ ε) :
    1-ε ≤ (μ.prod μ).prob (· ∈ (fun t => (draw t i,draw t j)) '' Y) := by
  classical
  let B : Set (A × A) := (fun t => (draw t i,draw t j)) '' Y
  let e : Fin 2 → Fin w := fun k => if k.val=0 then i else j
  have he : Function.Injective e := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hij (by simpa [e] using hkl)).elim
    · exact (hij (by simpa [e] using hkl.symm)).elim
    · rfl
  have hconditional : (condition ν (· ∈ Y) hY).prob
      (fun t => (draw t i,draw t j) ∈ B)=1 := by
    rw [condition_prob_event_eq_div]
    have hid : ν.prob (fun t => t ∈ Y ∧ (draw t i,draw t j) ∈ B)=ν.prob (· ∈ Y) := by
      congr 1
      funext t
      apply propext
      exact ⟨And.left,fun ht => ⟨ht,⟨t,ht,rfl⟩⟩⟩
    rw [hid]
    exact div_self hY.ne'
  have ht := injective_projectionTV_event_abs (condition ν (· ∈ Y) hY)
    μ draw e he ε hTV (fun v => fin2ToPair v ∈ B)
  have hpoint : (fun t => fin2ToPair (fun k => draw t (e k)) ∈ B)=
      (fun t => (draw t i,draw t j) ∈ B) := rfl
  rw [hpoint,hconditional,← pair_prod_eq_iid2 μ B] at ht
  have hh := (abs_le.mp ht).2
  change 1-ε ≤ (μ.prod μ).prob (· ∈ B)
  linarith

/-- Select the exceptional coordinates once, before choosing any owner
or pair. The same witness controls all original singleton and pair images. -/
theorem choose_shared_exception (ν : FiniteLaw S) (μ : FiniteLaw A)
    (draw : S → Fin w → A) (hwise : IsDWise 8192 ν draw μ)
    (Y : Set S) (θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η)
    (hY : θ ≤ ν.prob (· ∈ Y)) :
    ∃ E : Finset (Fin w), E.card ≤ V38Moments.exceptionCount θ (η/2) ∧
      (∀ J : Finset (Fin w), J ⊆ Finset.univ \ E → J.card ≤ 8 →
        projectionTV (condition ν (· ∈ Y) (hθ.trans_le hY)) μ draw J ≤
          conditioningEpsilonR 1024 θ (η/2)) ∧
      (∀ i : Fin w, i ∉ E →
        1-η/2 ≤ μ.prob (· ∈ (fun t => draw t i) '' Y)) ∧
      (∀ i j : Fin w, i ≠ j → i ∉ E → j ∉ E →
        (99/100 : ℝ) < (μ.prod μ).prob
          (· ∈ (fun t => (draw t i,draw t j)) '' Y)) := by
  classical
  obtain ⟨E,hE,hTV⟩ := V38Moments.conditioning_outside_exception
    ν μ draw hwise Y θ (η/2) hθ (by linarith) hY
  have hTV' : ∀ J : Finset (Fin w), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition ν (· ∈ Y) (hθ.trans_le hY)) μ draw J ≤
        conditioningEpsilonR 1024 θ (η/2) := by
    simpa only [epsilon_eq_R1024] using hTV
  refine ⟨E,hE,hTV',?_,?_⟩
  · intro i hi
    let e : Fin 1 → Fin w := fun _ => i
    have hs : Finset.univ.image e ⊆ Finset.univ \ E := by
      intro z hz
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
      simp [e,hi]
    have hc : (Finset.univ.image e).card ≤ 8 :=
      (Finset.card_image_le).trans (by simp)
    have hm := singleton_image_mass ν μ draw Y (hθ.trans_le hY) i
      (V38Moments.epsilon θ (η/2)) (hTV _ hs hc)
    have hcap : V38Moments.epsilon θ (η/2) ≤ η/2 := min_le_left _ _
    linarith
  · intro i j hij hi hj
    let e : Fin 2 → Fin w := fun k => if k.val=0 then i else j
    have hm (k : Fin 2) : e k ∉ E := by fin_cases k <;> simp [e,hi,hj]
    have hs : Finset.univ.image e ⊆ Finset.univ \ E := by
      intro z hz
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
      simp [hm k]
    have hc : (Finset.univ.image e).card ≤ 8 :=
      (Finset.card_image_le).trans (by simp)
    have hp := pair_image_mass ν μ draw Y (hθ.trans_le hY) i j hij
      (V38Moments.epsilon θ (η/2)) (hTV _ hs hc)
    have hε := epsilon_lt_point01 θ (η/2) hθ.le
      (hY.trans (ν.prob_le_one _))
    linarith

end CurrentAdditive.V39SharedConditioning

#print axioms CurrentAdditive.V39SharedConditioning.epsilon_eq_R1024
#print axioms CurrentAdditive.V39SharedConditioning.epsilon_lt_point01
#print axioms CurrentAdditive.V39SharedConditioning.singleton_image_mass
#print axioms CurrentAdditive.V39SharedConditioning.pair_image_mass
#print axioms CurrentAdditive.V39SharedConditioning.choose_shared_exception
