import CurrentAdditive.RestoreSelection
import CurrentAdditive.DeterministicFullBoost
import CurrentAdditive.InjectiveProjectionTVCompatible
import CurrentAdditive.V39RareBoost

/-! The current restoration theorem with exactly the two profile thresholds.
The old restoration proof assumes a third threshold and is not used as a
substitute. Its fixed-prefix and block-selection algorithms are reused;
the positive-Bob branch uses the checked current two-threshold suffix.
-/

namespace CurrentAdditive.V39TwoThresholdRestoration

open Paper2 CurrentAdditive.ArbitraryPrefix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicRestoration
open Workspace.Types.CommComplexity

set_option maxHeartbeats 2000000

theorem epsilon_eq (v τ : ℝ) :
    conditioningEpsilonR 1024 v τ = V38Moments.epsilon v τ := by
  unfold conditioningEpsilonR V38Moments.epsilon
  congr 1
  norm_num [Real.rpow_neg]

theorem old_count_le (v τ : ℝ) (hv : 0 < v) (hτ : 0 < τ) :
    conditioningExceptionCountR 1024 v τ ≤ V38Moments.exceptionCount v τ := by
  unfold conditioningExceptionCountR V38Moments.exceptionCount
  rw [epsilon_eq]
  norm_num only [Nat.cast_ofNat,show (-(2/(1024:ℝ)))= -(1/512:ℝ) by norm_num]
  apply Nat.mul_le_mul_left
  apply Nat.ceil_mono
  have he : 0 < V38Moments.epsilon v τ := by
    exact lt_min hτ (mul_pos (by positivity) (Real.rpow_pos_of_pos hv _))
  gcongr <;> first | positivity | norm_num

theorem fullboost
    {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (Rows : Fin q → Set X) (Y : Set S)
    (C a : ℕ) (x v δ : ℝ)
    (hC : 3 ≤ C) (hx : 0 < x) (hscale : (2 : ℝ)^a*x ≤ 1)
    (hcount : (if a=0 then 1 else 2^(a-1)+1) ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1) (hδ : 0 < δ)
    (hY : v ≤ source.prob (· ∈ Y))
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      x ≤ μ.toFiniteLaw.prob (· ∈ A) → 1-δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw
      x ((C-1:ℕ):ℤ))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ V38Moments.epsilon v (δ/2)) :
    C+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) Y := by
  let G : (Fin q × X) → S → Bool := fun a s => F a.2 (decode s a.1)
  let D := Compression.restrictionD G (rowRectangle Good Rows) Y
  by_contra hn
  change ¬ (C+a ≤ D) at hn
  have hD : D ≤ C+a-1 := by omega
  obtain ⟨A,B,Good',Rows',K,P',hab,hGoodOne,hGoodMany,hrow',hcond,
      hGoodsub,hRowsSub,hKsub,hcost,heval⟩ :=
    full_prefix_state μ.toFiniteLaw source G Good Rows Y C a x
      (by omega) hx hcount hrow (hv.trans_le hY) hD
  have hupper : Compression.restrictionD G (rowRectangle Good' Rows') K ≤ C-1 :=
    residual_restriction_upper G Good' Rows' K P' (C-1) hcost heval
  have hOutside' : ∀ i ∈ Good', i ∉ E := fun i hi => hOutside i (hGoodsub hi)
  by_cases hB0 : B=0
  · have hrow0 : ∀ i ∈ Good', x ≤ μ.toFiniteLaw.prob (· ∈ Rows' i) := by
      intro i hi
      simpa [hB0] using hrow' i hi
    have hmass : 1 ≤ source.prob (· ∈ K)/source.prob (· ∈ Y) := by
      simpa [hB0] using hcond
    have hgoodSubset : Good' ⊆ (Finset.univ : Finset (Fin q)) \ E := by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hOutside' i hi⟩
    have hgoodOne' : ∀ i ∈ Good', ∀ P : Z → Prop,
        |source.prob (fun s => s ∈ Y ∧ P (decode s i))/source.prob (· ∈ Y)-ν.toFiniteLaw.prob P| ≤
          V38Moments.epsilon v (δ/2) := by
      intro i hi P
      let e1 : Fin 1 → Fin q := fun _ => i
      have hinj : Function.Injective e1 := fun _ _ _ => Subsingleton.elim _ _
      have h := injective_good_conditioned_event_abs source ν.toFiniteLaw decode
        (· ∈ Y) (hv.trans_le hY) E Good' hgoodSubset
        (V38Moments.epsilon v (δ/2)) hTV (by decide : 1 ≤ 8)
        e1 hinj (fun _ => hi) (fun z => P (z 0))
      simpa only [e1,ReferenceProjectionMass.iid_one_coordinate_prob] using h
    have hεδ : V38Moments.epsilon v (δ/2) ≤ δ :=
      (min_le_left _ _).trans (by linarith)
    have hlow := FullBoost.zero_bob_suffix μ.toFiniteLaw ν.toFiniteLaw F source decode
      Good' hGoodOne Rows' Y K C x δ (V38Moments.epsilon v (δ/2))
      (hv.trans_le hY) hKsub hmass hrow0 hεδ hgoodOne' hnear
    change C ≤ Compression.restrictionD G (rowRectangle Good' Rows') K at hlow
    omega
  · have hBpos : 1 ≤ B := by omega
    have hlow := V38RareBoost.rare_suffix_two_threshold μ.toFiniteLaw ν F source decode hwise
      Good' E (hGoodMany hBpos) hOutside' Rows' Y K (C-1) x v (δ/2)
      (by omega) hx hp
      (by intro i hi; simpa only [show (B-1)+1=B by omega] using hrow' i hi)
      hv hv1 (by linarith) hY hKsub
      (by simpa only [show (B-1)+1=B by omega] using hcond) hTV
    change (C-1)+1 ≤ Compression.restrictionD G (rowRectangle Good' Rows') K at hlow
    omega

theorem restored_profile
    {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (r C : ℕ) (θ φ δ : ℝ)
    (src : CodeSource 8192 (2^r) Z ν)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hδ : 0 < δ)
    (hQ : 128*((V38Moments.exceptionCount φ (δ/2):ℝ)+1) ≤ (2^r:ℕ))
    (hθQ : ((2^r:ℕ):ℝ)*θ ≤ 1/20)
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      θ ≤ μ.toFiniteLaw.prob (· ∈ A) → 1-δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw
      θ ((C-1:ℕ):ℤ)) :
    V38RestrictionProfiles.TwoThresholdProfile
      (fun (seed : src.Label) (a : Fin (2^r) × X) => F a.2 (src.decode seed a.1))
      src.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (2^r))).prod μ).toFiniteLaw
      φ ((C+r:ℕ):ℤ) := by
  classical
  have hQold : 128*((conditioningExceptionCountR 1024 φ (δ/2):ℝ)+1) ≤ ((2^r:ℕ):ℝ) := by
    have h := old_count_le φ (δ/2) hφ (by linarith)
    have hR : (conditioningExceptionCountR 1024 φ (δ/2):ℝ) ≤
        (V38Moments.exceptionCount φ (δ/2):ℝ) := by exact_mod_cast h
    linarith
  intro j W U hW hU
  have hr : 7 ≤ r := width_exponent_seven r
    (conditioningExceptionCountR 1024 φ (δ/2)) hQold
  have hj : j.val+1 ≤ r := by have := j.isLt; omega
  obtain ⟨E,pick,hE,hOut,hRows,hTV⟩ := restore_selected_blocks μ ν r src U W
    ⟨j.val,by have := j.isLt; omega⟩ θ φ δ hθ hφ hδ hQold hθQ hU hW
  let Good : Finset (Fin (2^r)) := Finset.univ.image pick
  let Rows : Fin (2^r) → Set X := fun i => {x | (i,x) ∈ U}
  let a := r-j.val
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hcount : 2^(a-1)+1 ≤ Good.card := by
    have hcard : Good.card=2^(r-j.val-1)+1 := by simp [Good,Finset.card_image_of_injective _ pick.injective]
    change 2^(r-j.val-1)+1 ≤ Good.card
    omega
  have hOutside : ∀ i ∈ Good, i ∉ E := by
    intro i hi
    obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hi
    exact hOut h
  have hrow : ∀ i ∈ Good, (2:ℝ)^a*θ ≤ μ.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i hi
    obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hi
    simpa only [a,Nat.cast_pow,Nat.cast_ofNat,Rows] using hRows h
  have hscale : (2:ℝ)^a*θ ≤ 1 := by
    have hpw : (2:ℝ)^a ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num) (by dsimp [a]; omega)
    have hsc : (2:ℝ)^r*θ ≤ 1/20 := by exact_mod_cast hθQ
    exact (mul_le_mul_of_nonneg_right hpw hθ.le).trans (by linarith)
  have hTV' : ∀ J : Finset (Fin (2^r)), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition src.law.toFiniteLaw (· ∈ W) (hφ.trans_le hW))
        ν.toFiniteLaw src.decode J ≤ V38Moments.epsilon φ (δ/2) := by
    simpa only [epsilon_eq] using hTV
  have hl := fullboost μ ν F src.law.toFiniteLaw src.decode src.exactLaw Good E Rows W
    C a θ φ δ hC hθ hscale (by simpa only [if_neg (by omega : a≠0)] using hcount)
    hOutside hrow hφ hφ1 hδ hW hnear hp hTV'
  have hsub : Set.MapsTo id (rowRectangle Good Rows) U := by intro ix hix; exact hix.2
  have hlarge : C+a ≤ Compression.restrictionD
      (fun ix seed => F ix.2 (src.decode seed ix.1)) U W :=
    hl.trans (SourceProjection.restrictionD_map_le
      (fun ix seed => F ix.2 (src.decode seed ix.1)) id id U W
        (rowRectangle Good Rows) W hsub (fun _ h => h))
  rw [SourceProjection.restrictionD_transpose
    (fun ix seed => F ix.2 (src.decode seed ix.1)) U W]
  dsimp [a] at hlarge
  omega

theorem restored
    {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (r C : ℕ) (θ φ δ : ℝ)
    (src : CodeSource 8192 (2^r) Z ν)
    (hC : 3 ≤ C) (hD : D F=C) (hθ : 0 < θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hδ : 0 < δ)
    (hQ : 128*((V38Moments.exceptionCount φ (δ/2):ℝ)+1) ≤ (2^r:ℕ))
    (hθQ : ((2^r:ℕ):ℝ)*θ ≤ 1/20)
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      θ ≤ μ.toFiniteLaw.prob (· ∈ A) → 1-δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw
      θ ((C-1:ℕ):ℤ)) :
    D (fun (seed : src.Label) (a : Fin (2^r) × X) => F a.2 (src.decode seed a.1)) = C+r ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun (seed : src.Label) (a : Fin (2^r) × X) => F a.2 (src.decode seed a.1))
      src.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (2^r))).prod μ).toFiniteLaw
      φ ((C+r:ℕ):ℤ) := by
  have hprofile := restored_profile μ ν F r C θ φ δ src hC hθ hφ hφ1 hδ hQ hθQ hnear hp
  refine ⟨le_antisymm ?_ ?_,hprofile⟩
  · simpa only [hD] using generated_restore_upper ν F r src
  · have h := hprofile ⟨0,by decide⟩ Set.univ Set.univ (by simpa using hφ1) (by norm_num)
    have heq : Compression.restrictionD
        (fun (seed : src.Label) (a : Fin (2^r) × X) => F a.2 (src.decode seed a.1))
        Set.univ Set.univ = D (fun (seed : src.Label) (a : Fin (2^r) × X) =>
          F a.2 (src.decode seed a.1)) := by
      have hh := pullback_D_eq_of_surjective
        (fun (seed : src.Label) (a : Fin (2^r) × X) => F a.2 (src.decode seed a.1))
        Subtype.val Subtype.val
        (fun x => ⟨⟨x,Set.mem_univ x⟩,rfl⟩) (fun y => ⟨⟨y,Set.mem_univ y⟩,rfl⟩)
      exact hh
    simpa only [Fin.val_zero,Nat.cast_zero,sub_zero,heq,Nat.cast_le] using h

end CurrentAdditive.V39TwoThresholdRestoration

#print axioms CurrentAdditive.V39TwoThresholdRestoration.fullboost
#print axioms CurrentAdditive.V39TwoThresholdRestoration.restored
