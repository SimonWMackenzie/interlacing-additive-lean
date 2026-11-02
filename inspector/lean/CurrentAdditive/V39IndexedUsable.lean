import CurrentAdditive.V38IndexedRemaining
import CurrentAdditive.GeneratedDeficientCap

/-! Actual indexed two-tag bad-coordinate budgets and original-label
starting supports. No iid law for a decoded indexed word is asserted. -/

namespace CurrentAdditive.V38IndexedUsable

open Paper2 Paper2.SourceMatrix Paper2.SourceSupportFrontier
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V38IndexedTwoTag
open Workspace.Types.Protocol
open scoped BigOperators

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

noncomputable def templateBad (K : Set src.inner.Label) (cap : ℝ) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter fun α => ∃ i : Fin q₁, μX.toFiniteLaw.prob
    (fun u => SourceDeficiencyTemplate.projectedAt
      (fun t => ∃ z ∈ K, src.inner.decode z=t) α (i,u)) < cap

theorem templateBad_card_lt (hD : 2 ≤ D) (K : Set src.inner.Label)
    (hK : (1/7 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (cap : ℝ) (hcap : cap ≤ 1/8) : (templateBad src K cap).card < 8*q₁ :=
  deficient_cap_card_lt src hD K hK cap hcap

theorem head_mass_ge (K : Set src.inner.Label) (cap : ℝ) (α : Fin q₂)
    (hα : α ∉ templateBad src K cap) (i : Fin q₁) :
    cap ≤ μX.toFiniteLaw.prob (fun u => (i,u) ∈ (fun z => src.inner.decode z α) '' K) := by
  classical
  have hm : cap ≤ μX.toFiniteLaw.prob (fun u => SourceDeficiencyTemplate.projectedAt
      (fun t => ∃ z ∈ K, src.inner.decode z=t) α (i,u)) := by
    by_contra! hn
    apply hα
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hn⟩
  have hev : (fun u => SourceDeficiencyTemplate.projectedAt
      (fun t => ∃ z ∈ K, src.inner.decode z=t) α (i,u)) =
      (fun u => (i,u) ∈ (fun z => src.inner.decode z α) '' K) := by
    funext u
    apply propext
    constructor
    · rintro ⟨t,⟨z,hz,hzt⟩,htu⟩
      exact ⟨z,hz,(congrFun hzt α).trans htu⟩
    · rintro ⟨z,hz,hzu⟩
      exact ⟨src.inner.decode z,⟨z,hz,rfl⟩,hzu⟩
  rwa [hev] at hm

noncomputable def diagonalBad (U : Set (V38IndexedTwoTag.Column src)) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter fun α => src.gamma.law.toFiniteLaw.prob
    (fun γ => Sum.inr (α,γ) ∈ U) < 3/4

theorem diagonal_mass_ge (U : Set (V38IndexedTwoTag.Column src)) (α : Fin q₂)
    (hα : α ∉ diagonalBad src U) :
    3/4 ≤ src.gamma.law.toFiniteLaw.prob (fun γ => Sum.inr (α,γ) ∈ U) := by
  classical
  simpa [diagonalBad] using hα

theorem diagonalBad_card_lt (U : Set (V38IndexedTwoTag.Column src)) (η : ℝ)
    (hη : 0 < η) (hU : 1-η ≤ (V38IndexedTwoTag.law src).toFiniteLaw.prob (· ∈ U)) :
    ((diagonalBad src U).card : ℝ) < 1024*η*q₂ := by
  classical
  have ho := (src.outer.law.prod src.gamma.law).toFiniteLaw.prob_le_one
    (fun z => Sum.inl z ∈ U)
  have hd : 1-256*η ≤ ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw.prob
      (fun z => Sum.inr z ∈ U) := by
    rw [V38IndexedTwoTag.prob_split] at hU
    linarith
  have havg : 1-256*η ≤ (q₂ : ℝ)⁻¹ * ∑ α : Fin q₂,
      src.gamma.law.toFiniteLaw.prob (fun γ => Sum.inr (α,γ) ∈ U) := by
    rw [PositiveRationalLaw.toFiniteLaw_prod] at hd
    change 1-256*η ≤ ((PositiveRationalLaw.uniform (Fin q₂)).toFiniteLaw.prod
      src.gamma.law.toFiniteLaw).prob (fun z => Sum.inr (z.1,z.2) ∈ U) at hd
    rw [FiniteLaw.prod_prob _ _ (fun α γ => Sum.inr (α,γ) ∈ U)] at hd
    simpa only [PositiveRationalLaw.toFiniteLaw,PositiveRationalLaw.uniform,
      Fintype.card_fin,Rat.cast_inv,Rat.cast_natCast,← Finset.mul_sum] using hd
  have hh := SourceDeficiency.deficient_card_mul_lt
    (fun α : Fin q₂ => src.gamma.law.toFiniteLaw.prob (fun γ => Sum.inr (α,γ) ∈ U))
    (3/4) (256*η) (by positivity) (fun _ => src.gamma.law.toFiniteLaw.prob_le_one _)
    (by simpa only [Fintype.card_fin] using havg)
  change ((diagonalBad src U).card : ℝ)*(1-3/4) < _ at hh
  simp only [Fintype.card_fin] at hh
  nlinarith

noncomputable def bad (K : Set src.inner.Label) (U : Set (V38IndexedTwoTag.Column src))
    (cap : ℝ) : Finset (Fin q₂) := templateBad src K cap ∪ diagonalBad src U

theorem bad_card_lt (hD : 2 ≤ D) (K : Set src.inner.Label)
    (U : Set (V38IndexedTwoTag.Column src)) (cap η : ℝ)
    (hcap : cap ≤ 1/8) (hη : 0 < η)
    (hK : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (hU : 1-η ≤ (V38IndexedTwoTag.law src).toFiniteLaw.prob (· ∈ U)) :
    ((bad src K U cap).card : ℝ) < 8*q₁+1024*η*q₂ := by
  have ht := templateBad_card_lt src hD K (by linarith) cap hcap
  have hd := diagonalBad_card_lt src U η hη hU
  have hu : ((bad src K U cap).card : ℝ) ≤
      (templateBad src K cap).card+(diagonalBad src U).card := by
    exact_mod_cast Finset.card_union_le (templateBad src K cap) (diagonalBad src U)
  have ht' : ((templateBad src K cap).card : ℝ) < 8*q₁ := by exact_mod_cast ht
  linarith

theorem sum_bad_card_lt (hD : 2 ≤ D) (K : Fin s → Set src.inner.Label)
    (U : Set (V38IndexedTwoTag.Column src)) (cap η : ℝ)
    (hcap : cap ≤ 1/8) (hη : 0 < η)
    (hK : ∀ j, (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K j))
    (hU : 1-η ≤ (V38IndexedTwoTag.law src).toFiniteLaw.prob (· ∈ U)) :
    (∑ j, ((bad src (K j) U cap).card : ℝ)) < 8*s*q₁+1024*s*η*q₂ := by
  have hh := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin s)).Nonempty)
    (fun j _ => bad_card_lt src hD (K j) U cap η hcap hη (hK j) hU)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  nlinarith

noncomputable def initialState {A : Type*}
    (P : Protocol A (V38IndexedTwoTag.Column src) Bool)
    (U : Set (V38IndexedTwoTag.Column src)) (Bad Marks : Finset (Fin q₂)) :
    State A (V38IndexedTwoTag.Column src) (Fin q₂) src.gamma.Label := by
  classical
  exact {
    protocol := P
    columns := U
    coordinates := Finset.univ \ Bad
    attachments := Marks
    support := fun α => {γ : src.gamma.Label | Sum.inr (α,γ) ∈ U}.toFinset }

theorem initial_facts {A : Type*} (P : Protocol A (V38IndexedTwoTag.Column src) Bool)
    (K : Set src.inner.Label) (U : Set (V38IndexedTwoTag.Column src))
    (cap : ℝ) (Marks : Finset (Fin q₂)) :
    let S := initialState src P U (bad src K U cap) Marks
    S.coordinates.card+(bad src K U cap).card=q₂ ∧
    (∀ α ∈ S.coordinates, (3/4 : ℝ) ≤ SourceSupportStep.mass src.gamma.law.toFiniteLaw (S.support α)) ∧
    (∀ α ∈ S.coordinates, ∀ γ ∈ S.support α, Sum.inr (α,γ) ∈ U) ∧
    (∀ α ∈ S.coordinates, ∀ i : Fin q₁,
      cap ≤ μX.toFiniteLaw.prob (fun u => (i,u) ∈ (fun z => src.inner.decode z α) '' K)) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change (Finset.univ \ bad src K U cap).card+(bad src K U cap).card=q₂
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (bad src K U cap))
  · intro α hα
    have hn : α ∉ diagonalBad src U := by
      exact fun hd => (Finset.mem_sdiff.mp hα).2 (Finset.mem_union_right _ hd)
    simpa [initialState,SourceSupportStep.mass] using diagonal_mass_ge src U α hn
  · intro α _ γ hγ
    simpa [initialState] using hγ
  · intro α hα i
    have hn : α ∉ templateBad src K cap := by
      exact fun ht => (Finset.mem_sdiff.mp hα).2 (Finset.mem_union_left _ ht)
    exact head_mass_ge src K cap α hn i

end CurrentAdditive.V38IndexedUsable

#print axioms CurrentAdditive.V38IndexedUsable.templateBad
#print axioms CurrentAdditive.V38IndexedUsable.templateBad_card_lt
#print axioms CurrentAdditive.V38IndexedUsable.head_mass_ge
#print axioms CurrentAdditive.V38IndexedUsable.diagonalBad
#print axioms CurrentAdditive.V38IndexedUsable.diagonal_mass_ge
#print axioms CurrentAdditive.V38IndexedUsable.diagonalBad_card_lt
#print axioms CurrentAdditive.V38IndexedUsable.bad
#print axioms CurrentAdditive.V38IndexedUsable.bad_card_lt
#print axioms CurrentAdditive.V38IndexedUsable.sum_bad_card_lt
#print axioms CurrentAdditive.V38IndexedUsable.initialState
#print axioms CurrentAdditive.V38IndexedUsable.initial_facts
