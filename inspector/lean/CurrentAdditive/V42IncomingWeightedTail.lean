import CurrentAdditive.V42IncomingWeightedSection
import CurrentAdditive.V42WeightedMoment

namespace CurrentAdditive.V42IncomingWeightedTail

open Paper2 CurrentAdditive.EvenMoment
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open scoped BigOperators

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem probability_le_even_moment
    {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    (Bad : Ω → Prop) (S : Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (hbad : ∀ ω, Bad ω → t ≤ |S ω|) :
    ν.prob Bad ≤ ex ν (fun ω => |S ω|^256) / t^256 := by
  classical
  apply (le_div_iff₀ (pow_pos ht 256)).2
  unfold FiniteLaw.prob ex
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : Bad ω
  · simp only [h, ite_true]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ ht.le (hbad ω h) 256) (ν.nonneg ω)
  · simp only [h, ite_false, zero_mul]
    exact mul_nonneg (ν.nonneg ω) (pow_nonneg (abs_nonneg _) _)

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- The weighted lower tail under the actual metadata source. All `d_i`
are fixed before metadata is drawn. Independence comes from the source's
exact event law, and the finite-law moment theorem is proved separately. -/
theorem metadata_weighted_half_template_tail
    (d : Fin w → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1)
    (hW : 0 < ∑ i, d i) :
    streams.metadataStream.law.toFiniteLaw.prob
      (fun md => V42IncomingWeightedSection.templateMass src streams d md <
        (∑ i, d i)/2) ≤
      (((2 : ℝ)^14*(∑ i, d i))^128) /
        ((((255/256 : ℝ)-1/2)*(∑ i, d i))^256) := by
  classical
  let source := streams.metadataStream
  let ν := source.law.toFiniteLaw
  let F : Fin w → source.Label → Bool := fun i md =>
    isTemplateFlag (source.decode md i)
  let Z : Fin w → source.Label → ℝ := fun i md =>
    (if F i md then (1 : ℝ) else 0) - (255/256 : ℝ)
  let blocks : Fin w → Finset (Fin w) := fun i => {i}
  let H : ∀ i : Fin w, (blocks i → (Fin s ⊕ I)) → Bool :=
    fun i z => isTemplateFlag (z ⟨i,Finset.mem_singleton_self _⟩)
  have hwise : IsDWise (8*256) ν source.decode (metadataLaw μI).toFiniteLaw := by
    intro S hS E
    exact source.exactLaw S (hS.trans (by norm_num)) E
  have hjointBool : IndicatorJointAgreement ν F 256 := by
    intro S hS E
    have h := disjoint_blocks_indicator_joint_agreement ν (metadataLaw μI).toFiniteLaw
      source.decode hwise blocks (by intro i; simp [blocks])
      (by intro i j hij; simpa [blocks] using hij) H S hS E
    simpa only [F,H,blocks] using h
  have hjoint : V38GeneralMoment.JointLawAgreement ν Z 256 := by
    intro S hS E
    exact hjointBool S hS
      (fun z => E (fun i => (if z i then (1 : ℝ) else 0) - (255/256 : ℝ)))
  have hmean (i : Fin w) : ν.prob (fun md => F i md = true) = 255/256 :=
    metadata_template_coordinate_mean src streams (by norm_num) i
  have hcenter : ∀ i, ex ν (Z i) = 0 := by
    intro i
    have heq : ex ν (Z i) = ν.prob (fun md => F i md = true) - 255/256 := by
      dsimp [Z]
      unfold ex FiniteLaw.prob
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ν.total,
        one_mul, mul_ite, mul_one, mul_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro md _
      by_cases h : F i md = true <;> simp [h]
    rw [heq,hmean]
    ring
  have hbound : ∀ i md, |Z i md| ≤ 1 := by
    intro i md
    dsimp [Z]
    split_ifs <;> norm_num
  have hmoment := V42WeightedMoment.bounded_wise_moment_256 ν w d
    hd0 hd1 hW Z hcenter hbound hjoint
  let S : source.Label → ℝ := fun md => ∑ i, d i * Z i md
  let t : ℝ := ((255/256 : ℝ)-1/2)*(∑ i, d i)
  have ht : 0 < t := by dsimp [t]; positivity
  have hS (md : source.Label) : S md =
      V42IncomingWeightedSection.templateMass src streams d md -
        (∑ i, d i)*(255/256 : ℝ) := by
    dsimp [S,Z,V42IncomingWeightedSection.templateMass,F,source]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hbad (md : source.Label)
      (hb : V42IncomingWeightedSection.templateMass src streams d md <
        (∑ i, d i)/2) : t ≤ |S md| := by
    rw [hS]
    rw [abs_of_nonpos (by linarith :
      V42IncomingWeightedSection.templateMass src streams d md -
        (∑ i, d i)*(255/256 : ℝ) ≤ 0)]
    dsimp [t]
    linarith
  have hm := probability_le_even_moment ν
    (fun md => V42IncomingWeightedSection.templateMass src streams d md <
      (∑ i, d i)/2) S t ht hbad
  exact hm.trans (div_le_div_of_nonneg_right hmoment (pow_nonneg ht.le _))

end CurrentAdditive.V42IncomingWeightedTail

#print axioms CurrentAdditive.V42IncomingWeightedTail.metadata_weighted_half_template_tail
