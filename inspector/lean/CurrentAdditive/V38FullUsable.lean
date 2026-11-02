import CurrentAdditive.V38Matrix
import Paper2.SourceDeficiencyTemplate
import Paper2.SourceDeficiency
import Paper2.SourceCollisionPartition
import Paper2.SourceSupportFrontier

/-! Actual two-family bad-coordinate budgets and actual initial word
supports for v39/v38 robustness.tex:215--265. The old three-tag diagonal
law is not used. No profile or desired communication cost is a premise. -/

namespace CurrentAdditive.V38FullUsable

open Paper2 Paper2.SourceMatrix Paper2.SourceSupportFrontier
open CurrentAdditive.V38Matrix
open Workspace.Types.Protocol
open scoped BigOperators

variable {X Y A : Type*} [Fintype X] [Fintype Y]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

noncomputable def diagonalBad (ν : PositiveRationalLaw Y)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y)) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter fun α => (ν.iid (q₁+s+1)).toFiniteLaw.prob
    (fun γ => Sum.inr (α, γ) ∈ U) < 3 / 4

theorem diagonal_mass_ge (ν : PositiveRationalLaw Y)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y)) (α : Fin q₂)
    (hα : α ∉ diagonalBad ν U) :
    3 / 4 ≤ (ν.iid (q₁+s+1)).toFiniteLaw.prob
      (fun γ => Sum.inr (α, γ) ∈ U) := by
  classical
  simpa [diagonalBad] using hα

theorem diagonalBad_card_lt (ν : PositiveRationalLaw Y)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (η : ℝ) (hη : 0 < η)
    (hU : 1 - η ≤ (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U)) :
    ((diagonalBad ν U).card : ℝ) < 1024 * η * q₂ := by
  classical
  have ho := (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun z => Sum.inl z ∈ U)
  have hd : 1 - 256 * η ≤ (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
      (fun z => Sum.inr z ∈ U) := by
    rw [V38Matrix.tagged_prob] at hU
    linarith
  have havg : 1 - 256 * η ≤ (q₂ : ℝ)⁻¹ * ∑ α : Fin q₂,
      (ν.iid (q₁+s+1)).toFiniteLaw.prob (fun γ => Sum.inr (α, γ) ∈ U) := by
    change 1 - 256 * η ≤ (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
      (· ∈ {z | Sum.inr z ∈ U}) at hd
    rw [SourceProjection.outer_word_average] at hd
    exact hd
  have hh := SourceDeficiency.deficient_card_mul_lt
    (fun α : Fin q₂ => (ν.iid (q₁+s+1)).toFiniteLaw.prob
      (fun γ => Sum.inr (α, γ) ∈ U)) (3/4) (256*η) (by positivity)
    (fun _ => (ν.iid (q₁+s+1)).toFiniteLaw.prob_le_one _)
    (by simpa only [Fintype.card_fin] using havg)
  change ((diagonalBad ν U).card : ℝ) * (1 - 3/4) < _ at hh
  simp only [Fintype.card_fin] at hh
  nlinarith

noncomputable def bad (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (K : Set (Template q₁ q₂ X)) (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) : Finset (Fin q₂) :=
  SourceDeficiencyTemplate.deficientAt μ (· ∈ K) xcap ∪ diagonalBad ν U

theorem usable_masses (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (K : Set (Template q₁ q₂ X)) (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (α : Fin q₂) (hα : α ∉ bad μ ν K U xcap) :
    (∀ i : Fin q₁, xcap ≤ μ.toFiniteLaw.prob
      (fun u => (i,u) ∈ (fun z => z α) '' K)) ∧
    3 / 4 ≤ (ν.iid (q₁+s+1)).toFiniteLaw.prob
      (fun γ => Sum.inr (α,γ) ∈ U) := by
  classical
  have hn : α ∉ SourceDeficiencyTemplate.deficientAt μ (· ∈ K) xcap ∧
      α ∉ diagonalBad ν U := by
    simpa only [bad, Finset.mem_union, not_or] using hα
  constructor
  · intro i
    have hh := SourceDeficiencyTemplate.block_mass_ge_of_not_mem μ
      (· ∈ K) xcap α hn.1 i
    exact hh
  · exact diagonal_mass_ge ν U α hn.2

theorem bad_card_lt (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (K : Set (Template q₁ q₂ X)) (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (xcap η : ℝ) (hxcap : xcap ≤ 1/8) (hη : 0 < η)
    (hK : (998/1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ K))
    (hU : 1 - η ≤ (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U)) :
    ((bad μ ν K U xcap).card : ℝ) < 8 * q₁ + 1024 * η * q₂ := by
  have ht := SourceDeficiencyTemplate.deficientAt_card_lt μ (· ∈ K) xcap hxcap hK
  have hd := diagonalBad_card_lt ν U η hη hU
  have hu : ((bad μ ν K U xcap).card : ℝ) ≤
      (SourceDeficiencyTemplate.deficientAt μ (· ∈ K) xcap).card +
        (diagonalBad ν U).card := by
    exact_mod_cast Finset.card_union_le
      (SourceDeficiencyTemplate.deficientAt μ (· ∈ K) xcap) (diagonalBad ν U)
  have ht' : ((SourceDeficiencyTemplate.deficientAt μ (· ∈ K) xcap).card : ℝ) <
      8 * q₁ := by exact_mod_cast ht
  linarith

theorem sum_bad_card_lt
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (K : Fin s → Set (Template q₁ q₂ X))
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (xcap η : ℝ) (hxcap : xcap ≤ 1/8) (hη : 0 < η)
    (hK : ∀ j, (998/1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ K j))
    (hU : 1 - η ≤ (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U)) :
    (∑ j, ((bad μ ν (K j) U xcap).card : ℝ)) <
      8 * s * q₁ + 1024 * s * η * q₂ := by
  have hh := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin s)).Nonempty)
    (fun j _ => bad_card_lt μ ν (K j) U xcap η hxcap hη (hK j) hU)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  nlinarith

/-- The actual starting state uses every original retained diagonal word
in each usable coordinate. Its protocol and column set are the given ones. -/
noncomputable def initialState (P : Protocol A (V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (Bad Marks : Finset (Fin q₂)) :
    State A (V38Matrix.TaggedColumn q₁ q₂ s Y) (Fin q₂) (Word q₁ s Y) := by
  classical
  exact {
    protocol := P
    columns := U
    coordinates := Finset.univ \ Bad
    attachments := Marks
    support := fun α => {γ : Word q₁ s Y | Sum.inr (α, γ) ∈ U}.toFinset }

theorem initial_count
    (P : Protocol A (V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (Bad Marks : Finset (Fin q₂)) :
    (initialState P U Bad Marks).coordinates.card + Bad.card = q₂ := by
  classical
  change (Finset.univ \ Bad).card + Bad.card = q₂
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hb : Bad.card ≤ q₂ := by simpa using Finset.card_le_univ Bad
  omega

theorem initial_reaches
    (P : Protocol A (V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (Bad Marks : Finset (Fin q₂)) :
    ∀ α ∈ (initialState P U Bad Marks).coordinates,
      ∀ γ ∈ (initialState P U Bad Marks).support α, Sum.inr (α, γ) ∈ U := by
  classical
  intro α _ γ hγ
  simpa [initialState] using hγ

theorem initial_mass
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (K : Set (Template q₁ q₂ X)) (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (P : Protocol A (V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (Marks : Finset (Fin q₂)) :
    ∀ α ∈ (initialState P U (bad μ ν K U xcap) Marks).coordinates,
      (3 / 4 : ℝ) ≤ SourceSupportStep.mass
        (ν.iid (q₁+s+1)).toFiniteLaw
        ((initialState P U (bad μ ν K U xcap) Marks).support α) := by
  classical
  intro α hα
  have hn : α ∉ bad μ ν K U xcap := (Finset.mem_sdiff.mp hα).2
  simpa [initialState, SourceSupportStep.mass] using (usable_masses μ ν K U xcap α hn).2

end CurrentAdditive.V38FullUsable

#print axioms CurrentAdditive.V38FullUsable.diagonalBad
#print axioms CurrentAdditive.V38FullUsable.diagonal_mass_ge
#print axioms CurrentAdditive.V38FullUsable.diagonalBad_card_lt
#print axioms CurrentAdditive.V38FullUsable.bad
#print axioms CurrentAdditive.V38FullUsable.usable_masses
#print axioms CurrentAdditive.V38FullUsable.bad_card_lt
#print axioms CurrentAdditive.V38FullUsable.sum_bad_card_lt
#print axioms CurrentAdditive.V38FullUsable.initialState
#print axioms CurrentAdditive.V38FullUsable.initial_count
#print axioms CurrentAdditive.V38FullUsable.initial_reaches
#print axioms CurrentAdditive.V38FullUsable.initial_mass
