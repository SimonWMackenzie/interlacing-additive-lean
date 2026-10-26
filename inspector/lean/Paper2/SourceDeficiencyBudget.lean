import Paper2.SourceDeficiency
import Paper2.SourceDeficiencyTemplate

/-!
# The actual union of the two coordinate deficits

Frozen v12 Section 4, `src:near-full`, the definition and total bound for
`b_j`. The two finsets here are the actual deficient template projections
and actual deficient diagonal fibres. Their union is counted directly.
The further schedule comparison with the source witness density is separate.
-/

namespace Paper2.SourceDeficiency

open scoped BigOperators
open SourceMatrix SourceLawBinding

variable {X Y : Type*} [Fintype X] [Fintype Y] {q₁ q₂ s : ℕ}

/-- Both deficit conditions at one branch, retaining original coordinate labels. -/
noncomputable def branchDeficient (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (A : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) : Finset (Fin q₂) :=
  SourceDeficiencyTemplate.deficientAt μ A xcap ∪ diagonalDeficient ν U

@[simp] theorem mem_branchDeficient (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (A : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (α : Fin q₂) :
    α ∈ branchDeficient μ ν A U xcap ↔
      α ∈ SourceDeficiencyTemplate.deficientAt μ A xcap ∨ α ∈ diagonalDeficient ν U := by
  simp [branchDeficient]

/-- Every nondeficient coordinate has all the required template blocks and
the original retained diagonal word support of mass at least `3/4`. -/
theorem usable_coordinate_masses (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (A : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap : ℝ) (α : Fin q₂) (hα : α ∉ branchDeficient μ ν A U xcap) :
    (∀ r : Fin q₁, xcap ≤ μ.toFiniteLaw.prob
      (fun x => SourceDeficiencyTemplate.projectedAt A α (r, x))) ∧
    3 / 4 ≤ (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
      (fun γ => TaggedColumn.diagonal (α, γ) ∈ U) := by
  classical
  have hh := not_or.mp ((not_congr (mem_branchDeficient μ ν A U xcap α)).mp hα)
  refine ⟨fun r => SourceDeficiencyTemplate.block_mass_ge_of_not_mem μ A xcap α hh.1 r, ?_⟩
  simpa only [diagonalDeficient, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hh.2

theorem branchDeficient_card_lt [NeZero q₁] [NeZero q₂]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (A : Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap η : ℝ) (hxcap : xcap ≤ 1 / 8) (hη : 0 < η)
    (hA : (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob A)
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    ((branchDeficient μ ν A U xcap).card : ℝ) < 8 * q₁ + 1024 * η * q₂ := by
  have ht := SourceDeficiencyTemplate.deficientAt_card_lt μ A xcap hxcap hA
  have hd := diagonalDeficient_card_lt ν U η hη hU
  have hu : ((branchDeficient μ ν A U xcap).card : ℝ) ≤
      (SourceDeficiencyTemplate.deficientAt μ A xcap).card + (diagonalDeficient ν U).card := by
    exact_mod_cast Finset.card_union_le
      (SourceDeficiencyTemplate.deficientAt μ A xcap) (diagonalDeficient ν U)
  have ht' : ((SourceDeficiencyTemplate.deficientAt μ A xcap).card : ℝ) < 8 * q₁ := by
    exact_mod_cast ht
  linarith

/-- The actual total deficit before the scheduled witness-density comparison. -/
theorem sum_branchDeficient_card_lt [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (A : Fin s → Template q₁ q₂ X → Prop) (U : Set (TaggedColumn q₁ q₂ s Y))
    (xcap η : ℝ) (hxcap : xcap ≤ 1 / 8) (hη : 0 < η)
    (hA : ∀ j, (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (A j))
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    (∑ j, ((branchDeficient μ ν (A j) U xcap).card : ℝ)) <
      8 * s * q₁ + 1024 * s * η * q₂ := by
  have hh := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin s)).Nonempty)
    (fun j _ => branchDeficient_card_lt μ ν (A j) U xcap η hxcap hη (hA j) hU)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  calc
    _ < (s : ℝ) * (8 * q₁ + 1024 * η * q₂) := hh
    _ = _ := by ring

end Paper2.SourceDeficiency

#print axioms Paper2.SourceDeficiency.usable_coordinate_masses
#print axioms Paper2.SourceDeficiency.branchDeficient_card_lt
#print axioms Paper2.SourceDeficiency.sum_branchDeficient_card_lt
