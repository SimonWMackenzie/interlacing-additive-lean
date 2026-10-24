import CurrentAdditive.GeneratedNearFullSeparated
import CurrentAdditive.DeterministicIndexedProfileMass

/-! Retention of the actual indexed row and column laws gives the
conditional populations used by source-specific separation. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {I G A X Y : Type*} [Fintype I] [Fintype G] [Fintype A]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

private theorem prob_add_complement {Z : Type*} [Fintype Z]
    (μ : Paper2.FiniteLaw Z) (E : Z → Prop) :
    μ.prob E + μ.prob (fun z => ¬ E z) = 1 := by
  classical
  calc
    μ.prob E + μ.prob (fun z => ¬ E z) = μ.prob (fun _ => True) := by
      simp only [Paper2.FiniteLaw.prob, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : E z <;> simp [h]
    _ = 1 := μ.prob_true

theorem retained_fixed_tail_of_total
    (U : Set (Column src)) (η : ℝ)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hη : 256 * η ≤ 1 / 100) :
    (99 / 100 : ℝ) ≤ src.outer.law.toFiniteLaw.prob
      (fun js => (Column.fixedTail js : Column src) ∈ U) := by
  have hordinary := (ordinaryLaw src).toFiniteLaw.prob_le_one
    (fun z => Column.ordinary z ∈ U)
  have hdiag := (diagonalLaw src).toFiniteLaw.prob_le_one
    (fun z => Column.diagonal z ∈ U)
  rw [column_prob_split] at hU
  linarith

theorem retained_each_template_bin_of_total
    (μI : PositiveRationalLaw (G × (A ⊕ I)))
    (V : Set (Row (I := G × (A ⊕ I)) src)) (η : ℝ)
    (hV : 1 - η ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ V))
    (hη : (256 / 255 : ℝ) * s * η ≤ 1 / 1000)
    (p : Fin s) :
    (999 / 1000 : ℝ) ≤ src.inner.law.toFiniteLaw.prob
      (fun z => (Sum.inl (p,z) : Row (I := G × (A ⊕ I)) src) ∈ V) := by
  let ν := src.inner.law.toFiniteLaw
  let τ := (templateRowLaw src).toFiniteLaw
  let E : Fin s × src.inner.Label → Prop := fun pz => Sum.inl pz ∈ V
  have htpl : 1 - (256 / 255 : ℝ) * η ≤ τ.prob E := by
    have h := template_retained src μI V (1-η) hV
    dsimp [τ, E]
    convert h using 1 <;> ring
  have hnot : τ.prob (fun pz => ¬ E pz) ≤ (256 / 255 : ℝ) * η := by
    have ht := prob_add_complement τ E
    linarith
  have hmono : τ.prob (fun pz => pz.1 = p ∧ ¬ E pz) ≤
      τ.prob (fun pz => ¬ E pz) :=
    τ.prob_mono (fun _ h => h.2)
  have hbin : τ.prob (fun pz => pz.1 = p ∧ ¬ E pz) =
      ((s : ℝ)⁻¹) * ν.prob (fun z => ¬ E (p,z)) := by
    rw [show τ = ((PositiveRationalLaw.uniform (Fin s)).toFiniteLaw).prod ν
      from PositiveRationalLaw.toFiniteLaw_prod _ _]
    have he : (fun pz : Fin s × src.inner.Label => pz.1 = p ∧ ¬ E pz) =
        (fun pz => pz.1 = p ∧ ¬ E (p,pz.2)) := by
      funext ⟨p',z⟩
      by_cases hp : p' = p <;> simp [hp]
    rw [he]
    have h := Paper2.FiniteLaw.prod_prob_fixed_fst
      (PositiveRationalLaw.uniform (Fin s)).toFiniteLaw ν p
      (fun z => ¬ E (p,z))
    simpa [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform] using h
  have hsum := prob_add_complement ν (fun z => E (p,z))
  have hspos : (0 : ℝ) < s := by exact_mod_cast NeZero.pos s
  rw [hbin] at hmono
  have hmul : ν.prob (fun z => ¬ E (p,z)) ≤
      (256 / 255 : ℝ) * s * η := by
    have := hmono.trans hnot
    have hh := mul_le_mul_of_nonneg_left this (le_of_lt hspos)
    calc
      ν.prob (fun z => ¬ E (p,z)) =
          (s : ℝ) * ((s : ℝ)⁻¹ * ν.prob (fun z => ¬ E (p,z))) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hspos), one_mul]
      _ ≤ (s : ℝ) * ((256 / 255 : ℝ) * η) := hh
      _ = (256 / 255 : ℝ) * s * η := by ring
  dsimp [E] at hsum hmul
  linarith

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.retained_fixed_tail_of_total
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.retained_each_template_bin_of_total
