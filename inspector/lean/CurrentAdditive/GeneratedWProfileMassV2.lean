import CurrentAdditive.GeneratedWUpperAtSchedule
import CurrentAdditive.IndexedProfileRung

/-! The ordinary tagged columns retain a quantitative share of a rectangle
for the literal indexed internal interlace. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def WordinarySelected (V : Set (Fin w × Column src)) :
    Set (Fin w × (src.outer.Label × src.gamma.Label)) :=
  fun pz => (pz.1, Column.ordinary pz.2) ∈ V

theorem ordinarySelected_mass (V : Set (Fin w × Column src)) (β : ℝ)
    (hV : β ≤ (((PositiveRationalLaw.uniform (Fin w)).prod
      (columnLaw src)).toFiniteLaw).prob (· ∈ V)) :
    (β - (1 - 127/128)) / (127/128 : ℝ) ≤
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (ordinaryLaw src)).toFiniteLaw).prob
          (· ∈ WordinarySelected src V) := by
  classical
  let ν := (PositiveRationalLaw.uniform (Fin w)).toFiniteLaw
  let χ := (columnLaw src).toFiniteLaw
  let ο := (ordinaryLaw src).toFiniteLaw
  let O : Fin w → Set (src.outer.Label × src.gamma.Label) :=
    fun i => {z | (i, Column.ordinary z) ∈ V}
  have hpoint (i : Fin w) : χ.prob (fun z => (i,z) ∈ V) ≤
      (127/128 : ℝ) * ο.prob (· ∈ O i) + (1 - 127/128) := by
    have hf := src.outer.law.toFiniteLaw.prob_le_one
      (fun z => (i, Column.fixedTail z) ∈ V)
    have hd := (diagonalLaw src).toFiniteLaw.prob_le_one
      (fun z => (i, Column.diagonal z) ∈ V)
    have hs := column_prob_split src (fun z => (i,z) ∈ V)
    change χ.prob (fun z => (i,z) ∈ V) =
      (127/128 : ℝ) * ο.prob (fun z => (i,Column.ordinary z) ∈ V) +
      (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
        (fun z => (i,Column.fixedTail z) ∈ V) +
      (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
        (fun z => (i,Column.diagonal z) ∈ V) at hs
    change χ.prob (fun z => (i,z) ∈ V) ≤
      (127/128 : ℝ) * ο.prob (fun z => (i,Column.ordinary z) ∈ V) +
      (1-127/128)
    rw [hs]
    linarith
  have hsum : (∑ i : Fin w, ν.weight i * χ.prob (fun z => (i,z) ∈ V)) ≤
      (127/128 : ℝ) *
        (∑ i : Fin w, ν.weight i * ο.prob (· ∈ O i)) +
        (1 - 127/128) := by
    calc
      _ ≤ ∑ i : Fin w, ν.weight i *
        ((127/128 : ℝ) * ο.prob (· ∈ O i) + (1 - 127/128)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hpoint i) (ν.nonneg i)
      _ = (127/128 : ℝ) *
          (∑ i : Fin w, ν.weight i * ο.prob (· ∈ O i)) +
          (1 - 127/128) := by
            calc
              _ = ∑ i : Fin w, ((127/128 : ℝ) *
                    (ν.weight i * ο.prob (· ∈ O i)) +
                    (1-127/128) * ν.weight i) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
              _ = _ := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
                      ← Finset.mul_sum, ν.total]
                    ring
  have hprod : (((PositiveRationalLaw.uniform (Fin w)).prod
      (columnLaw src)).toFiniteLaw).prob (· ∈ V) =
      ∑ i : Fin w, ν.weight i * χ.prob (fun z => (i,z) ∈ V) := by
    simpa only [ν, χ, PositiveRationalLaw.toFiniteLaw_prod] using
      (FiniteLaw.prod_prob ν χ (fun i z => (i,z) ∈ V))
  have hO : (((PositiveRationalLaw.uniform (Fin w)).prod
      (ordinaryLaw src)).toFiniteLaw).prob
        (· ∈ WordinarySelected src V) =
      ∑ i : Fin w, ν.weight i * ο.prob (· ∈ O i) := by
    simpa only [ν, ο, PositiveRationalLaw.toFiniteLaw_prod,
      WordinarySelected, O] using
      (FiniteLaw.prod_prob ν ο
        (fun i z => (i, Column.ordinary z) ∈ V))
  rw [hO]
  rw [hprod] at hV
  linarith [hV, hsum]

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinarySelected_mass
