import CurrentAdditive.V38Matrix
import Paper2.RestorationRowPartition

/-! Actual two-family protected mass at a deterministic Alice frontier.
All events use the original laws. No probability is reassigned after a row
has survived or reached a particular destination. -/

namespace CurrentAdditive.V39ProtectedAccounting

open Paper2 Paper2.SourceMatrix
open scoped BigOperators

variable {Y D : Type*} [Fintype Y] [Fintype D]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₂]

noncomputable def referenceLoss (ν : PositiveRationalLaw Y)
    (keep : V38Matrix.TaggedColumn q₁ q₂ s Y → Prop)
    (dest : V38Matrix.TaggedColumn q₁ q₂ s Y → D) (own : D) : ℝ :=
  1 - (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob
    (fun Z => keep (.inl Z) ∧ dest (.inl Z) = own)

noncomputable def protectedDeleted (ν : PositiveRationalLaw Y)
    (keep : V38Matrix.TaggedColumn q₁ q₂ s Y → Prop) : ℝ :=
  (1/256 : ℝ) * (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
    (fun j => ¬ keep (.inr j))

noncomputable def protectedOutgoing (ν : PositiveRationalLaw Y)
    (keep : V38Matrix.TaggedColumn q₁ q₂ s Y → Prop)
    (dest : V38Matrix.TaggedColumn q₁ q₂ s Y → D) (own : D) : ℝ :=
  (1/256 : ℝ) * (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
    (fun j => keep (.inr j) ∧ dest (.inr j) ≠ own)

private theorem three_way_probability {Z : Type*} [Fintype Z]
    (μ : FiniteLaw Z) (keep : Z → Prop) (dest : Z → D) (own : D) :
    μ.prob (fun z => keep z ∧ dest z = own) + μ.prob (fun z => ¬ keep z) +
      μ.prob (fun z => keep z ∧ dest z ≠ own) = 1 := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ = ∑ z, μ.weight z := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hk : keep z <;> by_cases hd : dest z = own <;> simp [hk,hd]
    _ = 1 := μ.total

/-- Reference loss, initially deleted protected mass, and surviving
protected rows sent elsewhere partition the missing part of this copy. -/
theorem missing_copy_identity (ν : PositiveRationalLaw Y)
    (keep : V38Matrix.TaggedColumn q₁ q₂ s Y → Prop)
    (dest : V38Matrix.TaggedColumn q₁ q₂ s Y → D) (own : D) :
    (255/256 : ℝ) * referenceLoss ν keep dest own +
      protectedDeleted ν keep + protectedOutgoing ν keep dest own =
      1 - (V38Matrix.taggedLaw ν).toFiniteLaw.prob
        (fun Z => keep Z ∧ dest Z = own) := by
  rw [V38Matrix.tagged_prob]
  have hp := three_way_probability
    (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw
    (fun j => keep (.inr j)) (fun j => dest (.inr j)) own
  unfold referenceLoss protectedDeleted protectedOutgoing
  linarith

/-- Every surviving protected input outside its owner has exactly one
other-owner or nonowner destination. This uses an actual total destination
function; the receiving partition is proved, not assumed. -/
theorem outgoing_partition [DecidableEq D] (ν : PositiveRationalLaw Y)
    (keep : V38Matrix.TaggedColumn q₁ q₂ s Y → Prop)
    (dest : V38Matrix.TaggedColumn q₁ q₂ s Y → D)
    (owners : Finset D) (own : D) (ho : own ∈ owners) :
    protectedOutgoing ν keep dest own =
      (∑ d ∈ owners.erase own, (1/256 : ℝ) *
        (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
          (fun j => keep (.inr j) ∧ dest (.inr j) = d)) +
      (∑ d ∈ Finset.univ \ owners, (1/256 : ℝ) *
        (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
          (fun j => keep (.inr j) ∧ dest (.inr j) = d)) := by
  classical
  unfold protectedOutgoing FiniteLaw.prob
  simp_rw [Finset.mul_sum]
  conv_rhs =>
    lhs
    rw [Finset.sum_comm]
  conv_rhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hk : keep (.inr j)
  · by_cases hd : dest (.inr j) = own
    · simp [hk,hd,ho]
    · by_cases hm : dest (.inr j) ∈ owners <;> simp [hk,hd,hm]
  · simp [hk]

/-- The numerical contradiction in v39 lem:protected-accounting. The
arguments are the totals of the actual partition above; the strict owner
loss and source receipt estimates remain explicit inputs to this scalar
step. No communication lower bound is assumed here. -/
theorem accounting_contradiction
    (w count : ℕ) (η P a ε other exceptional q x : ℝ)
    (hw : 2 ≤ w) (hη : 0 < η) (hcount : (3/4 : ℝ) * w ≤ count)
    (hcountle : count ≤ w)
    (hP : (count : ℝ) * η < P + a + (255/256 : ℝ) * ε)
    (ha : a ≤ η/16) (hε : ε ≤ η/(8*(255/256 : ℝ)))
    (hexc : exceptional ≤ η*w/16)
    (hother : other ≤ (w : ℝ) *
      (2*(1/256 : ℝ)*w*q*x + (1/256 : ℝ)*η/(2*(255/256 : ℝ))))
    (hwidth : 4*(1/256 : ℝ)*w*q*x ≤ η/32)
    (hpartition : P = other + exceptional) : False := by
  have hwpos : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hw2 : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hscaled : 2*(1/256 : ℝ)*w*q*x ≤ η/64 := by linarith
  have hother' : other ≤ (w : ℝ) * (η/64 + η/510) := by
    calc
      other ≤ (w : ℝ) *
          (2*(1/256 : ℝ)*w*q*x + (1/256 : ℝ)*η/(2*(255/256 : ℝ))) := hother
      _ ≤ (w : ℝ) * (η/64 + η/510) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hwpos)
        have hconstant : (1/256 : ℝ)*η/(2*(255/256 : ℝ)) = η/510 := by ring
        rw [hconstant]
        linarith
  have hPa : (3/4 : ℝ)*w*η < P + η/16 + η/8 := by
    have hc : (3/4 : ℝ)*w*η ≤ (count : ℝ)*η :=
      mul_le_mul_of_nonneg_right hcount (le_of_lt hη)
    have hconstant : η/(8*(255/256 : ℝ)) = (32/255 : ℝ)*η := by ring
    rw [hconstant] at hε
    linarith
  nlinarith

end CurrentAdditive.V39ProtectedAccounting

#print axioms CurrentAdditive.V39ProtectedAccounting.missing_copy_identity
#print axioms CurrentAdditive.V39ProtectedAccounting.outgoing_partition
#print axioms CurrentAdditive.V39ProtectedAccounting.accounting_contradiction
