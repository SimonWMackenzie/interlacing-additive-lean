import CurrentAdditive.V39IndexedProtectedAccounting

/-! v39 robustness.tex, lem:protected-accounting.  All receipts are sums of
the same actual surviving-input events and the same total destination map.
The per-destination source estimates are local inputs; no conservation or
alignment certificate is an input. -/

namespace CurrentAdditive.V39IndexedTwoFamilySummation

open Paper2 Paper2.SourceMatrix CurrentAdditive.V39IndexedProtectedAccounting
open scoped BigOperators Classical

variable {X Y I T : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : CurrentAdditive.DeterministicIndexedMatrix.Sources
    (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

variable {D : Type*} [Fintype D] [DecidableEq D]


theorem conservation_contradiction
    (keep : Fin w → V38IndexedTwoTag.Column src → Prop)
    (dest : Fin w → V38IndexedTwoTag.Column src → D)
    (owners : Finset D) (origin : D → Fin w) (capacity : D → ℕ)
    (η K q x : ℝ)
    (hw : 2 ≤ w) (hη : 0 < η) (hK : 0 ≤ K)
    (hcount : (3/4 : ℝ)*w ≤ owners.card) (hcountle : owners.card ≤ w)
    (hmiss : ∀ d ∈ owners, η < 1 - (V38IndexedTwoTag.law src).toFiniteLaw.prob
      (fun c => keep (origin d) c ∧ dest (origin d) c = d))
    (hdeleted : (∑ d ∈ owners, protectedDeleted src (keep (origin d))) ≤ η/16)
    (hloss : (∑ d ∈ owners,
      referenceLoss src (keep (origin d)) (dest (origin d)) d) ≤ η/(8*(255/256 : ℝ)))
    (hincoming : ∀ v ∉ owners,
      (∑ d ∈ owners, (1/256 : ℝ) * (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
        (fun j => keep (origin d) (.inr j) ∧ dest (origin d) (.inr j) = v)) ≤
          K * capacity v)
    (hexceptional : K * (∑ v ∈ Finset.univ \ owners, (capacity v : ℝ)) ≤ η*w/16)
    (hforeign : ∀ d ∈ owners, ∀ v ∈ owners, d ≠ v →
      (1/256 : ℝ) * (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
        (fun j => keep (origin d) (.inr j) ∧ dest (origin d) (.inr j) = v) ≤
      (1/256 : ℝ) * (2*q*x + 4*referenceLoss src (keep (origin v)) (dest (origin v)) v))
    (hqx : 0 ≤ q*x) (hwidth : 4*(1/256 : ℝ)*w*q*x ≤ η/32) : False := by
  classical
  let receipt : D → D → ℝ := fun d v =>
    (1/256 : ℝ) * (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
      (fun j => keep (origin d) (.inr j) ∧ dest (origin d) (.inr j) = v)
  let ε := fun d => referenceLoss src (keep (origin d)) (dest (origin d)) d
  let P := ∑ d ∈ owners, protectedOutgoing src (keep (origin d)) (dest (origin d)) d
  let a := ∑ d ∈ owners, protectedDeleted src (keep (origin d))
  let other := ∑ d ∈ owners, ∑ v ∈ owners.erase d, receipt d v
  let exceptional := ∑ d ∈ owners, ∑ v ∈ Finset.univ \ owners, receipt d v
  have hpart : P = other + exceptional := by
    unfold P other exceptional
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact outgoing_partition src (keep (origin d)) (dest (origin d)) owners d hd
  have hεnonneg (d : D) : 0 ≤ ε d := by
    exact sub_nonneg.mpr ((CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw.prob_le_one _)
  have hreceiptnonneg (d v : D) : 0 ≤ receipt d v := by
    exact mul_nonneg (by norm_num) ((CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob_nonneg _)
  have hother : other ≤ (w : ℝ) *
      (2*(1/256 : ℝ)*w*q*x + (1/256 : ℝ)*η/(2*(255/256 : ℝ))) := by
    have hrow (d : D) (hd : d ∈ owners) :
        (∑ v ∈ owners.erase d, receipt d v) ≤
          ∑ v ∈ owners, (1/256 : ℝ)*(2*q*x+4*ε v) := by
      calc
        _ ≤ ∑ v ∈ owners.erase d, (1/256 : ℝ)*(2*q*x+4*ε v) := by
          apply Finset.sum_le_sum
          intro v hv
          exact hforeign d hd v (Finset.mem_of_mem_erase hv)
            (Finset.ne_of_mem_erase hv).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun v _ _ => by dsimp only [ε]; nlinarith [hεnonneg v])
    have hsum := Finset.sum_le_sum hrow
    have hcalc : (∑ v ∈ owners, (1/256 : ℝ)*(2*q*x+4*ε v)) =
        (1/256 : ℝ)*(2*owners.card*q*x+4*∑ v ∈ owners, ε v) := by
      calc
        _ = ∑ v ∈ owners, ((1/128 : ℝ)*q*x+(1/64 : ℝ)*ε v) := by
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    have hc : (owners.card : ℝ) ≤ w := by exact_mod_cast hcountle
    have hbound : (∑ v ∈ owners, (1/256 : ℝ)*(2*q*x+4*ε v)) ≤
        2*(1/256 : ℝ)*w*q*x+(1/256 : ℝ)*η/(2*(255/256 : ℝ)) := by
      rw [hcalc]
      have hm := mul_le_mul_of_nonneg_right hc hqx
      change (∑ v ∈ owners, ε v) ≤ η/(8*(255/256 : ℝ)) at hloss
      simp only [div_eq_mul_inv] at hloss ⊢
      norm_num at hloss ⊢
      simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
      nlinarith
    have hn : 0 ≤ (∑ v ∈ owners, (1/256 : ℝ)*(2*q*x+4*ε v)) := by
      exact Finset.sum_nonneg (fun v _ => by nlinarith [hεnonneg v])
    dsimp only [other] at *
    calc
      _ ≤ owners.card * (∑ v ∈ owners, (1/256 : ℝ)*(2*q*x+4*ε v)) := by
        simpa using hsum
      _ ≤ (w : ℝ) * (∑ v ∈ owners, (1/256 : ℝ)*(2*q*x+4*ε v)) :=
        mul_le_mul_of_nonneg_right hc hn
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg w)
  have hexc : exceptional ≤ η*w/16 := by
    dsimp only [exceptional]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ v ∈ Finset.univ \ owners, K*capacity v := by
        apply Finset.sum_le_sum
        intro v hv
        exact hincoming v (Finset.mem_sdiff.mp hv).2
      _ = K * (∑ v ∈ Finset.univ \ owners, (capacity v : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := hexceptional
  have hone : owners.Nonempty := by
    have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
    have hcpos : 0 < owners.card := by
      by_contra hn
      have hc0 : owners.card = 0 := by omega
      rw [hc0] at hcount
      norm_num at hcount
      simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
      linarith
    exact Finset.card_pos.mp hcpos
  have hstrict : (owners.card : ℝ)*η < P+a+(255/256 : ℝ)*(∑ d ∈ owners, ε d) := by
    have hsum := Finset.sum_lt_sum_of_nonempty hone (fun d hd => hmiss d hd)
    have hident (d : D) : 1-(V38IndexedTwoTag.law src).toFiniteLaw.prob
        (fun c => keep (origin d) c ∧ dest (origin d) c=d) =
        protectedOutgoing src (keep (origin d)) (dest (origin d)) d +
        protectedDeleted src (keep (origin d)) + (255/256 : ℝ)*ε d := by
      have h := missing_copy_identity src (keep (origin d)) (dest (origin d)) d
      dsimp only [ε]
      simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
      linarith
    simp_rw [hident] at hsum
    simpa [P, a, Finset.sum_add_distrib, Finset.mul_sum] using hsum
  exact CurrentAdditive.V39ProtectedAccounting.accounting_contradiction w owners.card η P a (∑ d ∈ owners, ε d)
    other exceptional q x hw hη hcount hcountle hstrict hdeleted hloss hexc
    hother hwidth hpart

end CurrentAdditive.V39IndexedTwoFamilySummation

#print axioms CurrentAdditive.V39IndexedTwoFamilySummation.conservation_contradiction
