import CurrentAdditive.V38Matrix
import Paper2.ProtectedDensityGroups

/-! Current res:incoming has one protected family. Direct diagonal receipt
avoids the obsolete factor-two choice between two protected families. -/

namespace CurrentAdditive.V39IncomingDensity

open Paper2 Paper2.ProtectedDensityGroups
open scoped BigOperators

variable {Ordinary Diagonal : Type*} [Fintype Diagonal]

noncomputable def density (ν : FiniteLaw Diagonal) (w : ℕ)
    (R : Set (Fin w × (Ordinary ⊕ Diagonal))) (origins : Finset (Fin w))
    (i : Fin w) : ℝ := by
  classical
  exact if i ∈ origins then ν.prob (fun z => (i,Sum.inr z) ∈ R) else 0

noncomputable def receipt (ν : FiniteLaw Diagonal) (w : ℕ)
    (R : Set (Fin w × (Ordinary ⊕ Diagonal))) (i : Fin w) : ℝ :=
  (1/256 : ℝ) * ν.prob (fun z => (i,Sum.inr z) ∈ R)

theorem density_nonneg (ν : FiniteLaw Diagonal) (w : ℕ)
    (R : Set (Fin w × (Ordinary ⊕ Diagonal))) (I : Finset (Fin w)) (i : Fin w) :
    0 ≤ density ν w R I i := by
  classical
  unfold density
  split_ifs <;> first | exact ν.prob_nonneg _ | norm_num

theorem density_le_one (ν : FiniteLaw Diagonal) (w : ℕ)
    (R : Set (Fin w × (Ordinary ⊕ Diagonal))) (I : Finset (Fin w)) (i : Fin w) :
    density ν w R I i ≤ 1 := by
  classical
  unfold density
  split_ifs <;> first | exact ν.prob_le_one _ | norm_num

theorem total_receipt (ν : FiniteLaw Diagonal) (w : ℕ)
    (R : Set (Fin w × (Ordinary ⊕ Diagonal))) (I : Finset (Fin w)) :
    (∑ i ∈ I, receipt ν w R i) = (1/256 : ℝ) * ∑ i, density ν w R I i := by
  classical
  simp [receipt,density,Finset.mul_sum]

/-- The source's sharp 512*mu receipt threshold directly yields a class
with m*delta>=256*s*kappa and m>=256*s*kappa. No protected-tag split is
performed. All rows and probability masses are actual retained diagonals. -/
theorem sharp_density_group (ν : FiniteLaw Diagonal) (w r s κ : ℕ)
    (R : Set (Fin w × (Ordinary ⊕ Diagonal))) (I : Finset (Fin w))
    (hw : w = 2^r) (hs : 0 < s) (hκ : 0 < κ)
    (hmass : 512*(1/256 : ℝ)*(r+2)*s*κ ≤ ∑ i ∈ I, receipt ν w R i) :
    let d := density ν w R I
    let D₀ : ℝ := ∑ i, d i
    512*(r+2 : ℝ)*s*κ ≤ D₀ ∧
    ∃ j : Fin (r+2),
      let δ : ℝ := (1/2 : ℝ)^j.val
      let V := dyadicGroup d D₀ j
      V ⊆ I ∧ 0 < δ ∧ δ ≤ 1 ∧ D₀/(2*(w : ℝ)) ≤ δ ∧
      (∀ i ∈ V, δ/2 < d i ∧ d i ≤ δ) ∧
      256*(s : ℝ)*κ ≤ (V.card : ℝ)*δ ∧
      256*(s : ℝ)*κ ≤ (V.card : ℝ) := by
  classical
  let d := density ν w R I
  let D₀ : ℝ := ∑ i, d i
  have hlarge : 512*(r+2 : ℝ)*s*κ ≤ D₀ := by
    rw [total_receipt] at hmass
    dsimp [D₀,d]
    linarith
  have hDone : 1 ≤ D₀ := by
    have hr : (1 : ℝ) ≤ r+2 := by exact_mod_cast (by omega : 1 ≤ r+2)
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hκ' : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
    have hp : (1 : ℝ) ≤ (r+2 : ℝ)*s*κ := by
      calc
        (1 : ℝ) = 1*1*1 := by ring
        _ ≤ (r+2 : ℝ)*s*κ := by gcongr
    nlinarith
  obtain ⟨j,hδpos,hδone,hδlow,hrow,hcount⟩ :=
    density_group d hw (density_nonneg ν w R I) (density_le_one ν w R I)
      D₀ rfl hDone
  let V := dyadicGroup d D₀ j
  have hsize : 256*(s : ℝ)*κ ≤ (V.card : ℝ)*(1/2 : ℝ)^j.val := by
    have hscaled : 256*(s : ℝ)*κ ≤ D₀/(2*(r+2 : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*(r+2 : ℝ))).2
      nlinarith
    exact hscaled.trans hcount
  refine ⟨hlarge,j,?_,hδpos,hδone,hδlow,hrow,hsize,?_⟩
  · intro i hi
    by_contra hn
    have hz : d i = 0 := by simp [d,density,hn]
    change density ν w R I i = 0 at hz
    have hm := (Finset.mem_filter.mp hi).2
    rw [hz] at hm
    have hp : (0 : ℝ) < (1/2 : ℝ)^(j.val+1) := by positivity
    linarith [hm.2.1]
  · have hc : (V.card : ℝ)*(1/2 : ℝ)^j.val ≤ V.card := by
      nlinarith [mul_nonneg (Nat.cast_nonneg V.card) (sub_nonneg.mpr hδone)]
    linarith

end CurrentAdditive.V39IncomingDensity

#print axioms CurrentAdditive.V39IncomingDensity.total_receipt
#print axioms CurrentAdditive.V39IncomingDensity.sharp_density_group
