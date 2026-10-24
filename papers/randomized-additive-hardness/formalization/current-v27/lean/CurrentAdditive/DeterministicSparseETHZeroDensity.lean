import CurrentAdditive.DeterministicSparseETH
import Paper2.AFrontSparse

/-! The zero-density case of the chosen sparse ETH carrier is decidable by
the inherited physical density checker. This makes the carrier's existential
clause-density constant provably positive without changing its definition. -/

namespace CurrentAdditive.DeterministicSparseETHZeroDensity

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicSparseETH

noncomputable def zeroAlgorithm : Algorithm where
  machine := AFront.Sparse.sparseCheck 0
  answer := AFront.Sparse.sparseAnswer 0
  time w := 260 * (w.length+1)^3
  run := AFront.Sparse.sparseCheck_outputs_poly 0

theorem zero_sparse_decider : SparseDecider 0 zeroAlgorithm := by
  constructor
  · intro Φ hsp
    have hempty : Φ.val.clauses = [] := by
      have : Φ.val.clauses.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    have hsat : EncodedCNF.Satisfiable Φ.val := by
      have heq : Φ.val = ⟨Φ.val.variables, []⟩ := by
        cases hΦ : Φ.val with
        | mk n cs =>
            have hcs : cs = [] := by simpa only [hΦ] using hempty
            simp [hcs]
      rw [heq]
      exact EncodedCNF.empty_satisfiable _
    change AFront.Sparse.sparseAnswer 0 (EncodedCNF.encode Φ.val) = true ↔ _
    rw [AFront.Sparse.sparseAnswer_encode 0 Φ.val Φ.property]
    simp [hempty, hsat]
  · intro ε hε
    refine ⟨260, 3, 0, ?_⟩
    intro Φ _ _
    have hceil : 1 ≤ ⌈(2:ℝ)^(ε * (Φ.val.variables:ℝ))⌉₊ :=
      Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    change 260 * ((EncodedCNF.encode Φ.val).length+1)^3 ≤
      260 * ⌈(2:ℝ)^(ε * (Φ.val.variables:ℝ))⌉₊ *
        ((EncodedCNF.encode Φ.val).length+1)^3
    have h := Nat.mul_le_mul_right
      (((EncodedCNF.encode Φ.val).length+1)^3) hceil
    have h' := Nat.mul_le_mul_left 260 h
    simpa only [one_mul, Nat.mul_assoc] using h'

theorem holds_density_positive (hETH : Holds) :
    ∃ cs : ℕ, 1 ≤ cs ∧ ¬∃ A : Algorithm, SparseDecider cs A := by
  obtain ⟨cs, hno⟩ := hETH
  refine ⟨cs, ?_, hno⟩
  by_contra hnot
  have hzero : cs = 0 := by omega
  subst cs
  exact hno ⟨zeroAlgorithm, zero_sparse_decider⟩

theorem sparse_witness_guard (cs cutoff : ℕ)
    (hcs : 1 ≤ cs) (hcutoff : 2 ≤ cutoff) :
    2 ≤ cs * cutoff := by nlinarith

theorem contradiction_of_positive_deciders (hETH : Holds)
    (hall : ∀ cs, 1 ≤ cs → ∃ A : Algorithm, SparseDecider cs A) : False := by
  obtain ⟨cs, hcs, hno⟩ := holds_density_positive hETH
  exact hno (hall cs hcs)

#print axioms zero_sparse_decider
#print axioms holds_density_positive
#print axioms sparse_witness_guard
#print axioms contradiction_of_positive_deciders

end CurrentAdditive.DeterministicSparseETHZeroDensity
