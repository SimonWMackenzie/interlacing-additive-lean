import CurrentAdditive.DeterministicAdmissibility

/-! The exact Appendix I public dyadic choice at the input floor used in
v27 `det:eth`. The graph reduction's polynomial vertex bound and fixed
graph constants remain source-reduction facts. -/

namespace CurrentAdditive.DeterministicEndpointSchedule

open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicParameters

/-- Choosing the public floor above both the graph vertices and the formula
mvar yields the actual Appendix I schedule and a polynomial-size
parameter. The coefficient `g+1` is explicit and uniform in the formula. -/
theorem public_schedule_for_eth
    (vertices mvar edges Δ g : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hedges : 0 < edges)
    (hdegree : 2*edges ≤ Δ*vertices)
    (hg : 1 ≤ g) (hmvar : 2 ≤ mvar)
    (hgraph : vertices ≤ mvar^g)
    (hcutoff : sourceCutoffSize Δ γ ≤ mvar) :
    let L := publicLog (max vertices mvar) Δ γ
    mvar ≤ N L ∧
    Admissible L Δ vertices edges sourceC128Ceil γ ∧
    N L ≤ mvar^(g+1) := by
  let floor := max vertices mvar
  let L := publicLog floor Δ γ
  have hsched := public_schedule_at_floor floor vertices edges Δ γ
    hΔ hγ hedges hdegree (le_max_left vertices mvar)
  change floor ≤ N L ∧
    Admissible L Δ vertices edges sourceC128Ceil γ ∧
    N L ≤ 2 * max floor (sourceCutoffSize Δ γ) at hsched
  have hvarpow : mvar ≤ mvar^g := by
    calc
      mvar = mvar^1 := by simp
      _ ≤ mvar^g := Nat.pow_le_pow_right (by omega) hg
  have hfloor : floor ≤ mvar^g := max_le hgraph hvarpow
  have hmax : max floor (sourceCutoffSize Δ γ) ≤ mvar^g :=
    max_le hfloor (hcutoff.trans hvarpow)
  have htwo : 2 * mvar^g ≤ mvar^(g+1) := by
    rw [pow_succ]
    calc
      2*mvar^g = mvar^g*2 := by ring
      _ ≤ mvar^g*mvar := Nat.mul_le_mul_left _ hmvar
  exact ⟨(le_max_right vertices mvar).trans hsched.1,
    hsched.2.1, (hsched.2.2.trans (Nat.mul_le_mul_left 2 hmax)).trans htwo⟩

#print axioms public_schedule_for_eth

end CurrentAdditive.DeterministicEndpointSchedule
