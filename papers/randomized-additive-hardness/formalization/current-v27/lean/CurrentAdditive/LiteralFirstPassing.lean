import CurrentAdditive.ExactAdmissibility
import CurrentAdditive.BoundedDyadicSearch

/-! A total, bounded search for the literal first passing v35 dyadic size.
The v27 strengthened cutoff is used only to cap the scan, not returned as
the public parameter. -/
namespace CurrentAdditive.PublicScheduleLiteralFirstPassing

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.PublicScheduleExactAdmissibility
open CurrentAdditive.PublicScheduleBoundedSearch

def exactPublicLog (n m Δ : ℕ) (γ : ℚ) : ℕ :=
  selectedLog (fun L => literalTest L n m Δ γ) 0 (publicLog n Δ γ)

theorem exactPublicLog_spec (n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    literalTest (exactPublicLog n m Δ γ) n m Δ γ = true ∧
    (∀ k < exactPublicLog n m Δ γ,
      literalTest k n m Δ γ = false) ∧
    N (exactPublicLog n m Δ γ) ≤
      2 * max n (sourceCutoffSize Δ γ) := by
  have hcap := public_schedule n m Δ γ hΔ hγ hm hdegree
  have hpass : literalTest (publicLog n Δ γ) n m Δ γ = true :=
    production_admissible_passes_literal (publicLog n Δ γ) n m Δ γ
      hΔ hγ hcap.1 hcap.2.1
  have hs := selectedLog_spec (fun L => literalTest L n m Δ γ)
    0 (publicLog n Δ γ) (Nat.zero_le _) hpass
  have hsize : N (exactPublicLog n m Δ γ) ≤ N (publicLog n Δ γ) := by
    unfold N
    exact Nat.pow_le_pow_right (by decide) hs.2.1
  refine ⟨hs.2.2.1, ?_, hsize.trans hcap.2.2⟩
  intro k hk
  exact hs.2.2.2 k (Nat.zero_le _) hk

theorem exactPublicLog_floor (n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    n ≤ N (exactPublicLog n m Δ γ) := by
  have h := (literalTest_iff _ _ _ _ _).mp
    (exactPublicLog_spec n m Δ γ hΔ hγ hm hdegree).1
  exact h.1

#print axioms exactPublicLog_spec
#print axioms exactPublicLog_floor

end CurrentAdditive.PublicScheduleLiteralFirstPassing
