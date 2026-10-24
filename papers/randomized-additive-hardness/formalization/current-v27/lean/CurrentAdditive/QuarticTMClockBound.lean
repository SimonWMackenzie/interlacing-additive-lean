import CurrentAdditive.QuarticTMExponent

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront

/-- Literal v27 physical threshold and sample-dimension machine clock. -/
theorem tmBd_poly27 (Δ n m k : ℕ) (γ : ℚ) (hγ : 0 < γ)
    (hΔ : 0 < Δ) (hn : 0 < n) (hmpos : 0 < m)
    (hm : m ≤ Δ * n) :
    TMFront.tmBd k (vector27 n m (Nat.clog 2 n) Δ γ) (Nat.clog 2 n) ≤
      (n + 2) ^ (clockExponent Δ γ * (k + 1)) := by
  let V0 := (n + 2) ^ baseExponent Δ γ
  let vv := vector27 n m (Nat.clog 2 n) Δ γ
  have hv0 : ∀ i, vv i ≤ V0 := by
    simpa only [vv, V0] using vector_bound27 Δ n m γ hγ hΔ hn hmpos hm
  have hThr : 2 ^ TMFront.thrVal k vv ≤ V0 ^ (220 * k + 45) := by
    simpa only [vv, V0] using
      threshold_bound27 Δ n m k γ hγ hΔ hn hmpos hm
  have hcaps := base_caps27 Δ n γ
  change 2 ≤ V0 ∧ 2 ^ 32 ≤ V0 ∧
    UnaryBinaryEncoding.coefficient + 6 ≤ V0 ∧ Nat.clog 2 n ≤ V0 at hcaps
  rcases hcaps with ⟨hV02, hV032, hc0, hL0⟩
  have htm := tmBd_generic k (Nat.clog 2 n) V0 vv
    hV02 hV032 hc0 hv0 hL0 hThr
  have hpow : (V0 ^ (266 * (k + 1))) ^ 8 =
      (n + 2) ^ (clockExponent Δ γ * (k + 1)) := by
    simpa only [V0, clockExponent] using
      power_identity (n + 2) (baseExponent Δ γ) k
  calc
    TMFront.tmBd k (vector27 n m (Nat.clog 2 n) Δ γ) (Nat.clog 2 n)
        ≤ (V0 ^ (266 * (k + 1))) ^ 8 := htm
    _ = (n + 2) ^ (clockExponent Δ γ * (k + 1)) := hpow

#print axioms tmBd_poly27

end Paper2.CurrentAdditive.QuarticTMClockRepair
