import CurrentAdditive.QuarticTMVectorBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront

theorem threshold_bound27 (Δ n m k : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hmpos : 0 < m)
    (hm : m ≤ Δ * n) :
    2 ^ TMFront.thrVal k
      (vector27 n m (Nat.clog 2 n) Δ γ) ≤
      ((n + 2) ^ baseExponent Δ γ) ^ (220 * k + 45) := by
  let V0 := (n + 2) ^ baseExponent Δ γ
  let vv := vector27 n m (Nat.clog 2 n) Δ γ
  have hN : 2 ≤ n + 2 := by omega
  have hE : 1 ≤ baseExponent Δ γ := by
    dsimp [baseExponent]
    omega
  have hV02 : 2 ≤ V0 := by
    have h1 : 2 ^ 1 ≤ (n + 2) ^ 1 := Nat.pow_le_pow_left hN 1
    have h2 : (n + 2) ^ 1 ≤ (n + 2) ^ baseExponent Δ γ :=
      Nat.pow_le_pow_right (by omega) hE
    simpa only [pow_one, V0] using h1.trans h2
  have hv0 : ∀ i, vv i ≤ V0 := by
    simpa only [vv, V0] using vector_bound27 Δ n m γ hγ hΔ hn hmpos hm
  have hcl : ∀ i, 2 ^ Nat.clog 2 (vv i) ≤ V0 ^ 44 := by
    intro i
    have h := Paper2.FrontClock13.two_pow_clog_V hV02
      (show vv i ≤ V0 ^ 1 by simpa using hv0 i)
    exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))
  simpa only [vv, V0] using Paper2.FrontClock13.thr_bounds k vv V0 hV02 hcl

#print axioms threshold_bound27

end Paper2.CurrentAdditive.QuarticTMClockRepair
