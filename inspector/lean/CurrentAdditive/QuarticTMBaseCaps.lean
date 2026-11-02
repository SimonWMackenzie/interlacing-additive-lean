import CurrentAdditive.QuarticTMGenericBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper

theorem base_caps27 (Δ n : ℕ) (γ : ℚ) :
    let V0 := (n + 2) ^ baseExponent Δ γ
    2 ≤ V0 ∧ 2 ^ 32 ≤ V0 ∧
      UnaryBinaryEncoding.coefficient + 6 ≤ V0 ∧
      Nat.clog 2 n ≤ V0 := by
  let N := n + 2
  let V0 := N ^ baseExponent Δ γ
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hE : 32 ≤ baseExponent Δ γ := by dsimp [baseExponent]; omega
  have hV02 : 2 ≤ V0 := by
    have h1 : 2 ^ 1 ≤ N ^ 1 := Nat.pow_le_pow_left hN 1
    have h2 : N ^ 1 ≤ N ^ baseExponent Δ γ :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa only [pow_one, V0] using h1.trans h2
  have hV032 : 2 ^ 32 ≤ V0 := by
    have h1 : 2 ^ 32 ≤ N ^ 32 := Nat.pow_le_pow_left hN 32
    have h2 : N ^ 32 ≤ N ^ baseExponent Δ γ :=
      Nat.pow_le_pow_right (by omega) hE
    exact h1.trans h2
  have hc0 : UnaryBinaryEncoding.coefficient + 6 ≤ V0 := by
    have hK : UnaryBinaryEncoding.coefficient + 6 ≤ baseCoefficient Δ γ := by
      dsimp [baseCoefficient]
      omega
    have hKN : baseCoefficient Δ γ ≤ V0 := by
      have h1 : baseCoefficient Δ γ ≤ N ^ (baseCoefficient Δ γ) :=
        (Nat.lt_two_pow_self).le.trans
          (Nat.pow_le_pow_left hN (baseCoefficient Δ γ))
      have h2 : N ^ (baseCoefficient Δ γ) ≤ V0 := by
        dsimp [V0, baseExponent]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact h1.trans h2
    exact hK.trans hKN
  have hL0 : Nat.clog 2 n ≤ V0 := by
    have h0 : Nat.clog 2 n ≤ n :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    have h1 : n ≤ N := by dsimp [N]; omega
    have h2 : N ≤ V0 := by
      have h := Nat.pow_le_pow_right (show 1 ≤ N by omega)
        (show 1 ≤ baseExponent Δ γ by omega)
      simpa only [pow_one, V0] using h
    exact h0.trans (h1.trans h2)
  exact ⟨hV02, hV032, hc0, hL0⟩

#print axioms base_caps27

end Paper2.CurrentAdditive.QuarticTMClockRepair
