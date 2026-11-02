import CurrentAdditive.QuarticSourceBankSize

/-! The fixed square-header clock is quadratic in one common size cap. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

theorem squareHeaderClock_le_of_atoms27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (Φ : EncodedCNF.Formula) (Z : ℕ)
    (he : (EncodedCNF.encode Φ).length ≤ Z)
    (hN : Φ.variables ≤ Z)
    (hk : Paper2.Unit4Shell.Asymptotics.kOf Φ.variables ≤ Z)
    (hL : squareEncodedLength27 hn edge Δ γ
      (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) ≤ Z) :
    squareHeaderClock27 hn edge Δ γ Φ ≤
      100 * (Paper2.Unit4Shell.KofFront.BK + 1) * (Z + 1) ^ 2 := by
  have hclock := squareHeaderClock_bound27 hn edge Δ γ Φ
  dsimp only at hclock
  let Q := (Z + 1) ^ 2
  have hQ : Z + 1 ≤ Q := by
    dsimp [Q]
    nlinarith
  have hNQ : (Φ.variables + 1) ^ 2 ≤ Q :=
    Nat.pow_le_pow_left (by omega) _
  have hKQ : (2 * Paper2.Unit4Shell.Asymptotics.kOf Φ.variables + 1 +
      squareEncodedLength27 hn edge Δ γ
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) + 1) ^ 2 ≤
      16 * Q := by
    have hbase : 2 * Paper2.Unit4Shell.Asymptotics.kOf Φ.variables + 1 +
      squareEncodedLength27 hn edge Δ γ
        (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) + 1 ≤
        4 * (Z + 1) := by omega
    have hp := Nat.pow_le_pow_left hbase 2
    calc
      _ ≤ (4 * (Z + 1)) ^ 2 := hp
      _ = 16 * Q := by dsimp [Q]; ring
  have hBK := Nat.mul_le_mul_left Paper2.Unit4Shell.KofFront.BK hNQ
  have htarget : 100 * (Paper2.Unit4Shell.KofFront.BK + 1) * Q =
      100 * (Paper2.Unit4Shell.KofFront.BK * Q) + 100 * Q := by ring
  rw [show 100 * (Paper2.Unit4Shell.KofFront.BK + 1) *
      (Z + 1) ^ 2 = 100 * (Paper2.Unit4Shell.KofFront.BK + 1) * Q by rfl,
    htarget]
  omega

#print axioms squareHeaderClock_le_of_atoms27

end Paper2.CurrentAdditive.QuarticClassEndpoint
