import CurrentAdditive.QuarticHeaderClockEnvelope

/-! A tape-independent graph-size cap for the actual encoded v27 square. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

theorem squareEncodedLength_le_poly27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k)
    (t : (select27 hn edge Δ γ k).Tape) :
    squareEncodedLength27 hn edge Δ γ k ≤
      (n + 2) ^ (333 * (k + 1)) := by
  let P := (n + 2) ^ (332 * (k + 1))
  have hh := headerWord_length_le_poly27 hn edge Δ γ k hk t
  have hout := outputBits27_length_le_poly hn edge Δ γ k hk t
  have hlen := squareEncodedLength_le27 hn edge Δ γ k t
  have heq := headerWord_length27 hn edge Δ γ k t
  have houtP : (outputBits27 hn edge Δ γ k t).length ≤ P := by
    exact hout.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hbound : squareEncodedLength27 hn edge Δ γ k ≤ 2 * P := by
    change (Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance
        (selectedInstance27 hn edge Δ γ k t))).length =
      headerLength27 hn edge Δ γ k at heq
    dsimp [P] at *
    omega
  have hfactor : 2 ≤ (n + 2) ^ (k + 1) := by
    have h0 : 2 ≤ n + 2 := by omega
    have h1 : (n + 2) ^ 1 ≤ (n + 2) ^ (k + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simp only [pow_one] at h1
    exact h0.trans h1
  have hmul := Nat.mul_le_mul_left P hfactor
  calc
    _ ≤ 2 * P := hbound
    _ ≤ P * (n + 2) ^ (k + 1) := by nlinarith only [hmul]
    _ = (n + 2) ^ (333 * (k + 1)) := by
      dsimp [P]
      rw [← pow_add]
      congr 1
      omega

#print axioms squareEncodedLength_le_poly27

end Paper2.CurrentAdditive.QuarticClassEndpoint
