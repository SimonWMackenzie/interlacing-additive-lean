import EthInapproximability.CurrentPaper.G5bRoundClockNamed

/-!
# Absorbing `poly(n, |enc G|) + 2^{O(p)}` into one power `Y^N` (private lane owner:b-g5-3)

Pure arithmetic support for segment 1. For `Y ≥ 2` and atoms `2^p, n, ell ≤ Y`, the writer clock
plus the round rest `(n + ell + 2)^Cw + 2^(Cw p) + roundRest C ps ps3 K ell p + 1` is at most
`Y^N` for ONE exponent `N` depending only on the constants `Cw C ps ps3 K` (quantified first).
-/

noncomputable section


namespace EthInapproximability.CurrentPaper.G5cPowBound

theorem const_le {Y : ℕ} (hY : 2 ≤ Y) (c : ℕ) : c ≤ Y ^ c :=
  (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hY c)

theorem add_le {Y a b i j : ℕ} (hY : 2 ≤ Y) (ha : a ≤ Y ^ i) (hb : b ≤ Y ^ j) :
    a + b ≤ Y ^ (i + j + 1) := by
  have h1 : Y ^ i ≤ Y ^ (i + j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : Y ^ j ≤ Y ^ (i + j) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 * Y ^ (i + j) ≤ Y ^ (i + j) * Y := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hY
  rw [pow_succ]; omega

theorem mul_le {Y a b i j : ℕ} (ha : a ≤ Y ^ i) (hb : b ≤ Y ^ j) : a * b ≤ Y ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem pow_le {Y a i : ℕ} (m : ℕ) (ha : a ≤ Y ^ i) : a ^ m ≤ Y ^ (i * m) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left ha m

theorem atomC {Y p : ℕ} (hP : 2 ^ p ≤ Y) (C : ℕ) : 2 ^ (C * p) ≤ Y ^ C := by
  rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hP C

/-- The ONE power bound of the writer clock plus the round rest. -/
theorem clock_le_pow [Fintype OuterLevel0Bridge.BStack]
    [Fintype MatrixTableInterlaceProtectedBridge.Label] (Cw C ps ps3 K : ℕ) :
    ∃ N : ℕ, ∀ Y p n ell : ℕ, 2 ≤ Y → 2 ^ p ≤ Y → n ≤ Y → ell ≤ Y →
      ((n + ell + 2) ^ Cw + 2 ^ (Cw * p)) +
          G5bRoundClockNamed.roundRest C ps ps3 K ell p + 1 ≤ Y ^ N := by
  apply Exists.intro
  intro Y p n ell hY hP hn hell
  have hP1 : 2 ^ p ≤ Y ^ 1 := by rw [pow_one]; exact hP
  have hn1 : n ≤ Y ^ 1 := by rw [pow_one]; exact hn
  have hell1 : ell ≤ Y ^ 1 := by rw [pow_one]; exact hell
  unfold G5bRoundClockNamed.roundRest
  repeat (first
    | with_reducible exact hP1 | with_reducible exact hn1 | with_reducible exact hell1
    | with_reducible apply atomC hP | with_reducible apply const_le hY
    | with_reducible apply add_le hY | with_reducible apply mul_le | with_reducible apply pow_le)

#print axioms clock_le_pow

end EthInapproximability.CurrentPaper.G5cPowBound
