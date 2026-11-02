import Mathlib.Tactic
import Mathlib.Data.Nat.Size

/-! Numerical iteration bound for the physical Euclidean controller. -/
namespace CurrentAdditive.EuclidCount

private theorem two_remainders_half (a b : Nat) (hb : 0 < b)
    (hr : 0 < a % b) : 2 * (b % (a % b)) < b := by
  let r := a % b
  change 2 * (b % r) < b
  have hrb : r < b := Nat.mod_lt _ hb
  have hrpos : 0 < r := hr
  have hs : b % r < r := Nat.mod_lt _ hrpos
  by_cases hsmall : 2 * r ≤ b
  · omega
  · have hbr : r ≤ b := by omega
    have hsub : b - r < r := by omega
    have hmod : b % r = b - r := by
      rw [Nat.mod_eq_sub_mod hbr]
      exact Nat.mod_eq_of_lt hsub
    rw [hmod]
    omega

theorem two_remainders_size_drop (a b : Nat) (hb : 0 < b)
    (hr : 0 < a % b) : Nat.size (b % (a % b)) < Nat.size b := by
  have hhalf := two_remainders_half a b hb hr
  have hsize : 0 < Nat.size b := Nat.size_pos.mpr hb
  let k := Nat.size b - 1
  have hk : Nat.size b = k + 1 := by omega
  have hp := Nat.lt_size_self b
  rw [hk, pow_succ] at hp
  have hs : b % (a % b) < 2 ^ k := by omega
  have hlen := Nat.size_le.mpr hs
  omega

def steps (a : Nat) : Nat → Nat
  | 0 => 0
  | b + 1 => 1 + steps (b + 1) (a % (b + 1))
termination_by b => b
decreasing_by
  exact Nat.mod_lt _ (by omega)

theorem steps_zero (a : Nat) : steps a 0 = 0 := by simp [steps]

theorem steps_pos (a b : Nat) (hb : 0 < b) :
    steps a b = 1 + steps b (a % b) := by
  cases b with
  | zero => omega
  | succ b => simp [steps]

theorem steps_bound (a b : Nat) : steps a b ≤ 2 * Nat.size b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      by_cases hb : b = 0
      · subst b; simp [steps_zero]
      · have hbpos : 0 < b := by omega
        let r := a % b
        have hrb : r < b := Nat.mod_lt _ hbpos
        rw [steps_pos a b hbpos]
        by_cases hr : r = 0
        · simp [r, hr, steps_zero]
          have hs : 0 < Nat.size b := Nat.size_pos.mpr hbpos
          omega
        · have hrpos : 0 < r := by omega
          have hsr : b % r < r := Nat.mod_lt _ hrpos
          rw [steps_pos b r hrpos]
          have hrec := ih (b % r) (by omega) r
          have hdrop := two_remainders_size_drop a b hbpos hrpos
          dsimp [r] at hrec hdrop ⊢
          omega

end CurrentAdditive.EuclidCount
