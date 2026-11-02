import CurrentAdditive.SmallBiasPublicDegree

/-! The exact unary degree can be printed by arithmetic on the cut and
suffix depth. This identity avoids a separate generic logarithm machine. -/

namespace CurrentAdditive.SmallBias.YaoDegreeArithmetic

theorem public_degree_closed (b t : ℕ) :
    publicFieldDegree b t =
      publicBiasExponent b t + b + 2 * t + 1 := by
  let A := publicBiasExponent b t
  let e := A + b + 2 * t
  have hp : 0 < 2 ^ (2 * t) := pow_pos (by omega : 0 < (2 : ℕ)) _
  have htarget : publicFieldTarget b t =
      2 ^ (A + b) * (2 ^ (2 * t) + 1) := by
    change (2 ^ b * (2 ^ t * 2 ^ t + 1)) * 2 ^ A = _
    rw [pow_add]
    rw [show 2 ^ (2 * t) = 2 ^ t * 2 ^ t by
      rw [show 2 * t = t + t by omega, pow_add]]
    ring
  have hlow : 2 ^ e < publicFieldTarget b t := by
    rw [htarget]
    change 2 ^ (A + b + 2 * t) < _
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (pow_pos (by decide) _)
  have hupp : publicFieldTarget b t ≤ 2 ^ (e + 1) := by
    rw [htarget]
    have hsmall : 2 ^ (2 * t) + 1 ≤ 2 ^ (2 * t) * 2 := by
      have : 1 ≤ 2 ^ (2 * t) := by omega
      omega
    calc
      2 ^ (A + b) * (2 ^ (2 * t) + 1) ≤
          2 ^ (A + b) * (2 ^ (2 * t) * 2) :=
        Nat.mul_le_mul_left _ hsmall
      _ = 2 ^ (e + 1) := by
        simp only [e, pow_succ, pow_add]
        ring
  have hl : e < Nat.clog 2 (publicFieldTarget b t) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2 : ℕ))).2 hlow
  have hu : Nat.clog 2 (publicFieldTarget b t) ≤ e + 1 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2 hupp
  unfold publicFieldDegree
  omega

#print axioms public_degree_closed

end CurrentAdditive.SmallBias.YaoDegreeArithmetic
