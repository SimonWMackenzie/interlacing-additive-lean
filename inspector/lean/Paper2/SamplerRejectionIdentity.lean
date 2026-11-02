import Paper2.SamplerDrawCount
import Paper2.SamplingBounds

namespace Paper2.SamplerRejectionIdentity

theorem clog_scaled (N : Nat) (hN : 0 < N) :
    Nat.clog 2 (2^12 * N) = 12 + Nat.clog 2 N := by
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
    rw [pow_add]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide : 1 < 2) N)
  · by_cases hone : N = 1
    · subst N
      simpa using (Nat.clog_pow 2 12 (by decide : 1 < 2)).symm.le
    · have hN' : 1 < N := by omega
      have hm : 0 < Nat.clog 2 N := Nat.clog_pos (by decide) hN'
      have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hN'
      have hpow : 2 ^ (12 + (Nat.clog 2 N).pred) < 2^12 * N := by
        rw [pow_add]
        exact Nat.mul_lt_mul_of_pos_left hp (by decide : 0 < 2^12)
      have hstep : 12 + (Nat.clog 2 N).pred < Nat.clog 2 (2^12*N) :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hpow
      have hpred : (Nat.clog 2 N).pred + 1 = Nat.clog 2 N :=
        Nat.succ_pred_eq_of_pos hm
      omega

theorem rejection_eq (N : Nat) (hN : 0 < N) :
    Paper2.rejectionAttemptCap N = 13 + Nat.clog 2 N := by
  rw [Paper2.rejectionAttemptCap, clog_scaled N hN]
  omega

#print axioms rejection_eq

end Paper2.SamplerRejectionIdentity
