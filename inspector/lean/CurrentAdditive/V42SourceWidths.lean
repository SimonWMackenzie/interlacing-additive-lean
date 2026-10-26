import CurrentAdditive.V42CommonMargins

namespace CurrentAdditive.V42Schedule

theorem s_ge_four (k : ℕ) (hk : 2 ≤ k) : 4 ≤ s k :=
  Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk

def sourceQ0 (k m : ℕ) : ℕ := V38Schedule.pow2Ceil (4*s k*m)
def repetition (k b m : ℕ) : ℕ := q₂ k b/sourceQ0 k m

theorem sourceQ0_dvd (k b m : ℕ) (hw : sourceQ0 k m ≤ q₂ k b) :
    sourceQ0 k m ∣ q₂ k b := by
  have hc : 4*s k*m ≤ 2^(b+2*k) :=
    (V39PublicSchedule.pow2Ceil_lower (4*s k*m)).trans hw
  have he : Nat.clog 2 (4*s k*m) ≤ b+2*k :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hc
  exact Nat.pow_dvd_pow 2 he

theorem repetition_exact (k b m : ℕ) (hw : sourceQ0 k m ≤ q₂ k b) :
    q₂ k b=sourceQ0 k m*repetition k b m :=
  (Nat.mul_div_cancel' (sourceQ0_dvd k b m hw)).symm

theorem repetition_pos (k b m : ℕ) (hw : sourceQ0 k m ≤ q₂ k b) :
    0 < repetition k b m := by
  have he := repetition_exact k b m hw
  have hp := q₂_pos k b
  by_contra h
  have hz : repetition k b m=0 := by omega
  rw [hz,Nat.mul_zero] at he
  omega

theorem item_labels_fit (n m k b : ℕ) (hn : 0 < n) (hs : 4 ≤ s k)
    (hm : n≤2*m) (hw : 4*s k*m≤q₂ k b) :
    4*s k*(n+s k-3) ≤ 2*s k*q₂ k b := by
  have hsn : n+s k-3 ≤ s k*n := by
    have h1 := Nat.mul_le_mul_left (s k-1) hn
    have he : s k*n=(s k-1)*n+n := by
      calc
        s k*n=((s k-1)+1)*n := by congr 1; omega
        _=(s k-1)*n+n := by ring
    omega
  have hq : 2*s k*n ≤ q₂ k b := by nlinarith
  have hq2 : 2*(n+s k-3) ≤ q₂ k b := by nlinarith only [hsn,hq]
  nlinarith

#print axioms sourceQ0_dvd
#print axioms repetition_exact
#print axioms repetition_pos
#print axioms item_labels_fit

end CurrentAdditive.V42Schedule
