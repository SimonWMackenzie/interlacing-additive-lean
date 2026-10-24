import CurrentAdditive.QuarticHeaderClockBound

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2

theorem clsTime_mono27 (C : Paper2.SelectedTape.Algorithm)
    {X Y X' Y' : ℕ} (hX : X ≤ X') (hY : Y ≤ Y') :
    Paper2.AEth5.clsTime C X Y ≤ Paper2.AEth5.clsTime C X' Y' := by
  unfold Paper2.AEth5.clsTime
  have ht := Paper2.AEth5.trunc_timeBound_mono C.cR C.dR
    Paper2.SelectedTape.Bind.idC Paper2.SelectedTape.Bind.idD
    Paper2.SelectedTape.Bind.idMachine.pushBound (by omega :
      2 * X + 1 + Y ≤ 2 * X' + 1 + Y')
  have hpR : (X + 1) ^ C.dR ≤ (X' + 1) ^ C.dR :=
    Nat.pow_le_pow_left (by omega) _
  have hpT : (X + 1) ^ C.dT ≤ (X' + 1) ^ C.dT :=
    Nat.pow_le_pow_left (by omega) _
  have hpR' := Nat.mul_le_mul_left C.cR hpR
  have hpT' := Nat.mul_le_mul_left C.cT hpT
  omega

#print axioms clsTime_mono27

end Paper2.CurrentAdditive.QuarticClassEndpoint
