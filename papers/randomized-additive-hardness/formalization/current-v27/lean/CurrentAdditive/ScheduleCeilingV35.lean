import Paper2.RestorationCoverParameters

/-! Private bridge between the selected v35 paper's real logarithmic ceiling
and the natural upper logarithm used by the frozen finite packet. -/

namespace FiniteV35Schedule

open Paper2.RestorationCoverParameters

/-- The paper writes `b_theta = ceil(log_2 (1/theta))` for
`theta = 1/(320Q)`. -/
noncomputable def paperBTheta (Q : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (1 / theta Q))

theorem paperBTheta_eq_b {Q : ℕ} (hQ : 0 < Q) :
    paperBTheta Q = b Q := by
  have hN : (0 : ℝ) < (320 * Q : ℕ) := by
    exact_mod_cast (by omega : 0 < 320 * Q)
  have htheta : 1 / theta Q = ((320 * Q : ℕ) : ℝ) := by
    unfold theta
    field_simp
  simp only [paperBTheta, htheta, b]
  exact Real.natCeil_logb_natCast 2 (320 * Q)

#print axioms paperBTheta_eq_b

end FiniteV35Schedule
