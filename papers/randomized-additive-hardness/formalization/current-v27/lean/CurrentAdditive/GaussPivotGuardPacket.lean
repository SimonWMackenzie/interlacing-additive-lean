import CurrentAdditive.GaussPivotGuardRun

/-! The checked unary terminal guard on the physically prepared Gauss packet. -/

namespace CurrentAdditive.GaussPivotGuardPacket

open EthInapproximability.CurrentPaper

noncomputable section

variable {m k : Nat} (s : GaussControlTrace.State m k)

theorem prepared_guard :
    ∃ t ≤ GaussPivotGuardRun.clock s.r m,
      GaussPivotGuard32.run t
        (GaussPivotGuard32.initial (GaussPivotPrepBank.prepared s)) =
        ⟨some (if s.r < m then .active else .terminal),
          .choose (some (decide (s.r < m))),
          GaussPivotPrepBank.prepared s⟩ := by
  have h13 : (GaussPivotPrepBank.prepared s) 13 =
      List.replicate m true := by
    simpa using GaussPivotPrepBank.prepared_exact s 13
  have h30 : (GaussPivotPrepBank.prepared s) 30 =
      List.replicate s.r true := by
    simpa using GaussPivotPrepBank.prepared_exact s 30
  have h20 : (GaussPivotPrepBank.prepared s) 20 = [] := by
    simpa using GaussPivotPrepBank.prepared_exact s 20
  have h21 : (GaussPivotPrepBank.prepared s) 21 = [] := by
    simpa using GaussPivotPrepBank.prepared_exact s 21
  have h22 : (GaussPivotPrepBank.prepared s) 22 = [] := by
    simpa using GaussPivotPrepBank.prepared_exact s 22
  have h29 : (GaussPivotPrepBank.prepared s) 29 = [] := by
    simpa using GaussPivotPrepBank.prepared_exact s 29
  exact GaussPivotGuardRun.outputs
    (GaussPivotPrepBank.prepared s) s.r m h30 h13 h20 h21 h22 h29

#print axioms prepared_guard

end
end CurrentAdditive.GaussPivotGuardPacket
