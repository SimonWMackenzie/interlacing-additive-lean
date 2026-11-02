import CurrentAdditive.GaussMatrixSupportClock

/-! One uniform full-support pivot rewrite budget for every actual state. -/

namespace CurrentAdditive.GaussUniformMatrixSupport

open CurrentAdditive.GaussNestedMatrixMap
open CurrentAdditive.GaussMatrixClockPolynomial
open EthInapproximability.CurrentPaper

theorem actual_pivot_matrix_full_support {m k Mparam : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hk : k ≤ m*Mparam)
    (t : Nat) (ht : t < k)
    (hr : (CurrentAdditive.GaussControlTrace.after
      (fun i j => (A i j : ℚ)) t).r < m)
    (hc : (CurrentAdditive.GaussControlTrace.after
      (fun i j => (A i j : ℚ)) t).c < k)
    (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      (CurrentAdditive.GaussControlTrace.after
        (fun i j => (A i j : ℚ)) t).B
      (CurrentAdditive.GaussControlTrace.after
        (fun i j => (A i j : ℚ)) t).r
      ⟨(CurrentAdditive.GaussControlTrace.after
        (fun i j => (A i j : ℚ)) t).c, hc⟩ = some pivot) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := CurrentAdditive.GaussControlTrace.after Aq t
    (matrixMachine GaussCellSubtractCall.machine).OutputsWithin
      (encodeNested
        (GaussAdaptedMatrixMap.adaptedMatrix
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
      (CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.GaussControlTrace.step s).B)
      (polyMatrixTime GaussCellSubtractCall.machine m (m*Mparam)
        (GaussUniformMatrixActual.requestCap m)
        (GaussUniformMatrixActual.resultCap m)
        (GaussCellGlobalClock.coefficient *
          (GaussUniformMatrixActual.requestCap m+1)^
            GaussUniformMatrixRun.exponent)) := by
  have h := GaussUniformMatrixGlobal.actual_pivot_matrix_global
    A h01 t ht hr hc pivot hp
  apply BitMachine.outputsWithin_mono _ h
  exact GaussMatrixSupportClock.full_support_matrix_clock
    GaussCellSubtractCall.machine m k Mparam
    (GaussUniformMatrixActual.requestCap m)
    (GaussUniformMatrixActual.resultCap m)
    (GaussCellGlobalClock.coefficient *
      (GaussUniformMatrixActual.requestCap m+1)^
        GaussUniformMatrixRun.exponent) hk

#print axioms actual_pivot_matrix_full_support

end CurrentAdditive.GaussUniformMatrixSupport
