import CurrentAdditive.GaussCellGlobalClock

set_option maxHeartbeats 2000000

/-! One coefficient, chosen once for the fixed cell program, controls every
full physical matrix rewrite. -/

namespace CurrentAdditive.GaussUniformMatrixGlobal

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussNestedMatrixMap

noncomputable def bound (x : List Bool) : Nat :=
  GaussCellGlobalClock.coefficient *
    (x.length+1)^GaussUniformMatrixRun.exponent

theorem physical_pivot_matrix_global {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c, hc⟩ = some pivot)
    (L R : Nat)
    (hin : ∀ i j,
      (GaussUniformCellAlgebra.adaptedSourceCellPacket
        s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j).length ≤ L)
    (hout : ∀ i j,
      (CurrentAdditive.CodeDCodec.encodeRawRat
        (CurrentAdditive.GaussPhysical.rawOfRat
          (CurrentAdditive.SequentialTotality.clearTyped
            (CurrentAdditive.SequentialTotality.swapTyped
              s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j))).length ≤ R) :
    (matrixMachine GaussCellSubtractCall.machine).OutputsWithin
      (encodeNested
        (GaussAdaptedMatrixMap.adaptedMatrix
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
      (CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.GaussControlTrace.step s).B)
      (GaussMatrixClockPolynomial.polyMatrixTime
        GaussCellSubtractCall.machine m k L R
        (GaussCellGlobalClock.coefficient *
          (L+1)^GaussUniformMatrixRun.exponent)) := by
  let f := GaussCellGlobalClock.result
  have hclock := GaussCellGlobalClock.computes
  have hnum := GaussAdaptedPivotStep.selected_pivot_numerator
    s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ hp
  have hf (i : Fin m) (j : Fin k) :
      f (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j) =
        CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat
            (CurrentAdditive.SequentialTotality.clearTyped
              (CurrentAdditive.SequentialTotality.swapTyped
                s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j)) := by
    obtain ⟨T,hvalid⟩ :=
      GaussUniformCellAlgebra.adapted_source_cell_outputs
        s.B ⟨s.r, hr⟩ pivot i ⟨s.c, hc⟩ j hnum
    exact BitMachine.outputsWithin_unique
      GaussCellSubtractCall.machine (hclock _) hvalid
  have hcell (i : Fin m) (j : Fin k) :
      GaussCellSubtractCall.machine.OutputsWithin
        (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j)
        (f (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j))
        (bound (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j)) := by
    simpa only [bound] using hclock _
  have hrun := GaussAdaptedPivotStep.physical_pivot_step
    s hr hc pivot hp GaussCellSubtractCall.machine f bound hcell hf
  have htime (i : Fin m) (j : Fin k) :
      bound (GaussUniformCellAlgebra.adaptedSourceCellPacket
        s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j) ≤
        GaussCellGlobalClock.coefficient *
          (L+1)^GaussUniformMatrixRun.exponent := by
    unfold bound
    gcongr
    exact hin i j
  have hbound := GaussAdaptedMatrixMap.adapted_clock_le
    s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩
    GaussCellSubtractCall.machine f bound L R
    (GaussCellGlobalClock.coefficient *
      (L+1)^GaussUniformMatrixRun.exponent)
    hin (by intro i j; rw [hf]; exact hout i j) htime
  apply BitMachine.outputsWithin_mono _ hrun
  exact hbound.trans
    (GaussMatrixClockPolynomial.matrixTime_le
      GaussCellSubtractCall.machine m k L R
      (GaussCellGlobalClock.coefficient *
        (L+1)^GaussUniformMatrixRun.exponent))

/-- The same fixed coefficient works for every actual state and every chosen
pivot, so the k-step loop can sum one uniform polynomial budget. -/
theorem actual_pivot_matrix_global {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
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
      (GaussMatrixClockPolynomial.polyMatrixTime
        GaussCellSubtractCall.machine m k
        (GaussUniformMatrixActual.requestCap m)
        (GaussUniformMatrixActual.resultCap m)
        (GaussCellGlobalClock.coefficient *
          (GaussUniformMatrixActual.requestCap m+1)^
            GaussUniformMatrixRun.exponent)) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := CurrentAdditive.GaussControlTrace.after Aq t
  change s.r < m at hr
  change s.c < k at hc
  change CurrentAdditive.SequentialTotality.pivotTyped
    s.B s.r ⟨s.c, hc⟩ = some pivot at hp
  have hB := congrArg CurrentAdditive.EliminationEntryBounds.CursorState.B
    (CurrentAdditive.GaussControlTrace.after_cursor Aq t)
  change s.B = (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B at hB
  have hnext : (CurrentAdditive.GaussControlTrace.step s).B =
      (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq (t+1)).B := by
    have hsucc : CurrentAdditive.GaussControlTrace.step s =
        CurrentAdditive.GaussControlTrace.after Aq (t+1) := by
      simp only [s, CurrentAdditive.GaussControlTrace.after,
        Function.iterate_succ_apply']
    rw [hsucc]
    exact congrArg CurrentAdditive.EliminationEntryBounds.CursorState.B
      (CurrentAdditive.GaussControlTrace.after_cursor Aq (t+1))
  have hin (i : Fin m) (j : Fin k) :
      (GaussUniformCellAlgebra.adaptedSourceCellPacket
        s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j).length ≤
          GaussUniformMatrixActual.requestCap m := by
    rw [hB]
    simpa only [GaussUniformMatrixActual.requestCap,
      GaussUniformMatrixActual.entryCap, Aq] using
      (GaussUniformCellClock.actual_adapted_source_packet_length
        A h01 t (Nat.le_of_lt ht) ⟨s.r, hr⟩ pivot i ⟨s.c, hc⟩ j)
  have hout (i : Fin m) (j : Fin k) :
      (CurrentAdditive.CodeDCodec.encodeRawRat
        (CurrentAdditive.GaussPhysical.rawOfRat
          (CurrentAdditive.SequentialTotality.clearTyped
            (CurrentAdditive.SequentialTotality.swapTyped
              s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j))).length ≤
        GaussUniformMatrixActual.resultCap m := by
    have hclear :
        CurrentAdditive.SequentialTotality.clearTyped
          (CurrentAdditive.SequentialTotality.swapTyped
            s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j =
          (CurrentAdditive.GaussControlTrace.step s).B i j := by
      simp [CurrentAdditive.GaussControlTrace.step, hr, hc, hp,
        CurrentAdditive.MaterializedGauss.materialize_eq]
    rw [hclear, hnext]
    simpa only [GaussUniformMatrixActual.resultCap,
      GaussUniformMatrixActual.entryCap, Aq] using
      (CurrentAdditive.GaussPhysical.actualGauss_cell_code_length
        A h01 (t+1) (Nat.succ_le_of_lt ht) i j)
  exact physical_pivot_matrix_global s hr hc pivot hp
    (GaussUniformMatrixActual.requestCap m)
    (GaussUniformMatrixActual.resultCap m) hin hout

#print axioms physical_pivot_matrix_global
#print axioms actual_pivot_matrix_global

end CurrentAdditive.GaussUniformMatrixGlobal
