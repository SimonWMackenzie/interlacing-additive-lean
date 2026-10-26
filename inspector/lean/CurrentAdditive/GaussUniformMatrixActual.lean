import CurrentAdditive.GaussUniformMatrixBounded

set_option maxHeartbeats 2000000

/-! The complete pivot rewrite has a uniform budget along every actual
zero-one trace; its bounds retain all k matrix columns. -/

namespace CurrentAdditive.GaussUniformMatrixActual

open CurrentAdditive.GaussPhysical

def entryCap (m : Nat) : Nat :=
  (m+3)*(m+1)^2+1

def requestCap (m : Nat) : Nat :=
  32*entryCap m+54

def resultCap (m : Nat) : Nat :=
  4*entryCap m+5

theorem actual_pivot_matrix_bound {m k : Nat}
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
    ∃ C : Nat,
      (GaussNestedMatrixMap.matrixMachine
        GaussCellSubtractCall.machine).OutputsWithin
        (GaussNestedMatrixMap.encodeNested
          (GaussAdaptedMatrixMap.adaptedMatrix
            s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
        (encodeTypedMatrix (CurrentAdditive.GaussControlTrace.step s).B)
        (GaussNestedMatrixMap.matrixTimeEnvelope
          GaussCellSubtractCall.machine m k
          (requestCap m) (resultCap m)
          (C*(requestCap m+1)^GaussUniformMatrixRun.exponent)) := by
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
        s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j).length ≤ requestCap m := by
    rw [hB]
    simpa only [requestCap, entryCap, Aq] using
      (GaussUniformCellClock.actual_adapted_source_packet_length
        A h01 t (Nat.le_of_lt ht) ⟨s.r, hr⟩ pivot i ⟨s.c, hc⟩ j)
  have hout (i : Fin m) (j : Fin k) :
      (CurrentAdditive.CodeDCodec.encodeRawRat
        (rawOfRat
          (CurrentAdditive.SequentialTotality.clearTyped
            (CurrentAdditive.SequentialTotality.swapTyped
              s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j))).length ≤
        resultCap m := by
    have hclear :
        CurrentAdditive.SequentialTotality.clearTyped
          (CurrentAdditive.SequentialTotality.swapTyped
            s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j =
          (CurrentAdditive.GaussControlTrace.step s).B i j := by
      simp [CurrentAdditive.GaussControlTrace.step, hr, hc, hp,
        CurrentAdditive.MaterializedGauss.materialize_eq]
    rw [hclear, hnext]
    simpa only [resultCap, entryCap, Aq] using
      (actualGauss_cell_code_length A h01 (t+1)
        (Nat.succ_le_of_lt ht) i j)
  exact GaussUniformMatrixBounded.physical_pivot_matrix_bounded
    s hr hc pivot hp (requestCap m) (resultCap m) hin hout

#print axioms actual_pivot_matrix_bound

end CurrentAdditive.GaussUniformMatrixActual
