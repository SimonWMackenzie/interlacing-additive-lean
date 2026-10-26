import CurrentAdditive.GaussUniformMatrixRun

set_option maxHeartbeats 2000000

/-! Uniform envelope for one complete m-by-k materialized pivot update. -/

namespace CurrentAdditive.GaussUniformMatrixBounded

open EthInapproximability.CurrentPaper

theorem physical_pivot_matrix_bounded {m k : Nat}
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
    ∃ C : Nat,
      (GaussNestedMatrixMap.matrixMachine
        GaussCellSubtractCall.machine).OutputsWithin
        (GaussNestedMatrixMap.encodeNested
          (GaussAdaptedMatrixMap.adaptedMatrix
            s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
        (CurrentAdditive.GaussPhysical.encodeTypedMatrix
          (CurrentAdditive.GaussControlTrace.step s).B)
        (GaussNestedMatrixMap.matrixTimeEnvelope
          GaussCellSubtractCall.machine m k L R
          (C*(L+1)^GaussUniformMatrixRun.exponent)) := by
  obtain ⟨f,C,hclock,_⟩ := GaussUniformMatrixRun.uniform_cell_clock
  let bound : List Bool → Nat := fun x =>
    C*(x.length+1)^GaussUniformMatrixRun.exponent
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
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j)) := hclock _
  have hrun := GaussAdaptedPivotStep.physical_pivot_step
    s hr hc pivot hp GaussCellSubtractCall.machine f bound hcell hf
  have htime (i : Fin m) (j : Fin k) :
      bound (GaussUniformCellAlgebra.adaptedSourceCellPacket
        s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j) ≤
        C*(L+1)^GaussUniformMatrixRun.exponent := by
    unfold bound
    gcongr
    exact hin i j
  have hbound := GaussAdaptedMatrixMap.adapted_clock_le
    s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩
    GaussCellSubtractCall.machine f bound L R
    (C*(L+1)^GaussUniformMatrixRun.exponent)
    hin (by intro i j; rw [hf]; exact hout i j) htime
  refine ⟨C,?_⟩
  exact BitMachine.outputsWithin_mono _ hrun hbound

#print axioms physical_pivot_matrix_bounded

end CurrentAdditive.GaussUniformMatrixBounded
