import CurrentAdditive.GaussCoefficientOuterJoin

/-! The second fixed machine consumes the literal output bank of the first.
This staged statement does not claim a fused TM2 program. -/

namespace CurrentAdditive.GaussCertificateStageJoin

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.GaussFirstFreeCandidate

theorem actual_coefficient_vector_staged {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank
      (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ m) (t : Nat)
      (T : GaussActualWorkList.Bank → List Bool),
      t ≤ CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Sel (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Proj (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 +
        GaussWorkListComplete.totalClock s.B f + 1 ∧
      ((advance GaussActualWorkList.program)^[t])
        (⟨some GaussActualWorkList.start, GaussActualWorkList.control, S⟩ :
          TM2.Cfg (fun _ : GaussActualWorkList.Bank => Bool) _ _) =
        ⟨none, GaussActualWorkList.control, T⟩ ∧
      (GaussVectorOuterWriter.machine GaussCoefficientProgram.machine).OutputsWithin
        (T ⟨24, by omega⟩)
        (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
        (SourceListMachineOuter.canonicalBound
          (GaussVectorOuterWriter.framedMachine GaussCoefficientProgram.machine)
          (GaussCertificateWorkList.workPackets s.B f)
          (fun x => SourceListMachineWriter.result true
            (GaussCoefficientProgram.result x))
          (GaussVectorOuterWriter.itemClock GaussCoefficientProgram.result
            GaussCoefficientOuterJoin.itemClock)) := by
  obtain ⟨f, hf, t, ht, hr⟩ :=
    GaussActualWorkList.physical_actual_work_list A h01 hkm
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let S := GaussStateMatrixContext.inputBank
    (GaussControlTrace.statePacket s) k
  let T : GaussActualWorkList.Bank → List Bool :=
    Function.update
      (Function.update
        (GaussWorkListFuel.stateAt
          (Function.update
            (Function.update
              (Function.update S ⟨1, by omega⟩
                (List.replicate f.val true))
              ⟨4, by omega⟩ (GaussPhysical.encodeTypedMatrix s.B))
            ⟨5, by omega⟩ (List.replicate k true))
          s.B f k)
        ⟨13, by omega⟩
        (SourceListMachineWriter.result false (List.replicate k true)))
      ⟨24, by omega⟩
      (SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f))
  refine ⟨f, hf, t, T, ht, ?_, ?_⟩
  · exact hr
  · have h24 : T ⟨24, by omega⟩ =
        SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f) := by
      simp [T]
    rw [h24]
    exact GaussCoefficientOuterJoin.outputs_physical_work_list s.B f hf

#print axioms actual_coefficient_vector_staged

end CurrentAdditive.GaussCertificateStageJoin
