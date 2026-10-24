import CurrentAdditive.GaussWideVectorInvoke
import CurrentAdditive.GaussActualWorkListValid

/-! One fixed widened TM2 program now runs the actual post-Gauss work-list
producer followed by the physical coefficient-vector machine. -/

namespace CurrentAdditive.GaussActualVectorFused

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.GaussFirstFreeCandidate

noncomputable def vectorClock {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k) : Nat :=
  SourceListMachineOuter.canonicalBound
    (GaussVectorOuterWriter.framedMachine GaussCoefficientProgram.machine)
    (GaussCertificateWorkList.workPackets B f)
    (fun x => SourceListMachineWriter.result true
      (GaussCoefficientProgram.result x))
    (GaussVectorOuterWriter.itemClock GaussCoefficientProgram.result
      GaussCoefficientOuterJoin.itemClock)

noncomputable def totalClock {m k : Nat}
    (s : GaussControlTrace.State m k) (f : Fin k) : Nat :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
      GaussStateMatrixContext.Sel (GaussControlTrace.statePacket s)
      (GaussPivotPrefixClock.prefixClock m k) +
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
      GaussStateMatrixContext.Proj (GaussControlTrace.statePacket s)
      (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 +
  GaussWorkListComplete.totalClock s.B f + 1 +
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
    GaussWideVectorInvoke.VectorMachine
    (SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f))
    (vectorClock s.B f) + 1

theorem actual_vector_fused {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank
      (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ m) (t : Nat)
      (T : GaussWideVectorInvoke.OldBank → List Bool),
      CurrentAdditive.SequentialTotality.typedFree s.pivots = some f ∧
      t ≤ totalClock s f ∧
      ((advance GaussWideVectorInvoke.program)^[t])
        (⟨some GaussWideVectorInvoke.start, GaussWideVectorInvoke.control,
          GaussWideVectorInvoke.wide S⟩ :
          TM2.Cfg (fun _ : GaussWideVectorInvoke.Bank => Bool) _ _) =
        ⟨none, GaussWideVectorInvoke.control,
          Function.update (GaussWideVectorInvoke.wide T)
            GaussWideVectorInvoke.slots.target
            (vectorPacket (Array.ofFn (directCandidate s.B f hf)))⟩ := by
  obtain ⟨f, hf, w, htyped, hw, hr⟩ :=
    GaussActualWorkListValid.physical_actual_work_list_valid A h01 hkm
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let S := GaussStateMatrixContext.inputBank
    (GaussControlTrace.statePacket s) k
  let T : GaussWideVectorInvoke.OldBank → List Bool :=
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
  have h24 : T ⟨24, by omega⟩ =
      SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f) := by
    simp [T]
  have h25 : T ⟨25, by omega⟩ = [] := by
    have hne : (⟨25, by omega⟩ : GaussWideVectorInvoke.OldBank) ≠
        GaussStateMatrixContext.selectorSlots.source := by
      intro h
      have hv := congrArg Fin.val h
      change 25 = 0 at hv
      omega
    simp [T, GaussWorkListFuel.stateAt, S,
      GaussStateMatrixContext.inputBank, hne]
  have h26 : T ⟨26, by omega⟩ = [] := by
    have hne : (⟨26, by omega⟩ : GaussWideVectorInvoke.OldBank) ≠
        GaussStateMatrixContext.selectorSlots.source := by
      intro h
      have hv := congrArg Fin.val h
      change 26 = 0 at hv
      omega
    simp [T, GaussWorkListFuel.stateAt, S,
      GaussStateMatrixContext.inputBank, hne]
  have hvec : GaussWideVectorInvoke.VectorMachine.OutputsWithin
      (T ⟨24, by omega⟩)
      (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
      (vectorClock s.B f) := by
    rw [h24]
    exact GaussCoefficientOuterJoin.outputs_physical_work_list s.B f hf
  obtain ⟨u, hu, hrun⟩ := GaussWideVectorInvoke.fused_run S T w
    (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
    (vectorClock s.B f) hr h25 h26 hvec
  refine ⟨f, hf, u, T, htyped, ?_, hrun⟩
  rw [h24] at hu
  dsimp only [s, Aq] at hu
  dsimp only [totalClock, s, Aq]
  omega

#print axioms actual_vector_fused

end CurrentAdditive.GaussActualVectorFused
