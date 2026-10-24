import CurrentAdditive.GaussActualWorkList
import CurrentAdditive.GaussCertificateWorkList

/-! A single fixed polynomial clock for the actual zero-one Gauss work-list run.
Every term in the physical schedule, including cleanup, is charged. -/

namespace CurrentAdditive.GaussActualWorkListClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext

def stateCap (m k : Nat) : Nat := GaussPivotPrefixClock.stateCap m k
def packetCap (m k : Nat) : Nat := 2 * (stateCap m k + 2 * k) + 3
def fieldCap (m k : Nat) : Nat := 3 * packetCap m k + 1

noncomputable def accumCap (m k : Nat) : Nat :=
  (2 * stateCap m k + 2) + (2 * k + 2) + (2 * k + 2) + 2 +
    (2 * packetCap m k + 2) + 1 +
    MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W
      (List.replicate (packetCap m k) true)
      ((UnaryBinaryEncoding.coefficient + 7) * (packetCap m k + 1)^2) + 1 +
    (2 * fieldCap m k + 2) + 1

noncomputable def roundCap (m k : Nat) : Nat :=
  accumCap m k + packetCap m k + fieldCap m k +
    3 * (GaussWorkItemRoundComplete.roundPush * accumCap m k) + 11

noncomputable def headerCap (k : Nat) : Nat :=
  MachineInvokeFull.uniformBound
    (SourceListMachineWriter.framingMachine false)
    (List.replicate k true)
    ((UnaryBinaryEncoding.coefficient + 7) * (k + 1)^2) +
  (2 * (3*k+1) + 2) + 1

noncomputable def clock (m k : Nat) : Nat :=
  MachineInvokeFull.uniformBound GaussStateMatrixContext.Sel
    (List.replicate (stateCap m k) true)
    (GaussPivotPrefixClock.prefixClock m k) +
  MachineInvokeFull.uniformBound GaussStateMatrixContext.Proj
    (List.replicate (stateCap m k) true)
    (12 * (stateCap m k + 1)) + 1 +
  ((2 * k + 2) + (k * (roundCap m k + 1) + 1) +
    headerCap k + 2) + 1

theorem uniformBound_mono (M : BitMachine.Machine)
    {xs ys : List Bool} {a b : Nat}
    (hx : xs.length ≤ ys.length) (ha : a ≤ b) :
    MachineInvokeFull.uniformBound M xs a ≤
      MachineInvokeFull.uniformBound M ys b := by
  unfold MachineInvokeFull.uniformBound
  gcongr

theorem matrix_length_le_statePacket {m k : Nat}
    (s : GaussControlTrace.State m k) :
    (GaussPhysical.encodeTypedMatrix s.B).length ≤
      (GaussControlTrace.statePacket s).length := by
  have h := BitMachineBankCodec.word_length_le_encode
    (GaussControlTrace.stateBank s) (0 : Fin 4)
  simpa [GaussControlTrace.statePacket, GaussControlTrace.stateBank] using h

theorem workPacket_length_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k) (C : Nat)
    (hB : (GaussPhysical.encodeTypedMatrix B).length ≤ C) :
    (GaussWorkItemContextSerialize.workPacket B f j).length ≤
      2 * (C + 2*k) + 3 := by
  have h := GaussCertificateWorkList.workPacket_length_le B f j
  have heq : GaussWorkItemContextSerialize.workPacket B f j =
      GaussCertificateWorkList.workPacket B f j := rfl
  rw [heq]
  omega

theorem actual_matrix_length {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    (GaussPhysical.encodeTypedMatrix s.B).length ≤ stateCap m k := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  have hs := GaussControlTrace.actual_statePacket_length A h01 k (by omega)
  exact (matrix_length_le_statePacket s).trans (by simpa [stateCap, s, Aq] using hs)

theorem roundClock_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (hB : (GaussPhysical.encodeTypedMatrix B).length ≤ stateCap m k) :
    GaussWorkItemRoundComplete.roundClock B f j ≤ roundCap m k := by
  let raw := GaussWorkItemContextSerialize.workPacket B f j
  let field := SourceListMachineWriter.result true raw
  have hr : raw.length ≤ packetCap m k := by
    exact workPacket_length_le B f j _ hB
  have hf : field.length ≤ fieldCap m k := by
    exact (SourceListMachineWriter.result_length true raw).trans (by
      unfold fieldCap
      omega)
  have hfl : f.val ≤ k := Nat.le_of_lt f.isLt
  have hjl : j.val ≤ k := Nat.le_of_lt j.isLt
  have hinvoke : MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W raw
      ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2) ≤
      MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W
        (List.replicate (packetCap m k) true)
        ((UnaryBinaryEncoding.coefficient + 7) * (packetCap m k + 1)^2) := by
    apply uniformBound_mono GaussWorkItemRoundRun.W
    · simpa using hr
    · gcongr
  have ha : GaussWorkItemRoundComplete.accumClock B f j ≤ accumCap m k := by
    change
      (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
      (2 * f.val + 2) + (2 * j.val + 2) + 2 +
      (2 * raw.length + 2) + 1 +
      MachineInvokeFull.uniformBound GaussWorkItemRoundRun.W raw
        ((UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2) + 1 +
      (2 * field.length + 2) + 1 ≤ accumCap m k
    unfold accumCap
    omega
  unfold GaussWorkItemRoundComplete.roundClock roundCap
  dsimp only
  gcongr

theorem maxRoundClock_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k)
    (hB : (GaussPhysical.encodeTypedMatrix B).length ≤ stateCap m k) :
    GaussWorkListFuel.maxRoundClock B f ≤ roundCap m k := by
  unfold GaussWorkListFuel.maxRoundClock
  exact Finset.sup_le (fun j hj => roundClock_le B f j hB)

theorem headerClock_le (k : Nat) :
    GaussWorkListHeaderJoin.headerClock k ≤ headerCap k := by
  have h := SourceListMachineWriter.result_length false (List.replicate k true)
  unfold GaussWorkListHeaderJoin.headerClock headerCap
  dsimp only
  simp only [List.length_replicate] at h ⊢
  omega

theorem totalClock_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f : Fin k)
    (hB : (GaussPhysical.encodeTypedMatrix B).length ≤ stateCap m k) :
    GaussWorkListComplete.totalClock B f ≤
      (2*k+2) + (k*(roundCap m k+1)+1) + headerCap k + 2 := by
  have hr := maxRoundClock_le B f hB
  have hh := headerClock_le k
  unfold GaussWorkListComplete.totalClock
  gcongr

theorem physical_actual_work_list_polynomial {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank
      (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ m) (t : Nat),
      t ≤ clock m k ∧
      ((BitMachineEncoding.advance GaussActualWorkList.program)^[t])
        (⟨some GaussActualWorkList.start, GaussActualWorkList.control, S⟩ :
          Turing.TM2.Cfg (fun _ : GaussActualWorkList.Bank => Bool) _ _) =
        ⟨none, GaussActualWorkList.control,
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
            (SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f))⟩ := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
  obtain ⟨f, hf, t, ht, hrun⟩ :=
    GaussActualWorkList.physical_actual_work_list A h01 hkm
  refine ⟨f, hf, t, ?_, ?_⟩
  have hs : (GaussControlTrace.statePacket s).length ≤ stateCap m k := by
    simpa [stateCap, s, Aq] using
      (GaussControlTrace.actual_statePacket_length A h01 k (by omega))
  have hB : (GaussPhysical.encodeTypedMatrix s.B).length ≤ stateCap m k :=
    (matrix_length_le_statePacket s).trans hs
  have hsel := uniformBound_mono GaussStateMatrixContext.Sel
    (xs := GaussControlTrace.statePacket s)
    (ys := List.replicate (stateCap m k) true)
    (a := GaussPivotPrefixClock.prefixClock m k)
    (b := GaussPivotPrefixClock.prefixClock m k)
    (by simpa only [List.length_replicate] using hs) (Nat.le_refl _)
  have hproj := uniformBound_mono GaussStateMatrixContext.Proj
    (xs := GaussControlTrace.statePacket s)
    (ys := List.replicate (stateCap m k) true)
    (a := 12 * ((GaussControlTrace.statePacket s).length + 1))
    (b := 12 * (stateCap m k + 1))
    (by simpa only [List.length_replicate] using hs)
    (by omega : 12 * ((GaussControlTrace.statePacket s).length + 1) ≤
      12 * (stateCap m k + 1))
  have hlist := totalClock_le s.B f hB
  have ht' : t ≤
      MachineInvokeFull.uniformBound GaussStateMatrixContext.Sel
          (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        MachineInvokeFull.uniformBound GaussStateMatrixContext.Proj
          (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 +
        GaussWorkListComplete.totalClock s.B f + 1 := by
    simpa [s, Aq] using ht
  · unfold clock
    omega
  · simpa [Aq, s, S] using hrun

#print axioms physical_actual_work_list_polynomial

end CurrentAdditive.GaussActualWorkListClock
