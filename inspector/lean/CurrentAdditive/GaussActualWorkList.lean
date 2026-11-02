import CurrentAdditive.GaussWorkListComplete

/-! The physically prepared post-Gauss state feeds the complete physical
ordered request-list producer.  The source is the actual zero-one input and
the retained unary width is explicit, including zero rows. -/

namespace CurrentAdditive.GaussActualWorkList

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussStateMatrixContext.Bank

noncomputable def program := BitMachineRawSequence.program
  GaussStateMatrixContext.program GaussWorkListComplete.program
  GaussWorkListComplete.start
  (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.selectorSlots,
    CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.matrixSlots)
  GaussWorkListComplete.control

private abbrev InputLabel {α β : Type} (_ : α → β) : Type := α

noncomputable def start : InputLabel program := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
      GaussStateMatrixContext.selectorSlots))

noncomputable def control :=
  ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.selectorSlots,
    CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.matrixSlots),
    GaussWorkListComplete.control)

theorem physical_actual_work_list {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank
      (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ m) (t : Nat),
      t ≤ CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Sel (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Proj (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 +
        GaussWorkListComplete.totalClock s.B f + 1 ∧
      ((advance program)^[t])
        (⟨some start, control, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, control,
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
  obtain ⟨fn, u, hfind, hu, hrunPrep⟩ :=
    GaussStateMatrixContext.physical_selector_and_matrix A h01 hkm
  have hfirst := GaussPivotPacketBridge.after_prefix_is_firstFree Aq hkm
  have hfn : fn = GaussPivotPrefixPhysical.prefixCount
      (GaussPivotPacketBridge.natPivots s.pivots) := by
    have heq := hfind.symm.trans hfirst
    exact Option.some.inj heq
  have hlen : (GaussPivotPacketBridge.natPivots s.pivots).length ≤ m := by
    have hp := GaussControlTrace.after_pivotCount Aq k
    have hr := GaussControlTrace.after_row_le Aq k
    change s.r = s.pivots.length at hp
    change s.r ≤ m at hr
    simpa [GaussPivotPacketBridge.natPivots] using (show s.pivots.length ≤ m by omega)
  have hprefix : GaussPivotPrefixPhysical.prefixCount
      (GaussPivotPacketBridge.natPivots s.pivots) ≤
      (GaussPivotPacketBridge.natPivots s.pivots).length := by
    unfold GaussPivotPrefixPhysical.prefixCount
    have htake (xs : List Bool) : (xs.takeWhile id).length ≤ xs.length := by
      induction xs with
      | nil => simp
      | cons b bs ih =>
          cases b <;> simp [List.takeWhile, ih] <;> omega
    have hflags : (GaussPivotPrefixPhysical.pivotFlags
        (GaussPivotPacketBridge.natPivots s.pivots)).length =
        (GaussPivotPacketBridge.natPivots s.pivots).length := by
      simp [GaussPivotPrefixPhysical.pivotFlags]
    have hle := htake (GaussPivotPrefixPhysical.pivotFlags
      (GaussPivotPacketBridge.natPivots s.pivots))
    omega
  have hfm : fn ≤ m := by omega
  have hfk' : fn < k := by omega
  let f : Fin k := ⟨fn, hfk'⟩
  have hf : f.val ≤ m := hfm
  let S1 := Function.update
      (Function.update S ⟨1, by omega⟩ (List.replicate f.val true))
      ⟨4, by omega⟩ (GaussPhysical.encodeTypedMatrix s.B)
  have hprep' : ((advance GaussStateMatrixContext.program)^[u])
      (⟨some (BitMachineRawSequence.leftLabel
        (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
          GaussStateMatrixContext.selectorSlots)),
        (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          GaussStateMatrixContext.selectorSlots,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          GaussStateMatrixContext.matrixSlots), S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,
        (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          GaussStateMatrixContext.selectorSlots,
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          GaussStateMatrixContext.matrixSlots), S1⟩ := by
    simpa [S1, GaussStateMatrixContext.selectorSlots,
      GaussStateMatrixContext.matrixSlots] using hrunPrep
  have hmat : S1 ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix s.B := by
    simp [S1]
  have hfree : S1 ⟨1, by omega⟩ = List.replicate f.val true := by
    simp [S1]
  have hwidth : S1 ⟨3, by omega⟩ = List.replicate k true := by
    have hs0 : GaussStateMatrixContext.selectorSlots.source =
        (⟨0, by omega⟩ : Bank) := rfl
    simp [S1, S, GaussStateMatrixContext.inputBank,
      hs0]
  have hblankLow (z : Bank) (hz0 : z.val ≠ 0)
      (hz1 : z.val ≠ 1) (hz3 : z.val ≠ 3)
      (hz4 : z.val ≠ 4) : S1 z = [] := by
    have hn0 : z ≠ GaussStateMatrixContext.selectorSlots.source := by
      intro h
      have hv := congrArg Fin.val h
      change z.val = 0 at hv
      exact hz0 hv
    have hn1 : z ≠ (⟨1, by omega⟩ : Bank) := by
      intro h
      have hv := congrArg Fin.val h
      change z.val = 1 at hv
      exact hz1 hv
    have hn3 : z ≠ (⟨3, by omega⟩ : Bank) := by
      intro h
      have hv := congrArg Fin.val h
      change z.val = 3 at hv
      exact hz3 hv
    have hn4 : z ≠ (⟨4, by omega⟩ : Bank) := by
      intro h
      have hv := congrArg Fin.val h
      change z.val = 4 at hv
      exact hz4 hv
    simp [S1, S, GaussStateMatrixContext.inputBank,
      hn0, hn1, hn3, hn4]
  have hs5 : S1 ⟨5, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs6 : S1 ⟨6, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs7 : S1 ⟨7, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs8 : S1 ⟨8, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs9 : S1 ⟨9, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs10 : S1 ⟨10, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs11 : S1 ⟨11, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs12 : S1 ⟨12, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs13 : S1 ⟨13, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs14 : S1 ⟨14, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs15 : S1 ⟨15, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : S1 ⟨24, by omega⟩ = [] := hblankLow _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsblank : ∀ i,
      S1 (GaussWorkItemFrameContext.slots.machine i) = [] := by
    intro i
    have hv : (GaussWorkItemFrameContext.slots.machine i).val = 16 + i.val := rfl
    have hi : i.val < 8 := by
      simpa only [show (SourceListMachineWriter.framingMachine true).stackCount = 8
        from rfl] using i.isLt
    exact hblankLow _ (by omega) (by omega) (by omega) (by omega)
  obtain ⟨v, hv, hrunList⟩ :=
    GaussWorkListComplete.physical_work_list s.B f S1
      hmat hfree hwidth hs5 hs6 hs7 hs8 hs9 hs10 hs11 hs12
      hs13 hs14 hs15 hs24 hsblank
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    GaussStateMatrixContext.program GaussWorkListComplete.program
    (BitMachineRawSequence.leftLabel
      (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
        GaussStateMatrixContext.selectorSlots))
    GaussWorkListComplete.start
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.selectorSlots,
    CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.matrixSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.selectorSlots,
    CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.matrixSlots)
    GaussWorkListComplete.control GaussWorkListComplete.control
    S S1
    (Function.update
      (Function.update
        (GaussWorkListFuel.stateAt
          (Function.update S1 ⟨5, by omega⟩ (List.replicate k true))
          s.B f k)
        ⟨13, by omega⟩
        (SourceListMachineWriter.result false (List.replicate k true)))
      ⟨24, by omega⟩
      (SourceListEncoding.encode (GaussWorkListComplete.workPackets s.B f)))
    u v hprep' hrunList
  refine ⟨f, hf, t, ?_, ?_⟩
  · change t ≤
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Sel (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Proj (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 +
        GaussWorkListComplete.totalClock s.B f + 1
    have hu' : u ≤
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Sel (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Proj (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 := by
      simpa [s, Aq] using hu
    omega
  · simpa [program, start, control, S1, S, Aq, s] using hrun

#print axioms physical_actual_work_list

end CurrentAdditive.GaussActualWorkList
