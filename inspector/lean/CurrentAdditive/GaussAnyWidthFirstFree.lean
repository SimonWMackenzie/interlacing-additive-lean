import CurrentAdditive.GaussDirectPostloop
import CurrentAdditive.IndependentSupport
import CurrentAdditive.GaussPivotPrefixClock
import CurrentAdditive.GaussStateMatrixContext

/-!
The physical pivot-prefix scan reports the first free column at every width.
The old endpoint used `m < k` to force a free column; the v38 loop also needs
the no-free result and dependent matrices with `k ≤ m`.
-/

namespace CurrentAdditive.GaussAnyWidthFirstFree

open Turing Turing.TM2 EthInapproximability.CurrentPaper.BitMachineEncoding
open GaussDirectPostloop GaussFirstFreeArithmetic
open GaussPivotPrefixPhysical SequentialTotality

theorem firstFreeNat_eq_prefix_or_none (k : Nat) (ps : List (Nat × Nat))
    (hrows : ps.map Prod.fst = List.range' 0 ps.length)
    (hinc : (ps.map Prod.snd).Pairwise (· < ·)) :
    GaussCertificateProbe.firstFreeNat k ps =
      if _h : prefixCount ps < k then some (prefixCount ps) else none := by
  let cs := ps.map Prod.snd
  have hflags := flags_eq_diagonalFrom 0 ps hrows
  have hfacts := diagonal_facts 0 cs hinc (by simp)
  have hp : diagonalPrefix 0 cs = prefixCount ps := by
    unfold diagonalPrefix prefixCount
    rw [← hflags]
  unfold GaussCertificateProbe.firstFreeNat
  by_cases hlt : prefixCount ps < k
  · simp only [dif_pos hlt]
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨?_, prefixCount ps, (by simpa using hlt), ?_, ?_⟩
    · simpa [GaussCertificateProbe.firstFreeNat, cs, hp] using hfacts.2
    · simp
    · intro j hj
      have hj' : j < diagonalPrefix 0 cs := by omega
      have hm : j ∈ cs := hfacts.1 j (by omega) (by simpa using hj')
      simpa [cs] using hm
  · simp only [dif_neg hlt]
    apply List.find?_eq_none.mpr
    intro j hj
    have hjk : j < k := by simpa using (List.mem_range.mp hj)
    have hj' : j < diagonalPrefix 0 cs := by omega
    have hm : j ∈ cs := hfacts.1 j (by omega) (by simpa using hj')
    simpa [cs] using hm

theorem after_typedFree_eq_prefix_or_none {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    let s := GaussControlTrace.after A k
    let f := prefixCount (natPivots s.pivots)
    (typedFree s.pivots).map Fin.val =
      if _h : f < k then some f else none := by
  let s := GaussControlTrace.after A k
  let ps := natPivots s.pivots
  have hcount := GaussControlTrace.after_pivotCount A k
  have hrows := GaussTraceInvariants.after_rows A k
  have hinc := GaussTraceInvariants.after_columns_pairwise A k
  have hrows' : ps.map Prod.fst = List.range' 0 ps.length := by
    simpa [ps, natPivots, hcount, List.range'_eq_map_range] using hrows
  have hinc' : (ps.map Prod.snd).Pairwise (· < ·) := by
    simpa [ps, natPivots] using hinc
  have hfirst := firstFreeNat_eq_prefix_or_none k ps hrows' hinc'
  have hbridge := GaussCertificateProbe.firstFreeNat_typed s.pivots
  simpa [s, ps, natPivots] using hbridge.symm.trans hfirst

/-- The already fixed selector machine runs within a polynomial clock at all
matrix widths, including the no-free case. Its output is the unary prefix
count; the preceding theorem gives the exact semantic branch condition. -/
theorem physical_prefix_clock_all_widths {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let ps := GaussPivotPacketBridge.natPivots s.pivots
    GaussPivotPrefixPhysical.machine.OutputsWithin
      (GaussControlTrace.statePacket s)
      (List.replicate (GaussPivotPrefixPhysical.prefixCount ps) true)
      (GaussPivotPrefixClock.prefixClock m k) ∧
    (typedFree s.pivots).map Fin.val =
      if _h : prefixCount ps < k then some (prefixCount ps) else none := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let ps := GaussPivotPacketBridge.natPivots s.pivots
  let n := (GaussControlTrace.statePacket s).length
  have hstate : n ≤ GaussPivotPrefixClock.stateCap m k := by
    simpa [n, s, Aq, GaussPivotPrefixClock.stateCap] using
      GaussControlTrace.actual_statePacket_length A h01 k (by omega)
  have hcount : s.pivots.length ≤ m := by
    have h₁ := GaussControlTrace.after_pivotCount Aq k
    have h₂ := GaussControlTrace.after_row_le Aq k
    change s.r = s.pivots.length at h₁
    change s.r ≤ m at h₂
    omega
  have hps : ps.length ≤ m := by
    simpa [ps, GaussPivotPacketBridge.natPivots] using hcount
  have hflags : (pivotFlags ps).length ≤ m := by
    simpa [pivotFlags] using hps
  have hfield :
      (EthInapproximability.CurrentPaper.EncodedCommunication.natField ps.length).length
        ≤ 2*m+1 := by
    have h := EthInapproximability.CurrentPaper.EncodedGraph.natField_length_upper
      ps.length
    omega
  have hheader :
      (EthInapproximability.CurrentPaper.EncodedCommunication.natField ps.length ++
        pivotFlags ps).length ≤ 3*m+1 := by
    simp only [List.length_append]
    omega
  have hpacket : (pivotListPacket ps).length ≤ n := by
    have h := EthInapproximability.CurrentPaper.BitMachineBankCodec.word_length_le_encode
      (stateBank (GaussPhysical.encodeTypedMatrix s.B) s.r s.c ps)
      (3 : Fin 4)
    simpa [stateBank, stateWord, GaussPivotPacketBridge.statePacket_eq, n] using h
  have houter : EthInapproximability.CurrentPaper.SourceListMachineOuter.canonicalBound
      GaussPivotPairEq.machine (pivotWords ps) GaussPivotPairEq.result
      pairClock ≤ GaussPivotPrefixClock.outerEnvelope m k := by
    simpa [ps] using GaussPivotPrefixClock.outer_bound s.pivots hcount
  dsimp only [ps] at hflags hfield hheader hpacket houter
  have hrun := GaussPivotPacketBridge.outputs_gauss_state s
  constructor
  · obtain ⟨t, ht, hhalt, hout⟩ := hrun
    refine ⟨t, ?_, hhalt, hout⟩
    unfold GaussPivotPrefixClock.prefixClock
    omega
  · exact after_typedFree_eq_prefix_or_none Aq

/-- The fixed two-call machine installs the actual post-Gauss matrix and
first-free prefix in separate banks at every width. It returns a prefix even
in the independent case, where the prefix is at least `k`. -/
theorem physical_selector_and_matrix_any_width {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let f := prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
    let S := GaussStateMatrixContext.inputBank
      (GaussControlTrace.statePacket s) k
    ∃ u,
      u ≤ CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Sel (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
          GaussStateMatrixContext.Proj (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 ∧
      ((advance GaussStateMatrixContext.program)^[u])
        (⟨some (EthInapproximability.CurrentPaper.BitMachineRawSequence.leftLabel
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            GaussStateMatrixContext.selectorSlots)),
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            GaussStateMatrixContext.selectorSlots,
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            GaussStateMatrixContext.matrixSlots), S⟩ :
          Turing.TM2.Cfg (fun _ : GaussStateMatrixContext.Bank => Bool) _ _) =
        ⟨none,
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            GaussStateMatrixContext.selectorSlots,
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            GaussStateMatrixContext.matrixSlots),
          Function.update
            (Function.update S GaussStateMatrixContext.selectorSlots.target
              (List.replicate f true))
            GaussStateMatrixContext.matrixSlots.target
            (GaussPhysical.encodeTypedMatrix s.B)⟩ ∧
      (typedFree s.pivots).map Fin.val =
        if _h : f < k then some f else none := by
  open EthInapproximability.CurrentPaper.BitMachineRawSequence in
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let state := GaussControlTrace.statePacket s
  let S := GaussStateMatrixContext.inputBank state k
  let f := prefixCount (GaussPivotPacketBridge.natPivots s.pivots)
  have hsel := (physical_prefix_clock_all_widths A h01).1
  have hbranch := (physical_prefix_clock_all_widths A h01).2
  open CurrentAdditive.MinimumRatioContext in
  obtain ⟨u, hu, hr⟩ := MachineInvokeFull.invoke_run_uniform
    GaussStateMatrixContext.selectorSlots S state (List.replicate f true)
    (GaussPivotPrefixClock.prefixClock m k)
    (GaussStateMatrixContext.input_source state k)
    (GaussStateMatrixContext.input_target state k)
    (GaussStateMatrixContext.input_scratch state k)
    (GaussStateMatrixContext.input_sel_blank state k) hsel
  let S1 := Function.update S GaussStateMatrixContext.selectorSlots.target
    (List.replicate f true)
  have hsrc : S1 GaussStateMatrixContext.matrixSlots.source = state := by
    simp [S1, S, GaussStateMatrixContext.matrixSlots,
      GaussStateMatrixContext.selectorSlots, GaussStateMatrixContext.inputBank]
  have htgt : S1 GaussStateMatrixContext.matrixSlots.target = [] := by
    simp [S1, S, GaussStateMatrixContext.matrixSlots,
      GaussStateMatrixContext.selectorSlots, GaussStateMatrixContext.inputBank]
  have hscr : S1 GaussStateMatrixContext.matrixSlots.scratch = [] := by
    simp [S1, S, GaussStateMatrixContext.matrixSlots,
      GaussStateMatrixContext.selectorSlots, GaussStateMatrixContext.inputBank]
  have hblank : ∀ i, S1 (GaussStateMatrixContext.matrixSlots.machine i) = [] := by
    intro i
    have h1 : GaussStateMatrixContext.matrixSlots.machine i ≠
        GaussStateMatrixContext.selectorSlots.target := by
      intro h
      have := congrArg Fin.val h
      simp [GaussStateMatrixContext.matrixSlots,
        GaussStateMatrixContext.projEmbed,
        GaussStateMatrixContext.selectorSlots] at this
      omega
    have h0 : GaussStateMatrixContext.matrixSlots.machine i ≠
        GaussStateMatrixContext.selectorSlots.source := by
      intro h
      have := congrArg Fin.val h
      simp [GaussStateMatrixContext.matrixSlots,
        GaussStateMatrixContext.projEmbed,
        GaussStateMatrixContext.selectorSlots] at this
    have h3 : GaussStateMatrixContext.matrixSlots.machine i ≠
        (⟨3, by omega⟩ : GaussStateMatrixContext.Bank) := by
      intro h
      have := congrArg Fin.val h
      simp [GaussStateMatrixContext.matrixSlots,
        GaussStateMatrixContext.projEmbed] at this
      omega
    simp [S1, S, GaussStateMatrixContext.inputBank, h1, h0, h3]
  open CurrentAdditive.MinimumRatioContext in
  obtain ⟨v, hv, hr2⟩ := MachineInvokeFull.invoke_run_uniform
    GaussStateMatrixContext.matrixSlots S1 state
    (GaussPhysical.encodeTypedMatrix s.B)
    (12 * (state.length + 1)) hsrc htgt hscr hblank
    (GaussStateMatrixContext.projected_matrix s)
  open EthInapproximability.CurrentPaper in
  obtain ⟨w, hw, hr3⟩ := BitMachineRawSequence.runs
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
      GaussStateMatrixContext.selectorSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
      GaussStateMatrixContext.matrixSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
      GaussStateMatrixContext.selectorSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
      GaussStateMatrixContext.matrixSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.selectorSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.selectorSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.matrixSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
      GaussStateMatrixContext.matrixSlots)
    S S1 (Function.update S1 GaussStateMatrixContext.matrixSlots.target
      (GaussPhysical.encodeTypedMatrix s.B)) u v hr hr2
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp only [state, s, Aq] at hu hv ⊢
    omega
  · simpa [GaussStateMatrixContext.program, S1] using hr3
  · exact hbranch

#print axioms firstFreeNat_eq_prefix_or_none
#print axioms after_typedFree_eq_prefix_or_none
#print axioms physical_prefix_clock_all_widths
#print axioms physical_selector_and_matrix_any_width

end CurrentAdditive.GaussAnyWidthFirstFree
