import CurrentAdditive.GaussFirstFreeContextInvoke
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A two-call fixed program preserves the Gauss state and width while
installing the first-free unary index and the matrix word in separate banks.
The remaining indexed work-item loop can consume those prepared banks. -/

namespace CurrentAdditive.GaussStateMatrixContext

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

noncomputable abbrev Sel := GaussPivotPrefixPhysical.machine
noncomputable abbrev Proj := BankFieldProjection.machine (0 : Fin 4)
abbrev Bank := MachineInvokeCore.StackN (Sel.stackCount + Proj.stackCount)

noncomputable def selEmbed (i : Fin Sel.stackCount) : Bank :=
  ⟨32 + i.val, by omega⟩

noncomputable def projEmbed (i : Fin Proj.stackCount) : Bank :=
  ⟨32 + Sel.stackCount + i.val, by omega⟩

theorem selEmbed_inj : Function.Injective selEmbed := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [selEmbed] at this
  omega

theorem projEmbed_inj : Function.Injective projEmbed := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [projEmbed] at this
  omega

noncomputable def selectorSlots : MachineInvokeCore.Slots Sel
    (Sel.stackCount + Proj.stackCount) where
  machine := ⟨selEmbed, selEmbed_inj⟩
  source := ⟨0, by omega⟩
  target := ⟨1, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have := congrArg Fin.val h; simp [selEmbed] at this; omega
  target_machine := by intro i h; have := congrArg Fin.val h; simp [selEmbed] at this; omega
  scratch_machine := by intro i h; have := congrArg Fin.val h; simp [selEmbed] at this; omega

noncomputable def matrixSlots : MachineInvokeCore.Slots Proj
    (Sel.stackCount + Proj.stackCount) where
  machine := ⟨projEmbed, projEmbed_inj⟩
  source := ⟨0, by omega⟩
  target := ⟨4, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have := congrArg Fin.val h; simp [projEmbed] at this; omega
  target_machine := by intro i h; have := congrArg Fin.val h; simp [projEmbed] at this; omega
  scratch_machine := by intro i h; have := congrArg Fin.val h; simp [projEmbed] at this; omega

noncomputable def inputBank (state : List Bool) (k : Nat) : Bank → List Bool :=
  fun b => if b = selectorSlots.source then state else
    if b = (⟨3, by omega⟩ : Bank) then List.replicate k true else []

theorem input_source (state : List Bool) (k : Nat) :
    inputBank state k selectorSlots.source = state := by simp [inputBank]

theorem input_target (state : List Bool) (k : Nat) :
    inputBank state k selectorSlots.target = [] := by
  simp [inputBank, selectorSlots]

theorem input_scratch (state : List Bool) (k : Nat) :
    inputBank state k selectorSlots.scratch = [] := by
  simp [inputBank, selectorSlots]

theorem input_sel_blank (state : List Bool) (k : Nat)
    (i : Fin Sel.stackCount) :
    inputBank state k (selectorSlots.machine i) = [] := by
  have h0 := (selectorSlots.source_machine i).symm
  have h3 : selectorSlots.machine i ≠ (⟨3, by omega⟩ : Bank) := by
    intro h
    have := congrArg Fin.val h
    simp [selectorSlots, selEmbed] at this
    omega
  simp [inputBank, h0, h3]

theorem projected_matrix {m k : Nat}
    (s : GaussControlTrace.State m k) :
    Proj.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussPhysical.encodeTypedMatrix s.B)
      (12 * ((GaussControlTrace.statePacket s).length + 1)) := by
  simpa [Proj, GaussControlTrace.statePacket,
    GaussControlTrace.stateBank, BankFieldProjection.result_encode] using
    (BankFieldProjection.outputs (0 : Fin 4)
      (GaussControlTrace.statePacket s))

noncomputable def program :=
  BitMachineRawSequence.program
    (MachineInvokeFull.program selectorSlots)
    (MachineInvokeFull.program matrixSlots)
    (MachineInvokeFull.start matrixSlots)
    (MachineInvokeFull.control selectorSlots)
    (MachineInvokeFull.control matrixSlots)

theorem physical_selector_and_matrix {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := inputBank (GaussControlTrace.statePacket s) k
    ∃ f u,
      (List.range k).find?
        (fun c => decide (c ∉
          (GaussPivotPacketBridge.natPivots s.pivots).map Prod.snd)) =
        some f ∧
      u ≤ MachineInvokeFull.uniformBound Sel
          (GaussControlTrace.statePacket s)
          (GaussPivotPrefixClock.prefixClock m k) +
        MachineInvokeFull.uniformBound Proj
          (GaussControlTrace.statePacket s)
          (12 * ((GaussControlTrace.statePacket s).length + 1)) + 1 ∧
      ((advance program)^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (MachineInvokeFull.start selectorSlots)),
          (MachineInvokeFull.control selectorSlots,
            MachineInvokeFull.control matrixSlots), S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,
          (MachineInvokeFull.control selectorSlots,
            MachineInvokeFull.control matrixSlots),
          Function.update
            (Function.update S selectorSlots.target (List.replicate f true))
            matrixSlots.target (GaussPhysical.encodeTypedMatrix s.B)⟩ := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let state := GaussControlTrace.statePacket s
  let S := inputBank state k
  obtain ⟨f, hf, hsel⟩ :=
    GaussPivotPrefixClock.physical_firstFree A h01 hkm
  obtain ⟨u, hu, hr⟩ := MachineInvokeFull.invoke_run_uniform
    selectorSlots S state (List.replicate f true)
    (GaussPivotPrefixClock.prefixClock m k)
    (input_source state k) (input_target state k)
    (input_scratch state k) (input_sel_blank state k) hsel
  let S1 := Function.update S selectorSlots.target (List.replicate f true)
  have hsrc : S1 matrixSlots.source = state := by
    simp [S1, S, matrixSlots, selectorSlots, inputBank]
  have htgt : S1 matrixSlots.target = [] := by
    simp [S1, S, matrixSlots, selectorSlots, inputBank]
  have hscr : S1 matrixSlots.scratch = [] := by
    simp [S1, S, matrixSlots, selectorSlots, inputBank]
  have hblank : ∀ i, S1 (matrixSlots.machine i) = [] := by
    intro i
    have h1 : matrixSlots.machine i ≠ selectorSlots.target := by
      intro h
      have := congrArg Fin.val h
      simp [matrixSlots, projEmbed, selectorSlots] at this
      omega
    have h0 : matrixSlots.machine i ≠ selectorSlots.source := by
      intro h
      have := congrArg Fin.val h
      simp [matrixSlots, projEmbed, selectorSlots] at this
    have h3 : matrixSlots.machine i ≠ (⟨3, by omega⟩ : Bank) := by
      intro h
      have := congrArg Fin.val h
      simp [matrixSlots, projEmbed] at this
      omega
    simp [S1, S, inputBank, h1, h0, h3]
  obtain ⟨v, hv, hr2⟩ := MachineInvokeFull.invoke_run_uniform
    matrixSlots S1 state (GaussPhysical.encodeTypedMatrix s.B)
    (12 * (state.length + 1)) hsrc htgt hscr hblank
    (projected_matrix s)
  obtain ⟨w, hw, hr3⟩ := BitMachineRawSequence.runs
    (MachineInvokeFull.program selectorSlots)
    (MachineInvokeFull.program matrixSlots)
    (MachineInvokeFull.start selectorSlots)
    (MachineInvokeFull.start matrixSlots)
    (MachineInvokeFull.control selectorSlots)
    (MachineInvokeFull.control selectorSlots)
    (MachineInvokeFull.control matrixSlots)
    (MachineInvokeFull.control matrixSlots)
    S S1 (Function.update S1 matrixSlots.target
      (GaussPhysical.encodeTypedMatrix s.B)) u v hr hr2
  refine ⟨f, w, hf, ?_, by simpa [program, S1] using hr3⟩
  dsimp only [state, s, Aq] at hu hv ⊢
  omega

#print axioms physical_selector_and_matrix

end CurrentAdditive.GaussStateMatrixContext
