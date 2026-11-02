import CurrentAdditive.GaussPivotPrefixClock
import CurrentAdditive.MachineInvokeFull

/-! The first-free selector now runs inside a fixed ambient Boolean-stack
program while retaining the entire post-Gauss state and the unary width.
The output is installed on a separate bank, and the embedded selector banks
are physically cleared.  Building the indexed work list remains separate. -/

namespace CurrentAdditive.GaussFirstFreeContextInvoke

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

noncomputable abbrev Selector : BitMachine.Machine := GaussPivotPrefixPhysical.machine
abbrev Bank := MachineInvokeCore.StackN Selector.stackCount

noncomputable def embedded (i : Fin Selector.stackCount) : Bank :=
  ⟨32 + i.val, by omega⟩

theorem embedded_injective : Function.Injective embedded := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp [embedded] at hv
  omega

noncomputable def slots : MachineInvokeCore.Slots Selector Selector.stackCount where
  machine := ⟨embedded, embedded_injective⟩
  source := ⟨0, by omega⟩
  target := ⟨1, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega
  target_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega
  scratch_machine := by intro i h; have := congrArg Fin.val h; simp [embedded] at this; omega

noncomputable def inputBank (state : List Bool) (k : Nat) : Bank → List Bool :=
  fun b => if b = slots.source then state else
    if b = (⟨3, by omega⟩ : Bank) then List.replicate k true else []

theorem source_word (state : List Bool) (k : Nat) :
    inputBank state k slots.source = state := by
  simp [inputBank]

theorem target_blank (state : List Bool) (k : Nat) :
    inputBank state k slots.target = [] := by
  simp [inputBank, slots]

theorem scratch_blank (state : List Bool) (k : Nat) :
    inputBank state k slots.scratch = [] := by
  simp [inputBank, slots]

theorem embedded_blank (state : List Bool) (k : Nat)
    (i : Fin Selector.stackCount) :
    inputBank state k (slots.machine i) = [] := by
  have h0 : slots.machine i ≠ slots.source := by
    exact (slots.source_machine i).symm
  have h3 : slots.machine i ≠ (⟨3, by omega⟩ : Bank) := by
    intro h
    have hv := congrArg Fin.val h
    simp [slots, embedded] at hv
    omega
  simp [inputBank, h0, h3]

theorem physical_firstFree_with_width {m k : Nat}
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
      u ≤ MachineInvokeFull.uniformBound Selector
        (GaussControlTrace.statePacket s)
        (GaussPivotPrefixClock.prefixClock m k) ∧
      ((advance (MachineInvokeFull.program slots))^[u])
        (⟨some (MachineInvokeFull.start slots),
          MachineInvokeFull.control slots, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, MachineInvokeFull.control slots,
          Function.update S slots.target (List.replicate f true)⟩ := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let state := GaussControlTrace.statePacket s
  let S := inputBank state k
  obtain ⟨f, hf, hsel⟩ :=
    GaussPivotPrefixClock.physical_firstFree A h01 hkm
  have hrun := MachineInvokeFull.invoke_run_uniform slots S
    state (List.replicate f true)
    (GaussPivotPrefixClock.prefixClock m k)
    (source_word state k) (target_blank state k)
    (scratch_blank state k) (embedded_blank state k) hsel
  obtain ⟨u, hu, hr⟩ := hrun
  exact ⟨f, u, hf, hu, hr⟩

#print axioms physical_firstFree_with_width

end CurrentAdditive.GaussFirstFreeContextInvoke
