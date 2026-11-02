import CurrentAdditive.GaussStepActiveRun32

/-! Charged scratch reset and Bank4 serialization in the fixed controller. -/

namespace CurrentAdditive.GaussStepFinish32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

def cleared (S : Stack → List Bool) : Stack → List Bool :=
  BitMachineClearBank.cleared GaussAssemblerReset32.bank S

private theorem first16 (S : Stack → List Bool)
    (w : Fin 4 → List Bool)
    (hw : GaussBranchFields32.preparedBank S = w)
    (j : Fin 16) :
    cleared S (assembleSlot j) =
      GaussStateAssemble16.initialBank w j := by
  have hsrc : ∀ p : Fin 4,
      cleared S (⟨p.val+4,by omega⟩ : Stack) = w p := by
    intro p
    simpa [cleared] using
      (GaussAssemblerReset32.source_preserved S p).trans (congrFun hw p)
  have hclear : ∀ q : Fin 12,
      cleared S (GaussAssemblerReset32.bank q) = [] := by
    intro q
    exact GaussAssemblerReset32.cleared S q
  fin_cases j
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 0
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 1
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 2
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 3
  · simpa [assembleSlot,GaussStateAssemble16.initialBank] using hsrc 0
  · simpa [assembleSlot,GaussStateAssemble16.initialBank] using hsrc 1
  · simpa [assembleSlot,GaussStateAssemble16.initialBank] using hsrc 2
  · simpa [assembleSlot,GaussStateAssemble16.initialBank] using hsrc 3
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 4
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 5
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 6
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 7
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 8
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 9
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 10
  · simpa [assembleSlot,GaussStateAssemble16.initialBank,
      GaussAssemblerReset32.bank] using hclear 11

private theorem assemble_frame {m k : Nat}
    (s : GaussControlTrace.State m k)
    (S : Stack → List Bool)
    (hw : GaussBranchFields32.preparedBank S =
      GaussControlTrace.stateBank s) :
    BitMachineStackEmbedding.cfg assembleSlot (cleared S)
      Label.assemble eAssemble (some .done)
      (⟨some (.copy 0 .scan),((),none),
        GaussStateAssemble16.initialBank
          (GaussControlTrace.stateBank s)⟩ :
          GaussStateAssemble16.Config) =
      ⟨some (.assemble (.copy 0 .scan)),eAssemble ((),none),
        cleared S⟩ := by
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg]
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro j
  exact (first16 S (GaussControlTrace.stateBank s) hw j).symm

theorem finish_state {m k : Nat}
    (s : GaussControlTrace.State m k)
    (S : Stack → List Bool) (ctrl : Control)
    (hw : GaussBranchFields32.preparedBank S =
      GaussControlTrace.stateBank s) :
    ∃ t ≤ 1+(GaussAssemblerReset32.clock S+1)+1+
        (GaussStateAssemble16.clock (GaussControlTrace.stateBank s)+1+
          2*(GaussControlTrace.statePacket s).length+2),
      (run t ⟨some .afterJoin,ctrl,S⟩).l =
        some .done ∧
      (run t ⟨some .afterJoin,ctrl,S⟩).stk 14 =
        GaussControlTrace.statePacket s := by
  have h0 : run 1 ⟨some .afterJoin,ctrl,S⟩ =
      ⟨some (.resetAssembler (.inl 0)),eResetAssembler ((),none),S⟩ := by
    rfl
  have hreset : GaussAssemblerReset32.run
      (GaussAssemblerReset32.clock S+1)
      ⟨some (.inl 0),((),none),S⟩ =
      ⟨none,((),none),cleared S⟩ := by
    change ((advance GaussAssemblerReset32.program)^[
      GaussAssemblerReset32.clock S+1]) _ = _
    rw [Function.iterate_succ_apply',
      ← GaussAssemblerReset32.run,
      GaussAssemblerReset32.physical_reset]
    rfl
  obtain ⟨u,hu,hglobal⟩ :=
    GaussStepPhaseLift32.reset_assembler_lift
      (⟨some (.inl 0),((),none),S⟩)
      (GaussAssemblerReset32.clock S+1)
      (by rw [hreset])
  have h1 : run u
      ⟨some (.resetAssembler (.inl 0)),eResetAssembler ((),none),S⟩ =
      ⟨some .afterResetAssembler,eResetAssembler ((),none),cleared S⟩ := by
    simpa [BitMachineInline.cfg,hreset] using hglobal
  have h2 : run 1
      ⟨some .afterResetAssembler,eResetAssembler ((),none),cleared S⟩ =
      ⟨some (.assemble (.copy 0 .scan)),eAssemble ((),none),
        cleared S⟩ := by rfl
  obtain ⟨v,hv,hhalt,hpacket⟩ :=
    GaussStateAssemble16.physical_state_packet_one_run s
  let localCfg : GaussStateAssemble16.Config :=
    ⟨some (.copy 0 .scan),((),none),
      GaussStateAssemble16.initialBank (GaussControlTrace.stateBank s)⟩
  obtain ⟨z,hz,hassemble⟩ := BitMachineStackEmbedding.outputs
    assembleSlot (cleared S) Label.assemble eAssemble Control.assemble
    (by intro q; rfl) (some .done)
    GaussStateAssemble16.program program (by intro l; rfl)
    localCfg v hhalt
  have h3 : run z
      ⟨some (.assemble (.copy 0 .scan)),eAssemble ((),none),
        cleared S⟩ =
      BitMachineStackEmbedding.cfg assembleSlot (cleared S)
        Label.assemble eAssemble (some .done)
        (GaussStateAssemble16.run v localCfg) := by
    simpa [assemble_frame s S hw,localCfg] using hassemble
  have htotal : run (1+u+1+z)
      ⟨some .afterJoin,ctrl,S⟩ =
      BitMachineStackEmbedding.cfg assembleSlot (cleared S)
        Label.assemble eAssemble (some .done)
        (GaussStateAssemble16.run v localCfg) := by
    rw [show 1+u+1+z = 1+(u+(1+z)) by omega,
      run_add h0 (u+(1+z)),run_add h1 (1+z),
      run_add h2 z]
    exact h3
  refine ⟨1+u+1+z, by omega, ?_, ?_⟩
  · rw [htotal]
    have hh : (GaussStateAssemble16.run v localCfg).l = none :=
      hhalt
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg]
    rw [hh]
  · rw [htotal]
    change (BitMachineStackEmbedding.cfg assembleSlot (cleared S)
      Label.assemble eAssemble (some .done)
      (GaussStateAssemble16.run v localCfg)).stk
        (assembleSlot (14 : Fin 16)) = _
    change (BitMachineStackEmbedding.bank assembleSlot (cleared S)
      (GaussStateAssemble16.run v localCfg).stk)
        (assembleSlot (14 : Fin 16)) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact hpacket

#print axioms finish_state

end
end CurrentAdditive.GaussStepFinish32
