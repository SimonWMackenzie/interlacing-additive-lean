import CurrentAdditive.GaussCertificateStageJoin
import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

set_option maxRecDepth 2048

/-! A wider, fixed ambient bank embeds the checked post-Gauss work-list
program and reserves disjoint cells for the coefficient-vector machine. -/

namespace CurrentAdditive.GaussWideVectorInvoke

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

noncomputable abbrev VectorMachine :=
  GaussVectorOuterWriter.machine GaussCoefficientProgram.machine
noncomputable abbrev BaseCount :=
  GaussStateMatrixContext.Sel.stackCount + GaussStateMatrixContext.Proj.stackCount
noncomputable abbrev Count := BaseCount + VectorMachine.stackCount
abbrev OldBank := MachineInvokeCore.StackN BaseCount
abbrev Bank := MachineInvokeCore.StackN Count

noncomputable def oldEmbed : OldBank ↪ Bank where
  toFun i := ⟨i.val, by
    have hi : i.val < 32 + BaseCount := i.isLt
    dsimp only [Count]
    omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun (x : Bank) => x.val) h

noncomputable def vectorEmbed (i : Fin VectorMachine.stackCount) : Bank :=
  ⟨32 + BaseCount + i.val, by
    have hi := i.isLt
    dsimp only [Count]
    omega⟩

theorem vectorEmbed_inj : Function.Injective vectorEmbed := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  change 32 + BaseCount + a.val = 32 + BaseCount + b.val at this
  omega

noncomputable def slots : MachineInvokeCore.Slots VectorMachine Count where
  machine := ⟨vectorEmbed, vectorEmbed_inj⟩
  source := ⟨24, by omega⟩
  target := ⟨25, by omega⟩
  scratch := ⟨26, by omega⟩
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 24 = 32 + BaseCount + i.val at hv
    omega
  target_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 25 = 32 + BaseCount + i.val at hv
    omega
  scratch_machine := by
    intro i h
    have hv := congrArg Fin.val h
    change 26 = 32 + BaseCount + i.val at hv
    omega

noncomputable def wide (S : OldBank → List Bool) : Bank → List Bool :=
  BitMachineStackEmbedding.bank oldEmbed (fun _ => []) S

theorem wide_at (S : OldBank → List Bool) (j : OldBank) :
    wide S (oldEmbed j) = S j :=
  BitMachineStackEmbedding.bank_at oldEmbed (fun _ => []) S j

theorem wide_vector_blank (S : OldBank → List Bool)
    (i : Fin VectorMachine.stackCount) :
    wide S (vectorEmbed i) = [] := by
  apply BitMachineStackEmbedding.bank_outside oldEmbed (fun _ => []) S
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = 32 + BaseCount + i.val at hv
  have hlt : j.val < 32 + BaseCount := j.isLt
  omega

private abbrev InputLabel {α β : Type} (_ : α → β) : Type := α
abbrev OldLabel := InputLabel GaussActualWorkList.program
abbrev NewLabel := InputLabel (MachineInvokeFull.program slots)

noncomputable def liftedProgram (l : OldLabel) :=
  BitMachineStackEmbedding.stmt oldEmbed id id id
    (none : Option OldLabel) (GaussActualWorkList.program l)

noncomputable def program := BitMachineRawSequence.program
  liftedProgram (MachineInvokeFull.program slots)
  (MachineInvokeFull.start slots)
  GaussActualWorkList.control (MachineInvokeFull.control slots)

noncomputable def start : BitMachineRawSequence.Label OldLabel NewLabel :=
  BitMachineRawSequence.leftLabel GaussActualWorkList.start
noncomputable def control :=
  (GaussActualWorkList.control, MachineInvokeFull.control slots)

theorem fused_run (S T : OldBank → List Bool) (t : Nat)
    (out : List Bool) (clock : Nat)
    (hwork :
      ((advance GaussActualWorkList.program)^[t])
        (⟨some GaussActualWorkList.start, GaussActualWorkList.control, S⟩ :
          TM2.Cfg (fun _ : OldBank => Bool) _ _) =
        ⟨none, GaussActualWorkList.control, T⟩)
    (h25 : T ⟨25, by omega⟩ = [])
    (h26 : T ⟨26, by omega⟩ = [])
    (hvector : VectorMachine.OutputsWithin
      (T ⟨24, by omega⟩) out clock) :
    ∃ u ≤ t + MachineInvokeFull.uniformBound VectorMachine
        (T ⟨24, by omega⟩) clock + 1,
      ((advance program)^[u])
        (⟨some start, control, wide S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, control, Function.update (wide T) slots.target out⟩ := by
  let c : TM2.Cfg (fun _ : OldBank => Bool) _ _ :=
    ⟨some GaussActualWorkList.start, GaussActualWorkList.control, S⟩
  have hh : (((advance GaussActualWorkList.program)^[t]) c).l = none := by
    rw [hwork]
  obtain ⟨a, ha, hrA⟩ := BitMachineStackEmbedding.outputs
    oldEmbed (fun _ => []) id id id (by intro; rfl)
    (none : Option OldLabel)
    GaussActualWorkList.program liftedProgram (by intro; rfl)
    c t hh
  rw [hwork] at hrA
  have hrunA :
      ((advance liftedProgram)^[a])
        (⟨some GaussActualWorkList.start, GaussActualWorkList.control, wide S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, GaussActualWorkList.control, wide T⟩ := by
    simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, wide, c] using hrA
  have hsource : wide T slots.source = T ⟨24, by omega⟩ := by
    simpa only [slots, oldEmbed] using wide_at T (⟨24, by omega⟩ : OldBank)
  have htarget : wide T slots.target = [] := by
    simpa only [slots, oldEmbed] using
      (wide_at T (⟨25, by omega⟩ : OldBank)).trans h25
  have hscratch : wide T slots.scratch = [] := by
    simpa only [slots, oldEmbed] using
      (wide_at T (⟨26, by omega⟩ : OldBank)).trans h26
  obtain ⟨b, hb, hrB⟩ := MachineInvokeFull.invoke_run_uniform
    slots (wide T) (T ⟨24, by omega⟩) out clock
    hsource htarget hscratch (fun i => wide_vector_blank T i) hvector
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    liftedProgram (MachineInvokeFull.program slots)
    GaussActualWorkList.start (MachineInvokeFull.start slots)
    GaussActualWorkList.control GaussActualWorkList.control
    (MachineInvokeFull.control slots) (MachineInvokeFull.control slots)
    (wide S) (wide T) (Function.update (wide T) slots.target out)
    a b hrunA hrB
  refine ⟨u, ?_, ?_⟩
  · omega
  · simpa only [program, start, control] using hr

#print axioms fused_run

end CurrentAdditive.GaussWideVectorInvoke
