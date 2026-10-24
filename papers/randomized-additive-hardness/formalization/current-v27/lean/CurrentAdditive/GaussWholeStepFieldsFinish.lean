import CurrentAdditive.GaussWholeStepProgram

namespace CurrentAdditive.GaussWholeStepFieldsFinish
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram

/-- Internal composition of a local field run with the actual output transfer.
The field run is later instantiated by the concrete pivot/no-pivot routines.
All discarded output62 bytes and all copied answer bytes are charged. -/
theorem physical_finish (S T : Fin 64 → List Bool) (t : Nat)
    (v : GaussNextStateFields64.Control) (answer : List Bool)
    (hfields : ((advance GaussNextStateFields64.program)^[t])
      (GaussNextStateFields64.initial S)=⟨none,v,T⟩)
    (h14 : T 14=answer) (h62 : T 62=S 62) (h63 : T 63=[]) :
    ∃ u≤t+(S 62).length+2*answer.length+8,
      ∃ w : Control,∃ U : Bank → List Bool,
      run u ⟨some (.fields GaussNextStateFields64.start),eFields GaussNextStateFields64.control,frame S⟩=
        ⟨none,w,U⟩ ∧ U (low 62)=answer := by
  obtain ⟨a,ha,hwide⟩ := BitMachineStackEmbedding.outputs low (fun _ : Bank => []) id id id
    (fun _ => rfl) none GaussNextStateFields64.program fieldsProgram (fun _ => rfl)
    (GaussNextStateFields64.initial S) t (by rw [hfields])
  rw [hfields] at hwide
  have hwide' : ((advance fieldsProgram)^[a])
      (⟨some GaussNextStateFields64.start,GaussNextStateFields64.control,frame S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _)=⟨none,v,frame T⟩ := hwide
  obtain ⟨b,hb,hglobal⟩ := BitMachineInline.outputs Label.fields eFields readFields
    (fun _ => rfl) (some .afterFields) fieldsProgram program (fun _ => rfl)
    (⟨some GaussNextStateFields64.start,GaussNextStateFields64.control,frame S⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _) a (by rw [hwide'])
  rw [hwide'] at hglobal
  have hfield : run b
      ⟨some (.fields GaussNextStateFields64.start),eFields GaussNextStateFields64.control,frame S⟩=
      ⟨some .afterFields,eFields v,frame T⟩ := hglobal
  have hnext : run 1 ⟨some .afterFields,eFields v,frame T⟩=
      ⟨some (.transfer GaussStepOutputTransfer.start),eTransfer GaussStepOutputTransfer.control,frame T⟩ := rfl
  obtain ⟨c,hc,htransfer⟩ := GaussStepOutputTransfer.physical_transfer (frame T)
    (by rw [GaussSearchGridInvoke.frame_at,h63])
  obtain ⟨d,hd,htransGlobal⟩ := BitMachineInline.outputs Label.transfer eTransfer readTransfer
    (fun _ => rfl) (some .done) GaussStepOutputTransfer.program program (fun _ => rfl)
    (⟨some GaussStepOutputTransfer.start,GaussStepOutputTransfer.control,frame T⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _) c (by rw [htransfer])
  rw [htransfer] at htransGlobal
  let U := Function.update (frame T) (low 62) ((frame T) (low 14))
  have htrans : run d
      ⟨some (.transfer GaussStepOutputTransfer.start),eTransfer GaussStepOutputTransfer.control,frame T⟩=
      ⟨some .done,eTransfer GaussStepOutputTransfer.control,U⟩ := htransGlobal
  have hall : run (b+1+d+1)
      ⟨some (.fields GaussNextStateFields64.start),eFields GaussNextStateFields64.control,frame S⟩=
      ⟨none,eTransfer GaussStepOutputTransfer.control,U⟩ := by
    rw [show b+1+d+1=b+(1+(d+1)) by omega,run_add hfield (1+(d+1)),
      run_add hnext (d+1),run_add htrans 1]
    rfl
  refine ⟨b+1+d+1,?_,eTransfer GaussStepOutputTransfer.control,U,hall,?_⟩
  · unfold GaussStepOutputTransfer.clock at hc
    rw [GaussSearchGridInvoke.frame_at,GaussSearchGridInvoke.frame_at,h14,h62] at hc
    omega
  · simp only [U,Function.update_self,GaussSearchGridInvoke.frame_at,h14]

#print axioms physical_finish
end
end CurrentAdditive.GaussWholeStepFieldsFinish
