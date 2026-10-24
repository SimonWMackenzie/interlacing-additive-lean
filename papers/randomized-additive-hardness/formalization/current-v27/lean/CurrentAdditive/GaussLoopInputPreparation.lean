import CurrentAdditive.GaussIterationPacketMachine
import CurrentAdditive.GaussInitialPacket
import CurrentAdditive.GaussMatrixDimensions64

namespace CurrentAdditive.GaussLoopInputPreparation
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
abbrev I:=GaussInitialMachine.machine
abbrev C:=GaussMatrixDimensions64.columnsMachine
abbrev N:=I.stackCount+C.stackCount
abbrev Bank:=MachineInvokeCore.StackN N
def low : Fin 32 ↪ Bank:=⟨fun i => ⟨i.val,by have h:=i.isLt; omega⟩,by
  intro a b h; exact Fin.ext (congrArg (fun z : Bank => z.val) h)⟩
def firstSlots : MachineInvokeCore.Slots I N where
  machine:=⟨fun i => ⟨32+i.val,by have h:=i.isLt; dsimp only [N]; omega⟩,by
    intro a b h; apply Fin.ext; have hv:=congrArg Fin.val h; dsimp at hv; omega⟩
  source:=low 0
  target:=low 1
  scratch:=low 31
  source_target:=by intro h; have hv:=congrArg Fin.val h; change (0:Nat)=1 at hv; omega
  source_scratch:=by intro h; have hv:=congrArg Fin.val h; change (0:Nat)=31 at hv; omega
  target_scratch:=by intro h; have hv:=congrArg Fin.val h; change (1:Nat)=31 at hv; omega
  source_machine:=by intro i h; have hv:=congrArg Fin.val h; change 0=32+i.val at hv; omega
  target_machine:=by intro i h; have hv:=congrArg Fin.val h; change 1=32+i.val at hv; omega
  scratch_machine:=by intro i h; have hv:=congrArg Fin.val h; change 31=32+i.val at hv; omega
def countSlots : MachineInvokeCore.Slots C N where
  machine:=⟨fun i => ⟨32+I.stackCount+i.val,by have h:=i.isLt; dsimp only [N]; omega⟩,by
    intro a b h; apply Fin.ext; have hv:=congrArg Fin.val h; dsimp at hv; omega⟩
  source:=low 0
  target:=low 2
  scratch:=low 31
  source_target:=by intro h; have hv:=congrArg Fin.val h; change (0:Nat)=2 at hv; omega
  source_scratch:=by intro h; have hv:=congrArg Fin.val h; change (0:Nat)=31 at hv; omega
  target_scratch:=by intro h; have hv:=congrArg Fin.val h; change (2:Nat)=31 at hv; omega
  source_machine:=by intro i h; have hv:=congrArg Fin.val h; change 0=32+I.stackCount+i.val at hv; omega
  target_machine:=by intro i h; have hv:=congrArg Fin.val h; change 2=32+I.stackCount+i.val at hv; omega
  scratch_machine:=by intro i h; have hv:=congrArg Fin.val h; change 31=32+I.stackCount+i.val at hv; omega
def serializerMap : Fin 2 ⊕ Fin 3 → Bank
  | .inl i => ![low 1,low 2] i
  | .inr i => ![low 3,low 4,low 5] i
def serializerSlots : (Fin 2 ⊕ Fin 3) ↪ Bank:=⟨serializerMap,by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [serializerMap]
    | inr b => fin_cases a <;> fin_cases b <;> simp [serializerMap] at h
  | inr a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp [serializerMap] at h
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [serializerMap]⟩
def firstProgram:=MachineInvokeFull.program firstSlots
def countProgram:=MachineInvokeFull.program countSlots
def serializerProgram:=GaussCellCursorEmbedding.relocate serializerSlots (BitMachineBankSerialize.program 2)
abbrev BodyLabel:=BitMachineRawSequence.Label (MachineInvokeFull.LabelFull C) (BitMachineBankSerialize.Label 2)
abbrev BodyControl:=BitMachineRawSequence.Control (MachineInvokeFull.ControlFull C) (Option Bool)
def bodyProgram:=BitMachineRawSequence.program countProgram serializerProgram (.emit 0)
  (MachineInvokeFull.control countSlots) none
def bodyStart : BodyLabel:=BitMachineRawSequence.leftLabel (MachineInvokeFull.start countSlots)
def bodyControl : BodyControl:=(MachineInvokeFull.control countSlots,(none : Option Bool))
abbrev Label:=BitMachineRawSequence.Label (MachineInvokeFull.LabelFull I) BodyLabel
abbrev Control:=BitMachineRawSequence.Control (MachineInvokeFull.ControlFull I) BodyControl
def program:=BitMachineRawSequence.program firstProgram bodyProgram bodyStart
  (MachineInvokeFull.control firstSlots) bodyControl
def start : Label:=BitMachineRawSequence.leftLabel (MachineInvokeFull.start firstSlots)
def control : Control:=(MachineInvokeFull.control firstSlots,bodyControl)
def machine : BitMachine.Machine:=ofFinite (low 0) (low 5) start control program
def initialBank (matrix : List Bool) : Bank → List Bool:=fun j => if j=low 0 then matrix else []
def packetCap (n : Nat) : Nat:=8*n+30
def clock (n : Nat) : Nat:=MachineInvokeFull.uniformBound I (List.replicate n true) (3*n+8)+
  MachineInvokeFull.uniformBound C (List.replicate n true) (GaussMatrixDimensions64.columnsClock n)+
  2*packetCap n+4

theorem packet_length {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    (BitMachineBankCodec.encode (GaussIterationPacketMachine.words B)).length ≤
      packetCap (GaussPhysical.encodeTypedMatrix B).length := by
  have hk:=GaussInitialByteDimensions.columns_le_initial_bytes B hm
  have hs:=BitMachine.output_length_bound I (GaussInitialPacket.initial_state_output B)
  have hpacket : (GaussControlTrace.statePacket (GaussControlTrace.initial B)).length=
      2*(GaussPhysical.encodeTypedMatrix B).length+6 := by
    simp [GaussControlTrace.statePacket_length,GaussControlTrace.initial,
      GaussControlTrace.pivotsPacket,SourceListEncoding.encode,SourceListEncoding.fields,
      EncodedCommunication.natField,EncodedCommunication.field]
    omega
  rw [BitMachineBankCodec.encode_length]
  simp only [GaussIterationPacketMachine.words,Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,List.length_replicate]
  unfold packetCap
  omega

theorem serialize_run (S : Bank → List Bool) (h3 : S (low 3)=[]) (h4 : S (low 4)=[]) (h5 : S (low 5)=[]) :
    ∃t ≤ 2*(BitMachineBankCodec.encode ![S (low 1),S (low 2)]).length+2,
      ∃v : Option Bool,∃T : Bank → List Bool,((advance serializerProgram)^[t])
        (⟨some (.emit 0),(none : Option Bool),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=
          ⟨none,v,T⟩ ∧ T (low 5)=BitMachineBankCodec.encode ![S (low 1),S (low 2)] := by
  let w : Fin 2 → List Bool:=![S (low 1),S (low 2)]
  obtain ⟨a,sf,ha,hser⟩:=BitMachineBankSerialize.serialize w [] []
  let c:=BitMachineBankSerialize.cfg (some (.emit 0)) none w [] [] []
  have hcode : BitMachineBankSerialize.encode (List.ofFn w)=BitMachineBankCodec.encode w := by
    simp [BitMachineBankSerialize.encode,BitMachineBankCodec.encode_eq_list]
  have hser' : ((advance (BitMachineBankSerialize.program 2))^[a]) c=
      BitMachineBankSerialize.cfg none none sf [] [] (BitMachineBankCodec.encode w) := by
    simpa only [c,BitMachineBankSerialize.run,List.append_nil,hcode] using hser
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs serializerSlots S id id id (fun _ => rfl)
    none (BitMachineBankSerialize.program 2) serializerProgram (fun _ => rfl) c a (by rw [hser']; rfl)
  have hbank : BitMachineStackEmbedding.bank serializerSlots S c.stk=S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro j
    cases j with
    | inl j => fin_cases j <;> rfl
    | inr j =>
      fin_cases j
      · simpa [serializerSlots,serializerMap,c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents]
          using h3.symm
      · simpa [serializerSlots,serializerMap,c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents]
          using h4.symm
      · simpa [serializerSlots,serializerMap,c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents]
          using h5.symm
  have hstart : BitMachineStackEmbedding.cfg serializerSlots S id id none c=
      (⟨some (.emit 0),none,S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) := by
    simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq]
    rw [hbank]
    rfl
  rw [hstart,hser'] at he
  refine ⟨t,ht.trans (by simpa only [hcode,w] using ha),_,_,he,?_⟩
  change BitMachineStackEmbedding.bank serializerSlots S _ (serializerSlots (.inr 2))=_
  rw [BitMachineStackEmbedding.bank_at]
  rfl

/-- From the matrix alone the fixed program writes the initial state, counts
the actual columns, and serializes the exact state/fuel packet. -/
theorem outputs {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    machine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
      (BitMachineBankCodec.encode (GaussIterationPacketMachine.words B))
      (clock (GaussPhysical.encodeTypedMatrix B).length) := by
  let matrix:=GaussPhysical.encodeTypedMatrix B
  let state:=GaussControlTrace.statePacket (GaussControlTrace.initial B)
  let S:=initialBank matrix
  let S1:=Function.update S (low 1) state
  let S2:=Function.update S1 (low 2) (List.replicate k true)
  obtain ⟨a,ha,hfirst⟩:=MachineInvokeFull.invoke_run_uniform firstSlots S matrix state
    (3*matrix.length+8) rfl (by simp [S,initialBank,firstSlots,low,Fin.ext_iff])
    (by simp [S,initialBank,firstSlots,low,Fin.ext_iff])
    (by intro j; simp [S,initialBank,firstSlots,low,Fin.ext_iff]) (GaussInitialPacket.initial_state_output B)
  obtain ⟨b,hb,hcount⟩:=MachineInvokeFull.invoke_run_uniform countSlots S1 matrix (List.replicate k true)
    (GaussMatrixDimensions64.columnsClock matrix.length)
    (by simp [S1,S,initialBank,countSlots,low,Function.update_apply,Fin.ext_iff])
    (by simp [S1,S,initialBank,countSlots,low,Function.update_apply,Fin.ext_iff])
    (by simp [S1,S,initialBank,countSlots,low,Function.update_apply,Fin.ext_iff])
    (by intro j; simp [S1,S,initialBank,countSlots,low,Function.update_apply,Fin.ext_iff]; omega)
    (GaussMatrixDimensions64.typed_columns B hm)
  obtain ⟨c,hc,v,T,hser,h5⟩:=serialize_run S2
    (by simp [S2,S1,S,initialBank,low,Fin.ext_iff])
    (by simp [S2,S1,S,initialBank,low,Fin.ext_iff])
    (by simp [S2,S1,S,initialBank,low,Fin.ext_iff])
  obtain ⟨d,hd,hbody⟩:=BitMachineRawSequence.runs countProgram serializerProgram
    (MachineInvokeFull.start countSlots) (.emit 0) (MachineInvokeFull.control countSlots)
    (MachineInvokeFull.control countSlots) none v S1 S2 T b c hcount hser
  obtain ⟨t,ht,he⟩:=BitMachineRawSequence.runs firstProgram bodyProgram
    (MachineInvokeFull.start firstSlots) bodyStart (MachineInvokeFull.control firstSlots)
    (MachineInvokeFull.control firstSlots) bodyControl (MachineInvokeFull.control countSlots,v)
    S S1 T a d hfirst hbody
  have hwords : ![S2 (low 1),S2 (low 2)]=GaussIterationPacketMachine.words B := by
    funext j
    fin_cases j <;> simp [S2,S1,GaussIterationPacketMachine.words,state,low,Fin.ext_iff]
  rw [hwords] at hc h5
  have hp:=packet_length B hm
  have ha' : a ≤ MachineInvokeFull.uniformBound I (List.replicate matrix.length true) (3*matrix.length+8) := by
    simpa only [MachineInvokeFull.uniformBound,List.length_replicate] using ha
  have hb' : b ≤ MachineInvokeFull.uniformBound C (List.replicate matrix.length true)
      (GaussMatrixDimensions64.columnsClock matrix.length) := by
    simpa only [MachineInvokeFull.uniformBound,List.length_replicate] using hb
  have hfull : ((advance program)^[t]) (rawInit (low 0) start control matrix)=
      ⟨none,(MachineInvokeFull.control firstSlots,MachineInvokeFull.control countSlots,v),T⟩:=he
  apply outputsWithin_of_raw_run (low 0) (low 5) start control program matrix
    (BitMachineBankCodec.encode (GaussIterationPacketMachine.words B)) t _
    (by unfold clock; dsimp only [matrix] at *; omega)
  · change (((advance program)^[t]) _).l=none
    rw [hfull]
  · change (((advance program)^[t]) _).stk (low 5)=_
    rw [hfull]
    exact h5

#print axioms serialize_run
#print axioms outputs
end
end CurrentAdditive.GaussLoopInputPreparation
