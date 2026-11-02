import CurrentAdditive.GaussGridInputPolynomial
import CurrentAdditive.GaussGridSerializerWhole64
import CurrentAdditive.GaussSearchGridBridge64

namespace CurrentAdditive.GaussSearchGridInvoke
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev M := GaussGridPreparedInput.finiteBitMachine
abbrev Bank := MachineInvokeCore.StackN (32+M.stackCount)
def low : Fin 64 ↪ Bank := ⟨fun i => ⟨i.val,by have hi:=i.isLt; omega⟩,by
  intro a b h; exact Fin.ext (congrArg (fun z : Bank => z.val) h)⟩
def frame (S : Fin 64 → List Bool) : Bank → List Bool :=
  BitMachineStackEmbedding.bank low (fun _ => []) S

theorem frame_at (S : Fin 64 → List Bool) (j : Fin 64) : frame S (low j)=S j :=
  BitMachineStackEmbedding.bank_at low (fun _ => []) S j
theorem frame_high (S : Fin 64 → List Bool) (j : Bank) (hj : 64≤j.val) :
    frame S j=[] := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i,hi⟩
  have he:=congrArg Fin.val hi
  have hb:=i.isLt
  dsimp [low] at he
  omega

def slots : MachineInvokeCore.Slots M (32+M.stackCount) where
  machine := ⟨fun i => ⟨64+i.val,by have hi:=i.isLt; omega⟩,by
    intro a b h; apply Fin.ext; have hv:=congrArg Fin.val h
    dsimp at hv; omega⟩
  source := low 62
  target := low 22
  scratch := low 63
  source_target := by intro h; have hv:=congrArg Fin.val h; change (62:Nat)=22 at hv; omega
  source_scratch := by intro h; have hv:=congrArg Fin.val h; change (62:Nat)=63 at hv; omega
  target_scratch := by intro h; have hv:=congrArg Fin.val h; change (22:Nat)=63 at hv; omega
  source_machine := by intro i h; have hv:=congrArg Fin.val h; change 62=64+i.val at hv; omega
  target_machine := by intro i h; have hv:=congrArg Fin.val h; change 22=64+i.val at hv; omega
  scratch_machine := by intro i h; have hv:=congrArg Fin.val h; change 63=64+i.val at hv; omega

def serializerProgram (l : BitMachineBankSerialize.Label 4) :=
  BitMachineStackEmbedding.stmt low id id id none (GaussSearchGridInput64.program l)
def serialized64 (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool) : Fin 64 → List Bool :=
  (BitMachineStackEmbedding.cfg GaussSearchGridInput64.location S id id none
    (BitMachineBankSerialize.cfg none none sf [] [] (GaussSearchGridInput64.packet S))).stk

theorem serialized_source (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool) :
    serialized64 S sf 62=GaussSearchGridInput64.packet S := by
  change BitMachineStackEmbedding.bank GaussSearchGridInput64.location S
    (BitMachineBankSerialize.cfg none none sf [] [] (GaussSearchGridInput64.packet S)).stk
      (GaussSearchGridInput64.location (.inr 2))=_
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem serialized_other (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool)
    (j : Fin 64) (hj : j.val∉[8,53,19,55,60,61,62]) :
    serialized64 S sf j=S j := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨v,hv⟩
  have he:=congrArg Fin.val hv
  cases v with
  | inl v => fin_cases v <;> simp [GaussSearchGridInput64.location] at he <;>
      simp_all
  | inr v => fin_cases v <;> simp [GaussSearchGridInput64.location] at he <;>
      simp_all

theorem serialize_run (S : Fin 64 → List Bool)
    (h60 : S 60=[]) (h61 : S 61=[]) (h62 : S 62=[]) :
    ∃ t≤2*(GaussSearchGridInput64.packet S).length+2,∃ sf : Fin 4 → List Bool,
      ((advance serializerProgram)^[t])
        (⟨some (.emit 0),none,frame S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ (Option Bool))=
        ⟨none,none,frame (serialized64 S sf)⟩ := by
  obtain ⟨a,ha,sf,hrun⟩:=GaussGridSerializerWhole64.physical_serialize S h60 h61 h62
  have hrun' : ((advance GaussSearchGridInput64.program)^[a])
      (GaussSearchGridInput64.initial S)=⟨none,none,serialized64 S sf⟩ := hrun
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs low (fun _ => []) id id id
    (by intro z; rfl) none GaussSearchGridInput64.program serializerProgram
    (by intro l; rfl) (GaussSearchGridInput64.initial S) a (by rw [hrun'])
  rw [hrun'] at he
  exact ⟨t,ht.trans ha,sf,he⟩

inductive ClearLabel where | scan | done deriving DecidableEq,Fintype
abbrev ClearControl := Unit × Option Bool
def clearProgram : ClearLabel → TM2.Stmt (fun _ : Bank => Bool) ClearLabel ClearControl
  | .scan => BitMachineClearBank.clearStep (low 22) .scan .done
  | .done => .halt

theorem clear_run (S : Bank → List Bool) :
    ((advance clearProgram)^[(S (low 22)).length+2])
      (⟨some .scan,((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,((),none),Function.update S (low 22) []⟩ := by
  have h:=BitMachineClearBank.clear_one_run clearProgram (low 22) .scan .done rfl () S
  rw [show (S (low 22)).length+2=((S (low 22)).length+1)+1 by omega,
    Function.iterate_succ_apply',h]
  rfl

def afterClear (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool) : Bank → List Bool :=
  Function.update (frame (serialized64 S sf)) (low 22) []
def finalBank (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool) (result : List Bool) : Bank → List Bool :=
  Function.update (frame (serialized64 S sf)) (low 22) result

def bodyProgram := BitMachineRawSequence.program clearProgram (MachineInvokeFull.program slots)
  (MachineInvokeFull.start slots) ((),none) (MachineInvokeFull.control slots)
abbrev BodyLabel := BitMachineRawSequence.Label ClearLabel (MachineInvokeFull.LabelFull M)
abbrev BodyControl := BitMachineRawSequence.Control ClearControl (MachineInvokeFull.ControlFull M)
def bodyStart : BodyLabel := BitMachineRawSequence.leftLabel .scan
def bodyControl : BodyControl := (((),none),MachineInvokeFull.control slots)
def program := BitMachineRawSequence.program serializerProgram bodyProgram bodyStart none bodyControl
abbrev Label := BitMachineRawSequence.Label (BitMachineBankSerialize.Label 4) BodyLabel
abbrev Control := BitMachineRawSequence.Control (Option Bool) BodyControl
def start : Label := BitMachineRawSequence.leftLabel (.emit 0)
def control : Control := (none,bodyControl)
def clock (S : Fin 64 → List Bool) : Nat :=
  2*(GaussSearchGridInput64.packet S).length+2+(S 22).length+2+
    MachineInvokeFull.uniformBound M (GaussSearchGridInput64.packet S)
      (GaussGridInputPolynomial.gridPolynomialClock (GaussSearchGridInput64.packet S).length)+2

/-- The dirty low target is cleared before the fixed grid machine is invoked.
The entire final bank is specified, including cleanup of every new machine
stack and preservation of the tag and saved original state outside the call. -/
theorem physical_rewrite {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (hn : B pivot c≠0)
    (S : Fin 64 → List Bool)
    (hpacket : GaussSearchGridInput64.packet S=
      BitMachineBankCodec.encode (GaussGridPreparedInput.rawWords B r pivot c))
    (h60 : S 60=[]) (h61 : S 61=[]) (h62 : S 62=[]) (h63 : S 63=[]) :
    ∃ t≤clock S,∃ sf : Fin 4 → List Bool,
      ((advance program)^[t])
        (⟨some start,control,frame S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control)=
        ⟨none,control,finalBank S sf (GaussGridPreparedInput.answer B r pivot c)⟩ := by
  obtain ⟨a,ha,sf,hser⟩:=serialize_run S h60 h61 h62
  have hclear:=clear_run (frame (serialized64 S sf))
  have htarget : afterClear S sf slots.target=[] := by simp [afterClear,slots]
  have hsource : afterClear S sf slots.source=GaussSearchGridInput64.packet S := by
    change Function.update (frame (serialized64 S sf)) (low 22) [] (low 62)=_
    rw [Function.update_of_ne (low.injective.ne (by decide)),frame_at,serialized_source]
  have hscratch : afterClear S sf slots.scratch=[] := by
    change Function.update (frame (serialized64 S sf)) (low 22) [] (low 63)=_
    rw [Function.update_of_ne (low.injective.ne (by decide)),frame_at,
      serialized_other S sf 63 (by decide),h63]
  have hblank (i : Fin M.stackCount) : afterClear S sf (slots.machine i)=[] := by
    have hne : slots.machine i≠low 22 := by
      intro he; have hv:=congrArg Fin.val he; dsimp [slots,low] at hv; omega
    rw [afterClear,Function.update_of_ne hne]
    apply frame_high
    dsimp [slots]
    omega
  have hm:=GaussGridInputPolynomial.outputs_polynomial B r pivot c hn
  rw [←hpacket] at hm
  obtain ⟨b,hb,hinvoke⟩:=MachineInvokeFull.invoke_run_uniform slots (afterClear S sf)
    (GaussSearchGridInput64.packet S) (GaussGridPreparedInput.answer B r pivot c)
    (GaussGridInputPolynomial.gridPolynomialClock (GaussSearchGridInput64.packet S).length)
    hsource htarget hscratch hblank hm
  have hfinal : Function.update (afterClear S sf) slots.target
      (GaussGridPreparedInput.answer B r pivot c)=
      finalBank S sf (GaussGridPreparedInput.answer B r pivot c) := by
    simp only [afterClear,slots,Function.update_idem,finalBank]
  rw [hfinal] at hinvoke
  obtain ⟨u,hu,hbody⟩:=BitMachineRawSequence.runs clearProgram (MachineInvokeFull.program slots)
    .scan (MachineInvokeFull.start slots) ((),none) ((),none)
    (MachineInvokeFull.control slots) (MachineInvokeFull.control slots)
    (frame (serialized64 S sf)) (afterClear S sf)
    (finalBank S sf (GaussGridPreparedInput.answer B r pivot c))
    ((frame (serialized64 S sf) (low 22)).length+2) b hclear hinvoke
  obtain ⟨t,ht,hall⟩:=BitMachineRawSequence.runs serializerProgram bodyProgram
    (.emit 0) bodyStart none none bodyControl bodyControl (frame S)
    (frame (serialized64 S sf)) (finalBank S sf (GaussGridPreparedInput.answer B r pivot c))
    a u hser hbody
  have h22 : frame (serialized64 S sf) (low 22)=S 22 := by
    rw [frame_at,serialized_other S sf 22 (by decide)]
  exact ⟨t,by unfold clock; rw [h22] at hu; omega,sf,hall⟩

theorem final_fields (S : Fin 64 → List Bool) (sf : Fin 4 → List Bool) (result : List Bool) :
    finalBank S sf result (low 22)=result ∧
    finalBank S sf result (low 20)=S 20 ∧
    finalBank S sf result (low 56)=S 56 ∧
    finalBank S sf result (low 63)=S 63 ∧
    ∀ i : Fin M.stackCount,finalBank S sf result (slots.machine i)=[] := by
  refine ⟨by simp [finalBank],?_,?_,?_,?_⟩
  · rw [finalBank,Function.update_of_ne (low.injective.ne (by decide)),frame_at,
      serialized_other S sf 20 (by decide)]
  · rw [finalBank,Function.update_of_ne (low.injective.ne (by decide)),frame_at,
      serialized_other S sf 56 (by decide)]
  · rw [finalBank,Function.update_of_ne (low.injective.ne (by decide)),frame_at,
      serialized_other S sf 63 (by decide)]
  · intro i
    have hne : slots.machine i≠low 22 := by
      intro he; have hv:=congrArg Fin.val he; dsimp [slots,low] at hv; omega
    rw [finalBank,Function.update_of_ne hne]
    apply frame_high
    dsimp [slots]; omega

theorem searched_scratch63 {m k : Nat} (s : GaussControlTrace.State m k)
    (Sf : Fin 32 → List Bool) : GaussPivotSearchHigh64.searched s Sf 63=[] := by
  rw [GaussPivotSearchHigh64.searched_high s Sf 63 (by decide)]
  exact SourceClausePreservingBroadcast.temp_empty 13 63 [58]
    (List.replicate m true) (GaussPivotPrepSave64.afterP s)

#print axioms physical_rewrite
#print axioms final_fields
#print axioms searched_scratch63
end
end CurrentAdditive.GaussSearchGridInvoke
