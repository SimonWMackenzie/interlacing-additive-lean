import CurrentAdditive.GaussMatrixDimensions64
import CurrentAdditive.MachineInvokeFull
import CurrentAdditive.GaussSerializeClears
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace CurrentAdditive.GaussInputDimensions
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

noncomputable def R := GaussRowCount.machine
noncomputable def C := GaussMatrixDimensions64.columnsMachine
abbrev Bank := MachineInvokeCore.StackN (R.stackCount+C.stackCount)
noncomputable def low (z : Fin 32) : Bank := ⟨z.val,by omega⟩

noncomputable def parseSlot : (Fin 4 ⊕ Fin 3) ↪ Bank :=
  ⟨fun z => match z with
    | .inl i => ⟨i.val,by omega⟩
    | .inr i => ⟨6+i.val,by omega⟩,by
    intro a b h
    have hv:=congrArg (fun z : Bank => z.val) h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext hv)
      | inr b => dsimp at hv; have ha:=a.isLt; omega
    | inr a => cases b with
      | inl b => dsimp at hv; have hb:=b.isLt; omega
      | inr b => exact congrArg Sum.inr (Fin.ext (by dsimp [low] at hv; omega))⟩

noncomputable def serSlot : (Fin 6 ⊕ Fin 3) ↪ Bank :=
  ⟨fun z => match z with
    | .inl i => ⟨i.val,by omega⟩
    | .inr i => ⟨6+i.val,by omega⟩,by
    intro a b h
    have hv:=congrArg (fun z : Bank => z.val) h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext hv)
      | inr b => dsimp at hv; have ha:=a.isLt; omega
    | inr a => cases b with
      | inl b => dsimp at hv; have hb:=b.isLt; omega
      | inr b => exact congrArg Sum.inr (Fin.ext (by dsimp [low] at hv; omega))⟩

noncomputable def rowSlots : MachineInvokeCore.Slots R (R.stackCount+C.stackCount) where
  machine := ⟨fun i => ⟨32+i.val,by have hi:=i.isLt; omega⟩,by
    intro a b h; exact Fin.ext (by have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega)⟩
  source := low 0
  target := low 4
  scratch := low 9
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega
  target_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega
  scratch_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega

noncomputable def colSlots : MachineInvokeCore.Slots C (R.stackCount+C.stackCount) where
  machine := ⟨fun i => ⟨32+R.stackCount+i.val,by have hi:=i.isLt; omega⟩,by
    intro a b h; exact Fin.ext (by have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega)⟩
  source := low 0
  target := low 5
  scratch := low 9
  source_target := by decide
  source_scratch := by decide
  target_scratch := by decide
  source_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega
  target_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega
  scratch_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [low] at hv; omega

noncomputable def parserProgram (l : BitMachineBankCodec.ParserLabel 4) :=
  BitMachineStackEmbedding.stmt parseSlot id id id none (BitMachineBankCodec.parser 4 l)
noncomputable def serializerProgram (l : BitMachineBankSerialize.Label 6) :=
  BitMachineStackEmbedding.stmt serSlot id id id none (BitMachineBankSerialize.program 6 l)
noncomputable def dimensionsProgram := BitMachineRawSequence.program
  (MachineInvokeFull.program rowSlots) (MachineInvokeFull.program colSlots)
  (MachineInvokeFull.start colSlots)
  (MachineInvokeFull.control rowSlots) (MachineInvokeFull.control colSlots)
noncomputable def dimensionsStart : BitMachineRawSequence.Label (MachineInvokeFull.LabelFull R) (MachineInvokeFull.LabelFull C) := BitMachineRawSequence.leftLabel (MachineInvokeFull.start rowSlots)
noncomputable def dimensionsControl := (MachineInvokeFull.control rowSlots,MachineInvokeFull.control colSlots)
noncomputable def p01 := BitMachineRawSequence.program parserProgram dimensionsProgram
  dimensionsStart none dimensionsControl
noncomputable def program := BitMachineRawSequence.program p01 serializerProgram (.emit 0)
  (none,dimensionsControl) none
abbrev DimensionLabel := BitMachineRawSequence.Label (MachineInvokeFull.LabelFull R) (MachineInvokeFull.LabelFull C)
abbrev DimensionControl := BitMachineRawSequence.Control (MachineInvokeFull.ControlFull R) (MachineInvokeFull.ControlFull C)
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 4) DimensionLabel)
  (BitMachineBankSerialize.Label 6)
abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control (Option Bool) DimensionControl) (Option Bool)
noncomputable def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (.scan 0))
noncomputable def control : Control := ((none,dimensionsControl),none)
noncomputable def finalControl : Control := control
noncomputable def fields (w : Fin 4 → List Bool) : Bank → List Bool :=
  fun z => if hz : z.val<4 then w ⟨z.val,hz⟩ else []

theorem fields_at (w : Fin 4 → List Bool) (i : Fin 4) :
    fields w (parseSlot (.inl i))=w i := by simp [fields,parseSlot,i.isLt]

theorem fields_high (w : Fin 4 → List Bool) (z : Bank) (hz : 4 ≤ z.val) :
    fields w z=[] := by simp [fields,show ¬z.val<4 by omega]

/-- The literal four-field parser fills exactly the four first banks. -/
theorem parse_run (w : Fin 4 → List Bool) :
    ∃ t ≤ 9*((BitMachineBankCodec.encode w).length+1),
      ((advance parserProgram)^[t])
        (rawInit (low 6) (.scan 0 : BitMachineBankCodec.ParserLabel 4) (none : Option Bool)
          (BitMachineBankCodec.encode w)) =
        ⟨none,some true,fields w⟩ := by
  obtain ⟨a,ha,hparse⟩:=BitMachineBankCodec.parser_correct 4 (BitMachineBankCodec.encode w) []
  rw [BitMachineBankCodec.decode_encode] at hparse
  change BitMachineBankCodec.parserRun a
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
      (BitMachineBankCodec.encode w) [] []) =
    BitMachineBankCodec.parserCfg none (some true) w [] [] [] at hparse
  let S:=fields w
  let initial:=BitMachineBankCodec.parserCfg (K:=4) (some (.scan 0)) none (fun _ => [])
    (BitMachineBankCodec.encode w) [] []
  have hbankInit : BitMachineStackEmbedding.bank parseSlot S initial.stk =
      (rawInit (low 6) (.scan 0 : BitMachineBankCodec.ParserLabel 4) (none : Option Bool)
        (BitMachineBankCodec.encode w)).stk := by
    funext z
    by_cases hz : z.val<4
    · let i : Fin 4:=⟨z.val,hz⟩
      have he : parseSlot (.inl i)=z := Fin.ext rfl
      rw [← he,BitMachineStackEmbedding.bank_at]
      have hne : parseSlot (.inl i)≠(low 6) := by
        intro h; have hv:=congrArg (fun z : Bank => z.val) h
        dsimp [parseSlot,low] at hv; omega
      simp [initial,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,rawInit,hne]
    by_cases h6 : z.val=6
    · have he : parseSlot (.inr (0 : Fin 3))=z := Fin.ext (by dsimp [parseSlot,low]; omega)
      rw [← he,BitMachineStackEmbedding.bank_at]
      rfl
    by_cases h7 : z.val=7
    · have he : parseSlot (.inr (1 : Fin 3))=z := Fin.ext (by dsimp [parseSlot,low]; omega)
      rw [← he,BitMachineStackEmbedding.bank_at]
      rfl
    by_cases h8 : z.val=8
    · have he : parseSlot (.inr (2 : Fin 3))=z := Fin.ext (by dsimp [parseSlot,low]; omega)
      rw [← he,BitMachineStackEmbedding.bank_at]
      rfl
    have hout : ¬∃ j,parseSlot j=z := by
      rintro ⟨j,hj⟩
      have hv:=congrArg (fun z : Bank => z.val) hj
      cases j with
      | inl j => dsimp [parseSlot,low] at hv; have hj:=j.isLt; omega
      | inr j => fin_cases j <;> simp [parseSlot] at hv <;> omega
    rw [BitMachineStackEmbedding.bank_outside parseSlot S _ z hout]
    have hne : z≠(low 6) := by intro h; exact h6 (congrArg (fun z : Bank => z.val) h)
    simp [S,fields,hz,rawInit,hne]
  have hbankFinal : BitMachineStackEmbedding.bank parseSlot S
      (BitMachineBankCodec.parserCfg none (some true) w [] [] []).stk=S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro z
    cases z with
    | inl i => exact (fields_at w i).symm
    | inr i => fin_cases i <;> simp [BitMachineBankCodec.parserCfg,
        BitMachineBankCodec.contents,S,fields,parseSlot]
  have hparse' : ((advance (BitMachineBankCodec.parser 4))^[a]) initial=
      BitMachineBankCodec.parserCfg none (some true) w [] [] [] := hparse
  have hhalt : (((advance (BitMachineBankCodec.parser 4))^[a]) initial).l=none :=
    congrArg (fun c => c.l) hparse'
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs parseSlot S id id id
    (by intro x; rfl) none (BitMachineBankCodec.parser 4) parserProgram (by intro l; rfl)
    initial a hhalt
  rw [hparse'] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq] at he
  rw [hbankInit,hbankFinal] at he
  exact ⟨t,ht.trans ha,he⟩

noncomputable def extended (w : Fin 4 → List Bool) (m k : Nat) : Fin 6 → List Bool :=
  ![w 0,w 1,w 2,w 3,List.replicate m true,List.replicate k true]

noncomputable def counted (w : Fin 4 → List Bool) (m k : Nat) : Bank → List Bool :=
  Function.update (Function.update (fields w) (low 4) (List.replicate m true)) (low 5) (List.replicate k true)

noncomputable def dimensionClock (matrix : List Bool) : Nat :=
  MachineInvokeFull.uniformBound R matrix (GaussRowCount.polynomialClock matrix.length)+
  MachineInvokeFull.uniformBound C matrix (GaussMatrixDimensions64.columnsClock matrix.length)+1

/-- Both dimensions are obtained by fixed actual machines reading the matrix;
none is passed as a unary source or supplied computation callback. -/
theorem dimension_run {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m)
    (w : Fin 4 → List Bool) (hw : w 0=GaussPhysical.encodeTypedMatrix B) :
    ∃ t ≤ dimensionClock (w 0),
      ((advance (BitMachineRawSequence.program (MachineInvokeFull.program rowSlots)
        (MachineInvokeFull.program colSlots) (MachineInvokeFull.start colSlots)
        (MachineInvokeFull.control rowSlots) (MachineInvokeFull.control colSlots)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (MachineInvokeFull.start rowSlots)),
          (MachineInvokeFull.control rowSlots,MachineInvokeFull.control colSlots),fields w⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none,(MachineInvokeFull.control rowSlots,MachineInvokeFull.control colSlots),counted w m k⟩ := by
  let S:=fields w
  have hsource : S rowSlots.source=w 0 := by simp [S,fields,rowSlots,low]
  have htarget : S rowSlots.target=[] := by simp [S,fields,rowSlots,low]
  have hscratch : S rowSlots.scratch=[] := by simp [S,fields,rowSlots,low]
  have hblank (i : Fin R.stackCount) : S (rowSlots.machine i)=[] := by
    apply fields_high; dsimp [rowSlots,low]; omega
  have hR : R.OutputsWithin (w 0) (List.replicate m true)
      (GaussRowCount.polynomialClock (w 0).length) := by
    rw [hw]
    exact GaussMatrixDimensions64.typed_rows B
  obtain ⟨a,ha,hrun⟩:=MachineInvokeFull.invoke_run_uniform rowSlots S (w 0)
    (List.replicate m true) _ hsource htarget hscratch hblank hR
  let S1:=Function.update S (low 4) (List.replicate m true)
  have hsource1 : S1 colSlots.source=w 0 := by simp [S1,S,fields,colSlots,low,Function.update_apply,Fin.ext_iff]
  have htarget1 : S1 colSlots.target=[] := by simp [S1,S,fields,colSlots,low,Function.update_apply,Fin.ext_iff]
  have hscratch1 : S1 colSlots.scratch=[] := by simp [S1,S,fields,colSlots,low,Function.update_apply,Fin.ext_iff]
  have hblank1 (i : Fin C.stackCount) : S1 (colSlots.machine i)=[] := by
    have hne : colSlots.machine i≠(low 4) := by
      intro h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [colSlots,low] at hv; omega
    change Function.update S (low 4) (List.replicate m true) (colSlots.machine i)=[]
    rw [Function.update_of_ne hne]
    apply fields_high; dsimp [colSlots,low]; omega
  have hC : C.OutputsWithin (w 0) (List.replicate k true)
      (GaussMatrixDimensions64.columnsClock (w 0).length) := by
    rw [hw]
    exact GaussMatrixDimensions64.typed_columns B hm
  obtain ⟨b,hb,hcols⟩:=MachineInvokeFull.invoke_run_uniform colSlots S1 (w 0)
    (List.replicate k true) _ hsource1 htarget1 hscratch1 hblank1 hC
  obtain ⟨t,ht,hfull⟩:=BitMachineRawSequence.runs
    (MachineInvokeFull.program rowSlots) (MachineInvokeFull.program colSlots)
    (MachineInvokeFull.start rowSlots) (MachineInvokeFull.start colSlots)
    (MachineInvokeFull.control rowSlots) (MachineInvokeFull.control rowSlots)
    (MachineInvokeFull.control colSlots) (MachineInvokeFull.control colSlots)
    S S1 (counted w m k) a b hrun hcols
  exact ⟨t,by unfold dimensionClock; omega,hfull⟩

noncomputable def outputPacket (w : Fin 4 → List Bool) (m k : Nat) : List Bool :=
  BitMachineBankCodec.encode (extended w m k)

noncomputable def serialized (w : Fin 4 → List Bool) (m k : Nat) : Bank → List Bool :=
  BitMachineStackEmbedding.bank serSlot (counted w m k)
    (BitMachineBankSerialize.cfg none none (fun _ : Fin 6 => []) [] []
      (outputPacket w m k)).stk

theorem serialize_run (w : Fin 4 → List Bool) (m k : Nat) :
    ∃ t ≤ 2*(outputPacket w m k).length+2,
      ((advance serializerProgram)^[t])
        (⟨some (.emit 0),none,counted w m k⟩ : TM2.Cfg (fun _ : Bank => Bool)
          (BitMachineBankSerialize.Label 6) (Option Bool)) =
        ⟨none,none,serialized w m k⟩ := by
  let c:=BitMachineBankSerialize.cfg (some (.emit 0)) none (extended w m k) [] [] []
  have hready : ∀ z,c.stk z=counted w m k (serSlot z) := by
    intro z
    cases z with
    | inl i =>
      change extended w m k i=counted w m k (serSlot (.inl i))
      fin_cases i <;> simp [counted,fields,serSlot,extended,low,Function.update_apply]
    | inr i =>
      fin_cases i <;> simp [c,BitMachineBankSerialize.cfg,BitMachineBankSerialize.contents,
        counted,fields,serSlot,low,Function.update_apply]
  have hbank:=BitMachineStackEmbedding.bank_eq_self serSlot (counted w m k) c.stk hready
  obtain ⟨a,ha,hser⟩:=GaussSerializeClears.serialize_empty (extended w m k) [] []
  have hpacket : BitMachineBankSerialize.encode (List.ofFn (extended w m k))=outputPacket w m k := by
    exact (BitMachineBankCodec.encode_eq_list (extended w m k)).symm
  simp only [List.append_nil] at hser
  rw [hpacket] at hser ha
  have hser' : ((advance (BitMachineBankSerialize.program 6))^[a]) c=
      BitMachineBankSerialize.cfg none none (fun _ => []) [] [] (outputPacket w m k) := hser
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs serSlot (counted w m k) id id id
    (by intro x; rfl) none (BitMachineBankSerialize.program 6) serializerProgram
    (by intro l; rfl) c a (by rw [hser']; rfl)
  rw [hser'] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg,id_eq] at he
  rw [hbank] at he
  exact ⟨t,ht.trans ha,he⟩

theorem serialized_output (w : Fin 4 → List Bool) (m k : Nat) :
    serialized w m k (low 8)=outputPacket w m k := by
  change BitMachineStackEmbedding.bank serSlot (counted w m k)
    (BitMachineBankSerialize.cfg none none (fun _ : Fin 6 => []) [] []
      (outputPacket w m k)).stk (serSlot (.inr 2))=_
  rw [BitMachineStackEmbedding.bank_at]
  rfl

noncomputable def clock (w : Fin 4 → List Bool) (m k : Nat) : Nat :=
  9*((BitMachineBankCodec.encode w).length+1)+dimensionClock (w 0)+
    2*(outputPacket w m k).length+4

/-- One fixed parser/count/serialize program preserves the original four words
and appends both dimensions computed from the physical typed matrix. -/
theorem physical_prepare {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m)
    (w : Fin 4 → List Bool) (hw : w 0=GaussPhysical.encodeTypedMatrix B) :
    ∃ t ≤ clock w m k,
      ((advance program)^[t]) (rawInit (low 6) start control (BitMachineBankCodec.encode w)) =
        ⟨none,finalControl,serialized w m k⟩ := by
  obtain ⟨a,ha,hparse⟩:=parse_run w
  obtain ⟨b,hb,hdim⟩:=dimension_run B hm w hw
  obtain ⟨c,hc,hser⟩:=serialize_run w m k
  let S0:=(rawInit (low 6) (.scan 0 : BitMachineBankCodec.ParserLabel 4) (none : Option Bool)
    (BitMachineBankCodec.encode w)).stk
  obtain ⟨u,hu,h01⟩:=BitMachineRawSequence.runs parserProgram dimensionsProgram
    (.scan 0) dimensionsStart none (some true) dimensionsControl dimensionsControl
    S0 (fields w) (counted w m k) a b hparse hdim
  obtain ⟨t,ht,hfull⟩:=BitMachineRawSequence.runs p01 serializerProgram
    (BitMachineRawSequence.leftLabel (.scan 0)) (.emit 0)
    (none,dimensionsControl) (none,dimensionsControl) none none
    S0 (counted w m k) (serialized w m k) u c h01 hser
  exact ⟨t,by unfold clock; omega,hfull⟩

noncomputable def machine : BitMachine.Machine :=
  ofFinite (low 6) (low 8) start control program

theorem outputs {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m)
    (w : Fin 4 → List Bool) (hw : w 0=GaussPhysical.encodeTypedMatrix B) :
    machine.OutputsWithin (BitMachineBankCodec.encode w) (outputPacket w m k) (clock w m k) := by
  obtain ⟨t,ht,hrun⟩:=physical_prepare B hm w hw
  apply outputsWithin_of_raw_run (low 6) (low 8) start control program
    (BitMachineBankCodec.encode w) (outputPacket w m k) t (clock w m k) ht
  · simp only [hrun]
  · rw [hrun]
    exact serialized_output w m k

#print axioms parse_run
#print axioms dimension_run
#print axioms serialize_run
#print axioms outputs
end CurrentAdditive.GaussInputDimensions
