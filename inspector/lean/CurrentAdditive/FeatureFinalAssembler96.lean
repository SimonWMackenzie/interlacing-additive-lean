import CurrentAdditive.FeatureFinalStateProjection96
import CurrentAdditive.FeatureSeedSerialize

namespace CurrentAdditive.FeatureFinalAssembler96
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

abbrev Q := FeatureFinalStateProjection96.qMachine
abbrev F := FeatureFinalStateProjection96.featureMachine
abbrev T := FeatureFinalStateProjection96.tupleMachine
abbrev N := 96+Q.stackCount+F.stackCount+T.stackCount
abbrev Bank := MachineInvokeCore.StackN N

def cell (i : Fin 128) : Bank := ⟨i.val,by dsimp only [N]; omega⟩
theorem cell_injective : Function.Injective cell := by
  intro i j h
  exact Fin.ext (congrArg (fun b : Bank => b.val) h)
@[simp] theorem cell_eq (i j : Fin 128) : cell i=cell j ↔ i=j := cell_injective.eq_iff

def qEmbed : Fin Q.stackCount ↪ Bank := ⟨fun i => ⟨128+i.val,by dsimp only [N]; omega⟩,
  by intro i j h; apply Fin.ext; have hv := congrArg (fun b : Bank => b.val) h; dsimp at hv; omega⟩
def fEmbed : Fin F.stackCount ↪ Bank := ⟨fun i => ⟨128+Q.stackCount+i.val,by dsimp only [N]; omega⟩,
  by intro i j h; apply Fin.ext; have hv := congrArg (fun b : Bank => b.val) h; dsimp at hv; omega⟩
def tEmbed : Fin T.stackCount ↪ Bank := ⟨fun i => ⟨128+Q.stackCount+F.stackCount+i.val,by dsimp only [N]; omega⟩,
  by intro i j h; apply Fin.ext; have hv := congrArg (fun b : Bank => b.val) h; dsimp at hv; omega⟩

def slots (M : BitMachine.Machine) (embed : Fin M.stackCount ↪ Bank)
    (hhigh : ∀ i,128 ≤ (embed i).val) (target : Fin 3) : MachineInvokeCore.Slots M N where
  machine := embed
  source := cell 96
  target := cell ⟨target.val,by omega⟩
  scratch := cell 98
  source_target := by intro h; have hv := congrArg (fun b : Bank => b.val) h; change 96=target.val at hv; have ht := target.isLt; omega
  source_scratch := by simp
  target_scratch := by intro h; have hv := congrArg (fun b : Bank => b.val) h; change target.val=98 at hv; have ht := target.isLt; omega
  source_machine := by intro i h; have hh := hhigh i; have hv := congrArg (fun b : Bank => b.val) h; change 96=(embed i).val at hv; omega
  target_machine := by intro i h; have hh := hhigh i; have ht := target.isLt; have hv := congrArg (fun b : Bank => b.val) h; change target.val=(embed i).val at hv; omega
  scratch_machine := by intro i h; have hh := hhigh i; have hv := congrArg (fun b : Bank => b.val) h; change 98=(embed i).val at hv; omega

def qSlots := slots Q qEmbed (by intro i; change 128 ≤ 128+i.val; omega) 0
def fSlots := slots F fEmbed (by intro i; change 128 ≤ 128+Q.stackCount+i.val; omega) 1
def tSlots := slots T tEmbed (by intro i; change 128 ≤ 128+Q.stackCount+F.stackCount+i.val; omega) 2

def rawBank (state : List Bool) : Bank → List Bool := Function.update (fun _ => []) (cell 96) state
def afterQ (state q : List Bool) := Function.update (rawBank state) (cell 0) q
def afterF (state q features : List Bool) := Function.update (afterQ state q) (cell 1) features
def afterT (state q features tuples : List Bool) := Function.update (afterF state q features) (cell 2) tuples

theorem update_blank_high (S : Bank → List Bool) (h : ∀ b,128 ≤ b.val → S b=[])
    (i : Fin 128) (word : List Bool) :
    ∀ b,128 ≤ b.val → Function.update S (cell i) word b=[] := by
  intro b hb
  rw [Function.update_of_ne (show b ≠ cell i from by
    intro he; have hv := congrArg (fun b : Bank => b.val) he
    change b.val=i.val at hv; have hi := i.isLt; omega)]
  exact h b hb
theorem raw_high (state : List Bool) : ∀ b,128 ≤ b.val → rawBank state b=[] :=
  update_blank_high (fun _ => []) (by intro b hb; rfl) 96 state
theorem q_high (state q : List Bool) : ∀ b,128 ≤ b.val → afterQ state q b=[] :=
  update_blank_high _ (raw_high state) 0 q
theorem f_high (state q features : List Bool) : ∀ b,128 ≤ b.val → afterF state q features b=[] :=
  update_blank_high _ (q_high state q) 1 features

def location : (Fin 3 ⊕ Fin 3) ↪ Bank := ⟨Sum.elim
  (![cell 0,cell 1,cell 2]) (![cell 100,cell 101,cell 102]),by
  intro i j h
  cases i <;> cases j <;> rename_i i j <;> fin_cases i <;> fin_cases j <;> simp_all⟩

def packet (q : Nat) (features tuples : List Bool) :=
  BitMachineBankCodec.encode (![List.replicate q true,features,tuples] : Fin 3 → List Bool)

def firstProgram := BitMachineRawSequence.program (MachineInvokeFull.program qSlots)
  (MachineInvokeFull.program fSlots) (MachineInvokeFull.start fSlots)
  (MachineInvokeFull.control qSlots) (MachineInvokeFull.control fSlots)
def secondProgram := BitMachineRawSequence.program firstProgram (MachineInvokeFull.program tSlots)
  (MachineInvokeFull.start tSlots) (MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots)
  (MachineInvokeFull.control tSlots)
def program := BitMachineRawSequence.program secondProgram (FeatureSeedSerialize.serializeProgram location)
  (.emit 0) ((MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots),MachineInvokeFull.control tSlots)
  (none : Option Bool)
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label (MachineInvokeFull.LabelFull Q) (MachineInvokeFull.LabelFull F))
      (MachineInvokeFull.LabelFull T)) (BitMachineBankSerialize.Label 3)
def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots)))
def control := (((MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots),MachineInvokeFull.control tSlots),(none : Option Bool))
def machine : BitMachine.Machine := ofFinite (cell 96) (cell 102) start control program

def qClock (n r : Nat) := 196*(n+1)+2*r+2+10*(r+1)
def fClock (n : Nat) := 196*(n+1)
def tClock (n r : Nat) := 196*(n+1)+2*r+2+CylinderRawInputProjection.coefficient*(r+1)^3
def clock (state raw : List Bool) (q : Nat) (features tuples : List Bool) :=
  MachineInvokeFull.uniformBound Q state (qClock state.length raw.length)+
  MachineInvokeFull.uniformBound F state (fClock state.length)+
  MachineInvokeFull.uniformBound T state (tClock state.length raw.length)+
    (2*(packet q features tuples).length+2)+3
def finalBank (state : List Bool) (q : Nat) (features tuples : List Bool) (sf : Fin 3 → List Bool) :=
  FeatureSeedSerialize.finish location (afterT state (List.replicate q true) features tuples) sf (packet q features tuples)

theorem final_at (state : List Bool) (q : Nat) (features tuples : List Bool) (sf : Fin 3 → List Bool) :
    finalBank state q features tuples sf (cell 102)=packet q features tuples ∧
    finalBank state q features tuples sf (cell 96)=state := by
  constructor
  · exact BitMachineStackEmbedding.bank_at location _ _ (.inr 2)
  · unfold finalBank FeatureSeedSerialize.finish
    rw [BitMachineStackEmbedding.bank_outside]
    · simp [afterT,afterF,afterQ,rawBank]
    · rintro ⟨k,hk⟩
      cases k <;> rename_i k <;> fin_cases k <;>
        have hv := congrArg (fun b : Bank => b.val) hk <;> dsimp [location,cell] at hv <;> omega

/-- Physical final preparation from the actual complete final state. Every
projection reads that state; no projected field is supplied as a premise. -/
theorem actual_run {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    let features := CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst)
    let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
    ∃ t ≤ clock state raw q features tuples, ∃ sf : Fin 3 → List Bool,
      ((advance program)^[t]) (rawInit (cell 96) start control state)=
        ⟨none,control,finalBank state q features tuples sf⟩ := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
  let features := CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst)
  let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
  obtain ⟨a,ha,hra⟩ := MachineInvokeFull.invoke_run_uniform qSlots (rawBank state) state (List.replicate q true)
    (qClock state.length raw.length) (by simp [qSlots,slots,rawBank]) (by simp [qSlots,slots,rawBank])
    (by simp [qSlots,slots,rawBank]) (fun i => raw_high state _ (by change 128 ≤ 128+i.val; omega))
    (FeatureFinalStateProjection96.q_output alphabet source)
  obtain ⟨b,hb,hrb⟩ := MachineInvokeFull.invoke_run_uniform fSlots (afterQ state (List.replicate q true)) state features
    (fClock state.length) (by simp [fSlots,slots,afterQ,rawBank]) (by simp [fSlots,slots,afterQ,rawBank])
    (by simp [fSlots,slots,afterQ,rawBank])
    (fun i => q_high state _ _ (by change 128 ≤ 128+Q.stackCount+i.val; omega))
    (FeatureFinalStateProjection96.features_output q (alphabet.map Prod.fst) raw)
  obtain ⟨c,hc,hrc⟩ := MachineInvokeFull.invoke_run_uniform tSlots
    (afterF state (List.replicate q true) features) state tuples (tClock state.length raw.length)
    (by simp [tSlots,slots,afterF,afterQ,rawBank]) (by simp [tSlots,slots,afterF,afterQ,rawBank])
    (by simp [tSlots,slots,afterF,afterQ,rawBank])
    (fun i => f_high state _ _ _ (by change 128 ≤ 128+Q.stackCount+F.stackCount+i.val; omega))
    (FeatureFinalStateProjection96.tuples_output alphabet source)
  have hw : (fun i => afterT state (List.replicate q true) features tuples (location (.inl i))) =
      (![List.replicate q true,features,tuples] : Fin 3 → List Bool) := by
    funext i
    fin_cases i <;> simp [afterT,afterF,afterQ,rawBank,location]
  obtain ⟨d,hd,sf,hrd⟩ := FeatureSeedSerialize.serialize location
    (afterT state (List.replicate q true) features tuples)
    (by intro i; fin_cases i <;> simp [afterT,afterF,afterQ,rawBank,location])
  rw [hw] at hrd hd
  obtain ⟨ab,hab,hrab⟩ := BitMachineRawSequence.runs (MachineInvokeFull.program qSlots) (MachineInvokeFull.program fSlots)
    (MachineInvokeFull.start qSlots) (MachineInvokeFull.start fSlots)
    (MachineInvokeFull.control qSlots) (MachineInvokeFull.control qSlots)
    (MachineInvokeFull.control fSlots) (MachineInvokeFull.control fSlots)
    (rawBank state) (afterQ state (List.replicate q true)) (afterF state (List.replicate q true) features) a b hra hrb
  obtain ⟨abc,habc,hrabc⟩ := BitMachineRawSequence.runs firstProgram (MachineInvokeFull.program tSlots)
    (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots)) (MachineInvokeFull.start tSlots)
    (MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots)
    (MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots)
    (MachineInvokeFull.control tSlots) (MachineInvokeFull.control tSlots)
    (rawBank state) (afterF state (List.replicate q true) features)
    (afterT state (List.replicate q true) features tuples) ab c hrab hrc
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs secondProgram (FeatureSeedSerialize.serializeProgram location)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots))) (.emit 0)
    ((MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots),MachineInvokeFull.control tSlots)
    ((MachineInvokeFull.control qSlots,MachineInvokeFull.control fSlots),MachineInvokeFull.control tSlots)
    (none : Option Bool) none (rawBank state) (afterT state (List.replicate q true) features tuples)
    (finalBank state q features tuples sf) abc d hrabc hrd
  refine ⟨t,?_,sf,?_⟩
  · change t ≤ clock state raw q features tuples
    change d ≤ 2*(packet q features tuples).length+2 at hd
    unfold clock
    omega
  · have hbank : rawBank state=(fun k => if k=cell 96 then state else []) := by
      funext k; simp [rawBank,Function.update_apply]
    simpa only [program,start,control,rawInit,hbank] using hr

theorem outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    let features := CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst)
    let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
    machine.OutputsWithin state (packet q features tuples) (clock state raw q features tuples) := by
  obtain ⟨t,ht,sf,hr⟩ := actual_run alphabet source
  apply outputsWithin_of_raw_run (cell 96) (cell 102) start control program _ _ t _ ht
  · rw [hr]
  · rw [hr]
    exact (final_at _ _ _ _ _).1

#print axioms actual_run
#print axioms outputs
end
end CurrentAdditive.FeatureFinalAssembler96
