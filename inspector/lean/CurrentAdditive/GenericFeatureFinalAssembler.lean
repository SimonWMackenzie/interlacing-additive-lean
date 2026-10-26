import CurrentAdditive.GenericFeatureFinalStateProjection
import CurrentAdditive.FeatureFinalAssembler96

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GenericFeatureFinalAssembler
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext FeatureFinalAssembler96

abbrev Q := FeatureFinalAssembler96.Q
abbrev F := FeatureFinalAssembler96.F
abbrev T := FeatureFinalAssembler96.T
abbrev packet := FeatureFinalAssembler96.packet
abbrev qClock := FeatureFinalAssembler96.qClock
abbrev fClock := FeatureFinalAssembler96.fClock
abbrev tClock := FeatureFinalAssembler96.tClock

/-- The final bank parsers and serializer are dimension independent. Their
input state contains the actual dimension-D feature packet. -/
def machine (_D : Nat) : BitMachine.Machine := FeatureFinalAssembler96.machine
def clock (_D : Nat) := FeatureFinalAssembler96.clock

theorem actual_run (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
    let features := CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst)
    let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
    ∃ t ≤ clock D state raw q features tuples, ∃ sf : Fin 3 → List Bool,
      ((advance program)^[t]) (rawInit (cell 96) start control state)=
        ⟨none,control,finalBank state q features tuples sf⟩ := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
  let features := CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst)
  let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
  obtain ⟨a,ha,hra⟩ := MachineInvokeFull.invoke_run_uniform qSlots (rawBank state) state (List.replicate q true)
    (qClock state.length raw.length) (by simp [qSlots,slots,rawBank]) (by simp [qSlots,slots,rawBank])
    (by simp [qSlots,slots,rawBank]) (fun i => raw_high state _ (by change 128 ≤ 128+i.val; omega))
    (GenericFeatureFinalStateProjection.q_output D alphabet source)
  obtain ⟨b,hb,hrb⟩ := MachineInvokeFull.invoke_run_uniform fSlots (afterQ state (List.replicate q true)) state features
    (fClock state.length) (by simp [fSlots,slots,afterQ,rawBank]) (by simp [fSlots,slots,afterQ,rawBank])
    (by simp [fSlots,slots,afterQ,rawBank])
    (fun i => q_high state _ _ (by change 128 ≤ 128+Q.stackCount+i.val; omega))
    (GenericFeatureFinalStateProjection.features_output D q (alphabet.map Prod.fst) raw)
  obtain ⟨c,hc,hrc⟩ := MachineInvokeFull.invoke_run_uniform tSlots
    (afterF state (List.replicate q true) features) state tuples (tClock state.length raw.length)
    (by simp [tSlots,slots,afterF,afterQ,rawBank]) (by simp [tSlots,slots,afterF,afterQ,rawBank])
    (by simp [tSlots,slots,afterF,afterQ,rawBank])
    (fun i => f_high state _ _ _ (by change 128 ≤ 128+Q.stackCount+F.stackCount+i.val; omega))
    (GenericFeatureFinalStateProjection.tuples_output D alphabet source)
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
  · change t ≤ clock D state raw q features tuples
    change d ≤ 2*(packet q features tuples).length+2 at hd
    unfold clock FeatureFinalAssembler96.clock
    dsimp only [qClock,fClock,tClock,packet] at ha hb hc hd
    omega
  · have hbank : rawBank state=(fun k => if k=cell 96 then state else []) := by
      funext k; simp [rawBank,Function.update_apply]
    simpa only [FeatureFinalAssembler96.program,FeatureFinalAssembler96.start,
      FeatureFinalAssembler96.control,rawInit,hbank] using hr

theorem outputs (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
    let features := CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst)
    let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
    (machine D).OutputsWithin state (packet q features tuples) (clock D state raw q features tuples) := by
  obtain ⟨t,ht,sf,hr⟩ := actual_run D alphabet source
  apply outputsWithin_of_raw_run (cell 96) (cell 102) start control program _ _ t _ ht
  · rw [hr]
  · rw [hr]
    exact (final_at _ _ _ _ _).1


end CurrentAdditive.GenericFeatureFinalAssembler
