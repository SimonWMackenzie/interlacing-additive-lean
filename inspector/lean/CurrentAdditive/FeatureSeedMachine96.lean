import CurrentAdditive.FeatureSeedSerialize

namespace CurrentAdditive.FeatureSeedMachine96
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open FeatureSeedPrepare FeatureSeedSerialize
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

private abbrev ProgramControl {K L V : Type} (_ : L → TM2.Stmt (fun _ : K => Bool) L V) := V
abbrev PrepControl := ProgramControl FeatureSeedPrepare.program
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label FeatureSeedPrepare.Label (BitMachineBankSerialize.Label 96))
    (BitMachineBankSerialize.Label 2)

def firstProgram := BitMachineRawSequence.program FeatureSeedPrepare.program
  (serializeProgram loc96) (.emit 0) FeatureSeedPrepare.control (none : Option Bool)
def program := BitMachineRawSequence.program firstProgram (serializeProgram loc2)
  (.emit 0) (FeatureSeedPrepare.control,(none : Option Bool)) (none : Option Bool)
def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel FeatureSeedPrepare.start)
def control := ((FeatureSeedPrepare.control,(none : Option Bool)),(none : Option Bool))
def machine : BitMachine.Machine := ofFinite (cell 96) (cell 105) start control program

def clock (raw : List Bool) (q : Nat) (ys : List Nat) :=
  FeatureSeedPrepare.clock raw (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys))+
    (2*(BitMachineBankCodec.encode (FeatureSeedLayout.bank raw ys)).length+2)+
      (2*(FeatureSeedLayout.output raw q ys).length+2)+2

def finalBank (raw : List Bool) (q : Nat) (ys : List Nat)
    (sf96 : Fin 96 → List Bool) (sf2 : Fin 2 → List Bool) :=
  finish loc2 (bank96 raw q ys sf96) sf2 (FeatureSeedLayout.output raw q ys)

theorem final_at (raw : List Bool) (q : Nat) (ys : List Nat)
    (sf96 : Fin 96 → List Bool) (sf2 : Fin 2 → List Bool) :
    finalBank raw q ys sf96 sf2 (cell 105)=FeatureSeedLayout.output raw q ys ∧
    finalBank raw q ys sf96 sf2 (cell 96)=raw := by
  constructor
  · exact BitMachineStackEmbedding.bank_at loc2 _ _ (.inr 2)
  · unfold finalBank finish
    rw [BitMachineStackEmbedding.bank_outside]
    · exact (bank96_at raw q ys sf96).2.2.1
    · rintro ⟨k,hk⟩
      cases k <;> rename_i k <;> fin_cases k <;>
        have hv := congrArg (fun b : Bank => b.val) hk <;> dsimp [loc2,cell] at hv <;> omega

/-- The complete final bank is determined by actual finite programs. The raw
input survives in cell 96, and the output is the exact nested q-loop packet. -/
theorem actual_run {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let ys := (alphabet.map Prod.fst).toList
    ∃ t ≤ clock raw q ys, ∃ (sf96 : Fin 96 → List Bool) (sf2 : Fin 2 → List Bool),
      ((advance program)^[t]) (rawInit (cell 96) start control raw)=
        ⟨none,control,finalBank raw q ys sf96 sf2⟩ := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  let inner := BitMachineBankCodec.encode (FeatureSeedLayout.bank raw ys)
  obtain ⟨a,ha,hra⟩ := FeatureSeedPrepare.run alphabet source
  obtain ⟨b,hb,sf96,hrb⟩ := serialize loc96 (prepared raw q ys) (prepared_aux raw q ys)
  rw [prepared_low] at hrb hb
  have hwords : (fun i => bank96 raw q ys sf96 (loc2 (.inl i))) =
      (![inner,List.replicate q true] : Fin 2 → List Bool) := by
    funext i
    have h := bank96_at raw q ys sf96
    fin_cases i <;> first | exact h.1 | exact h.2.1
  have haux : ∀ i,bank96 raw q ys sf96 (loc2 (.inr i))=[] := by
    intro i
    have h := bank96_at raw q ys sf96
    fin_cases i <;> first | exact h.2.2.2.1 | exact h.2.2.2.2.1 | exact h.2.2.2.2.2
  obtain ⟨c,hc,sf2,hrc⟩ := serialize loc2 (bank96 raw q ys sf96) haux
  rw [hwords] at hrc hc
  obtain ⟨ab,hab,hrab⟩ := BitMachineRawSequence.runs FeatureSeedPrepare.program (serializeProgram loc96)
    FeatureSeedPrepare.start (.emit 0) FeatureSeedPrepare.control FeatureSeedPrepare.control
    (none : Option Bool) none (rawBank raw) (prepared raw q ys) (bank96 raw q ys sf96)
    a b hra hrb
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs firstProgram (serializeProgram loc2)
    (BitMachineRawSequence.leftLabel FeatureSeedPrepare.start) (.emit 0)
    (FeatureSeedPrepare.control,(none : Option Bool)) (FeatureSeedPrepare.control,(none : Option Bool))
    (none : Option Bool) none (rawBank raw) (bank96 raw q ys sf96)
    (finalBank raw q ys sf96 sf2) ab c hrab hrc
  refine ⟨t,?_,sf96,sf2,?_⟩
  swap
  · have hbank : rawBank raw = (fun k => if k=cell 96 then raw else []) := by
      funext k
      simp [rawBank,Function.update_apply]
    simpa only [program,start,control,rawInit,hbank] using hr
  change t ≤ clock raw q ys
  change a ≤ FeatureSeedPrepare.clock raw (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)) at ha
  change b ≤ 2*inner.length+2 at hb
  change c ≤ 2*(FeatureSeedLayout.output raw q ys).length+2 at hc
  unfold clock
  dsimp only [inner] at hb
  omega

theorem outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let ys := (alphabet.map Prod.fst).toList
    machine.OutputsWithin raw (FeatureSeedLayout.output raw q ys) (clock raw q ys) := by
  obtain ⟨t,ht,sf96,sf2,hr⟩ := actual_run alphabet source
  apply outputsWithin_of_raw_run (cell 96) (cell 105) start control program _ _ t _ ht
  · rw [hr]
  · rw [hr]
    exact (final_at _ _ _ _ _).1

#print axioms actual_run
#print axioms outputs
end
end CurrentAdditive.FeatureSeedMachine96
