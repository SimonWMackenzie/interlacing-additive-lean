import CurrentAdditive.FeatureSeedLayout
import CurrentAdditive.MachineInvokeFull
import CurrentAdditive.GaussRowCount
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

namespace CurrentAdditive.FeatureSeedPrepare
noncomputable section

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128

abbrev Q := CylinderRawInputProjection.qMachine
abbrev A := CylinderRawInputProjection.alphabetMachine
abbrev C := GaussRowCount.machine
abbrev N := 96+Q.stackCount+A.stackCount+C.stackCount
abbrev Bank := MachineInvokeCore.StackN N

def cell (i : Fin 128) : Bank := ⟨i.val,by dsimp only [N]; omega⟩
theorem cell_injective : Function.Injective cell := by
  intro i j h
  exact Fin.ext (congrArg (fun b : Bank => b.val) h)
@[simp] theorem cell_eq (i j : Fin 128) : cell i=cell j ↔ i=j := cell_injective.eq_iff

def qEmbed : Fin Q.stackCount ↪ Bank := ⟨fun i => ⟨128+i.val,by dsimp only [N]; omega⟩,
  by intro i j h; apply Fin.ext; have hv := congrArg (fun b : Bank => b.val) h; dsimp at hv; omega⟩
def aEmbed : Fin A.stackCount ↪ Bank := ⟨fun i => ⟨128+Q.stackCount+i.val,by dsimp only [N]; omega⟩,
  by intro i j h; apply Fin.ext; have hv := congrArg (fun b : Bank => b.val) h; dsimp at hv; omega⟩
def cEmbed : Fin C.stackCount ↪ Bank := ⟨fun i => ⟨128+Q.stackCount+A.stackCount+i.val,by dsimp only [N]; omega⟩,
  by intro i j h; apply Fin.ext; have hv := congrArg (fun b : Bank => b.val) h; dsimp at hv; omega⟩

def slots (M : BitMachine.Machine) (embed : Fin M.stackCount ↪ Bank)
    (hhigh : ∀ i,128 ≤ (embed i).val) (source target : Fin 128)
    (hs : source.val ≤ 97) (ht : target.val ≤ 97) (hne : source ≠ target) :
    MachineInvokeCore.Slots M N where
  machine := embed
  source := cell source
  target := cell target
  scratch := cell 98
  source_target := by simpa using hne
  source_scratch := by intro h; have := cell_injective h; have := congrArg Fin.val this; omega
  target_scratch := by intro h; have := cell_injective h; have := congrArg Fin.val this; omega
  source_machine := by intro i h; have hh:=hhigh i; have := congrArg Fin.val h; change source.val=(embed i).val at this; omega
  target_machine := by intro i h; have hh:=hhigh i; have := congrArg Fin.val h; change target.val=(embed i).val at this; omega
  scratch_machine := by intro i h; have hh:=hhigh i; have := congrArg Fin.val h; change 98=(embed i).val at this; omega

def qSlots := slots Q qEmbed (by intro i; change 128 ≤ 128+i.val; omega) 96 97 (by decide) (by decide) (by decide)
def aSlots := slots A aEmbed (by intro i; change 128 ≤ 128+Q.stackCount+i.val; omega) 96 30 (by decide) (by decide) (by decide)
def cSlots := slots C cEmbed (by intro i; change 128 ≤ 128+Q.stackCount+A.stackCount+i.val; omega) 30 31 (by decide) (by decide) (by decide)

def copySlots : Fin 3 ↪ Bank := ⟨![cell 96,cell 29,cell 98],by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

def rawBank (raw : List Bool) : Bank → List Bool := Function.update (fun _ => []) (cell 96) raw
def afterQ (raw q : List Bool) := Function.update (rawBank raw) (cell 97) q
def afterA (raw q labels : List Bool) := Function.update (afterQ raw q) (cell 30) labels
def afterC (raw q labels count : List Bool) := Function.update (afterA raw q labels) (cell 31) count
def afterCopy (raw q labels count : List Bool) := Function.update (afterC raw q labels count) (cell 29) raw
def seeded (S : Bank → List Bool) := Function.update (Function.update (Function.update
  (Function.update S (cell 8) FeatureSeedLayout.seedPacket) (cell 9) FeatureSeedLayout.seedBody)
    (cell 12) [true]) (cell 13) [true]

theorem update_blank_high (S : Bank → List Bool) (h : ∀ b,128 ≤ b.val → S b=[])
    (i : Fin 128) (word : List Bool) :
    ∀ b,128 ≤ b.val → Function.update S (cell i) word b=[] := by
  intro b hb
  rw [Function.update_of_ne (show b ≠ cell i from by
    intro he; have hv:=congrArg Fin.val he; change b.val=i.val at hv; have hi:=i.isLt; omega)]
  exact h b hb

theorem raw_high (raw : List Bool) : ∀ b,128 ≤ b.val → rawBank raw b=[] :=
  update_blank_high (fun _ => []) (by intro b hb; rfl) 96 raw
theorem q_high (raw q : List Bool) : ∀ b,128 ≤ b.val → afterQ raw q b=[] :=
  update_blank_high _ (raw_high raw) 97 q
theorem a_high (raw q labels : List Bool) : ∀ b,128 ≤ b.val → afterA raw q labels b=[] :=
  update_blank_high _ (q_high raw q) 30 labels

def pushWord {L V : Type} (target : Bank) : List Bool → TM2.Stmt (fun _ : Bank => Bool) L V → TM2.Stmt (fun _ : Bank => Bool) L V
  | [],next => next
  | b::bs,next => .push target (fun _ => b) (pushWord target bs next)

def constantProgram (_ : Unit) : TM2.Stmt (fun _ : Bank => Bool) Unit Unit :=
  pushWord (cell 8) FeatureSeedMachine.seedBytes.reverse
    (pushWord (cell 9) [false,false,true,true]
      (.push (cell 12) (fun _ => true) (.push (cell 13) (fun _ => true) .halt)))

theorem constant_run (S : Bank → List Bool)
    (h8 : S (cell 8)=[]) (h9 : S (cell 9)=[]) (h12 : S (cell 12)=[]) (h13 : S (cell 13)=[]) :
    ((advance constantProgram)^[1]) (⟨some (),(),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=
      ⟨none,(),seeded S⟩ := by
  rw [Function.iterate_one]
  unfold advance
  simp only [TM2.step]
  have hrev : FeatureSeedMachine.seedBytes.reverse = [false,false,true,true,false,true,true] := by decide
  dsimp only [constantProgram]
  rw [hrev]
  dsimp only [pushWord]
  simp [TM2.stepAux,seeded,FeatureSeedLayout.seedPacket_bytes,
    FeatureSeedLayout.seedBody_bytes,FeatureSeedMachine.seedBytes,
    h8,h9,h12,h13,Function.update_idem]

def p01 := BitMachineRawSequence.program (MachineInvokeFull.program qSlots) (MachineInvokeFull.program aSlots)
  (MachineInvokeFull.start aSlots) (MachineInvokeFull.control qSlots) (MachineInvokeFull.control aSlots)
def p012 := BitMachineRawSequence.program p01 (MachineInvokeFull.program cSlots)
  (MachineInvokeFull.start cSlots) (MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots) (MachineInvokeFull.control cSlots)
def p0123 := BitMachineRawSequence.program p012 (ExactParameterBranchInstall.copyProgram copySlots)
  BitMachineCopy.Label.scan ((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots) none
def program := BitMachineRawSequence.program p0123 constantProgram ()
  (((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots),(none:Option Bool)) ()
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label (MachineInvokeFull.LabelFull Q) (MachineInvokeFull.LabelFull A))
      (MachineInvokeFull.LabelFull C)) BitMachineCopy.Label) Unit

def start : Label := BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots))))
def control := ((((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots),(none:Option Bool)),())

def clock (raw labels : List Bool) : Nat :=
  MachineInvokeFull.uniformBound Q raw (10*(raw.length+1))+
  MachineInvokeFull.uniformBound A raw (CylinderRawInputProjection.coefficient*(raw.length+1)^3)+
  MachineInvokeFull.uniformBound C labels (GaussRowCount.polynomialClock labels.length)+2*raw.length+2+5

theorem run {q : Nat} (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    let raw:=CylinderRawInputProjection.input alphabet source
    let ys:=(alphabet.map Prod.fst).toList
    let labels:=SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)
    ∃ t ≤ clock raw labels,((advance program)^[t])
      (⟨some start,control,rawBank raw⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=
      ⟨none,control,seeded (afterCopy raw (List.replicate q true) labels (List.replicate ys.length true))⟩ := by
  let raw:=CylinderRawInputProjection.input alphabet source
  let ys:=(alphabet.map Prod.fst).toList
  let labels:=SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)
  have hl : CylinderProductionProjection.labelWords alphabet=FeatureInnerAlphabetRun64.labelWords ys := by
    simp [CylinderProductionProjection.labelWords,FeatureInnerAlphabetRun64.labelWords,ys,List.map_map]
  have hcount : (FeatureInnerAlphabetRun64.labelWords ys).length=ys.length := by simp [FeatureInnerAlphabetRun64.labelWords]
  obtain ⟨a,ha,hrQ⟩:=MachineInvokeFull.invoke_run_uniform qSlots (rawBank raw) raw (List.replicate q true)
    (10*(raw.length+1)) (by simp [qSlots,slots,rawBank]) (by simp [qSlots,slots,rawBank])
    (by simp [qSlots,slots,rawBank]) (fun i => raw_high raw _ (by change 128 ≤ 128+i.val; omega))
    (CylinderRawInputProjection.q_output alphabet source)
  obtain ⟨b,hb,hrA⟩:=MachineInvokeFull.invoke_run_uniform aSlots (afterQ raw (List.replicate q true)) raw labels
    (CylinderRawInputProjection.coefficient*(raw.length+1)^3)
    (by simp [aSlots,slots,afterQ,rawBank]) (by simp [aSlots,slots,afterQ,rawBank])
    (by simp [aSlots,slots,afterQ,rawBank])
    (fun i => q_high raw _ _ (by change 128 ≤ 128+Q.stackCount+i.val; omega))
    (by simpa [labels,hl] using CylinderRawInputProjection.alphabet_output_polynomial alphabet source)
  obtain ⟨c,hc,hrC⟩:=MachineInvokeFull.invoke_run_uniform cSlots (afterA raw (List.replicate q true) labels) labels
    (List.replicate ys.length true) (GaussRowCount.polynomialClock labels.length)
    (by simp [cSlots,slots,afterA]) (by simp [cSlots,slots,afterA,afterQ,rawBank])
    (by simp [cSlots,slots,afterA,afterQ,rawBank])
    (fun i => a_high raw _ _ _ (by change 128 ≤ 128+Q.stackCount+A.stackCount+i.val; omega))
    (by simpa only [hcount] using GaussRowCount.outputs_polynomial (FeatureInnerAlphabetRun64.labelWords ys))
  obtain ⟨d,hd,hrCopy⟩:=ExactParameterBranchInstall.copy_run copySlots
    (afterC raw (List.replicate q true) labels (List.replicate ys.length true)) raw
    (by simp [copySlots,afterC,afterA,afterQ,rawBank])
    (by simp [copySlots,afterC,afterA,afterQ,rawBank])
    (by simp [copySlots,afterC,afterA,afterQ,rawBank])
  have hrConst:=constant_run (afterCopy raw (List.replicate q true) labels (List.replicate ys.length true))
    (by simp [afterCopy,afterC,afterA,afterQ,rawBank]) (by simp [afterCopy,afterC,afterA,afterQ,rawBank])
    (by simp [afterCopy,afterC,afterA,afterQ,rawBank]) (by simp [afterCopy,afterC,afterA,afterQ,rawBank])
  obtain ⟨ab,hab,hrab⟩:=BitMachineRawSequence.runs (MachineInvokeFull.program qSlots) (MachineInvokeFull.program aSlots)
    (MachineInvokeFull.start qSlots) (MachineInvokeFull.start aSlots)
    (MachineInvokeFull.control qSlots) (MachineInvokeFull.control qSlots)
    (MachineInvokeFull.control aSlots) (MachineInvokeFull.control aSlots)
    (rawBank raw) (afterQ raw (List.replicate q true)) (afterA raw (List.replicate q true) labels) a b hrQ hrA
  obtain ⟨abc,habc,hrabc⟩:=BitMachineRawSequence.runs p01 (MachineInvokeFull.program cSlots)
    (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots)) (MachineInvokeFull.start cSlots)
    (MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots)
    (MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots)
    (MachineInvokeFull.control cSlots) (MachineInvokeFull.control cSlots)
    (rawBank raw) (afterA raw (List.replicate q true) labels)
    (afterC raw (List.replicate q true) labels (List.replicate ys.length true)) ab c hrab hrC
  obtain ⟨abcd,habcd,hrabcd⟩:=BitMachineRawSequence.runs p012 (ExactParameterBranchInstall.copyProgram copySlots)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots))) BitMachineCopy.Label.scan
    ((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots)
    ((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots)
    (none:Option Bool) none (rawBank raw) (afterC raw (List.replicate q true) labels (List.replicate ys.length true))
    (afterCopy raw (List.replicate q true) labels (List.replicate ys.length true)) abc d hrabc hrCopy
  obtain ⟨t,ht,hr⟩:=BitMachineRawSequence.runs p0123 constantProgram
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (MachineInvokeFull.start qSlots)))) ()
    (((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots),(none:Option Bool))
    (((MachineInvokeFull.control qSlots,MachineInvokeFull.control aSlots),MachineInvokeFull.control cSlots),(none:Option Bool))
    () () (rawBank raw) (afterCopy raw (List.replicate q true) labels (List.replicate ys.length true))
    (seeded (afterCopy raw (List.replicate q true) labels (List.replicate ys.length true))) abcd 1 hrabcd hrConst
  refine ⟨t,?_,hr⟩
  change t ≤ clock raw labels
  unfold clock
  omega

#print axioms run

end
end CurrentAdditive.FeatureSeedPrepare
