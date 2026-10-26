import CurrentAdditive.FeatureMapInputParser
import CurrentAdditive.FeatureMapInvoke

/-! Ordinary Bank2 input loading, physical V2 count decoding, and optional
output count-header preparation on one fixed finite ambient bank. -/

namespace CurrentAdditive.FeatureMapInitialize

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureMapPairLoader CurrentAdditive.FeatureMapInvoke
open CurrentAdditive.MinimumRatioContext

noncomputable section
variable (M : BitMachine.Machine) (framed : Bool)

def countRegion : Fin FeatureMapListCount.machine.stackCount ↪ Bank M framed where
 toFun i := ⟨32 + (evaluator M framed).stackCount + i.val, by
   have := i.isLt;change _ < 32 + count M framed;dsimp [count];omega⟩
 inj' := by intro a b h;apply Fin.ext;have hh := congrArg Fin.val h;dsimp only at hh;omega

def headerRegion : Fin (FeatureMapHeaders.machine framed).stackCount ↪ Bank M framed where
 toFun i := ⟨32 + (evaluator M framed).stackCount +
   FeatureMapListCount.machine.stackCount + i.val,by
   have := i.isLt;change _ < 32 + count M framed;dsimp [count];omega⟩
 inj' := by intro a b h;apply Fin.ext;have hh := congrArg Fin.val h;dsimp only at hh;omega

def countSlots : MachineInvokeCore.Slots FeatureMapListCount.machine (count M framed) where
 machine := countRegion M framed
 source := low 8
 target := low 13
 scratch := low 14
 source_target := by simp [low,Fin.ext_iff]
 source_scratch := by simp [low,Fin.ext_iff]
 target_scratch := by simp [low,Fin.ext_iff]
 source_machine := by intro i h;have hh := congrArg Fin.val h;change 8=32+_+i.val at hh;omega
 target_machine := by intro i h;have hh := congrArg Fin.val h;change 13=32+_+i.val at hh;omega
 scratch_machine := by intro i h;have hh := congrArg Fin.val h;change 14=32+_+i.val at hh;omega

def headerSlots : MachineInvokeCore.Slots (FeatureMapHeaders.machine framed) (count M framed) where
 machine := headerRegion M framed
 source := low 13
 target := low 9
 scratch := low 14
 source_target := by simp [low,Fin.ext_iff]
 source_scratch := by simp [low,Fin.ext_iff]
 target_scratch := by simp [low,Fin.ext_iff]
 source_machine := by intro i h;have hh := congrArg Fin.val h;change 13=32+_+_+i.val at hh;omega
 target_machine := by intro i h;have hh := congrArg Fin.val h;change 9=32+_+_+i.val at hh;omega
 scratch_machine := by intro i h;have hh := congrArg Fin.val h;change 14=32+_+_+i.val at hh;omega

def countProgram := MachineInvokeFull.program (countSlots M framed)
def headerProgram := MachineInvokeFull.program (headerSlots M framed)

def firstProgram := BitMachineRawSequence.program
 (FeatureMapInputParser.program (N := count M framed)) (countProgram M framed)
 (MachineInvokeFull.start (countSlots M framed)) none
 (MachineInvokeFull.control (countSlots M framed))

def program := BitMachineRawSequence.program
 (firstProgram M framed) (headerProgram M framed)
 (MachineInvokeFull.start (headerSlots M framed))
 (none,MachineInvokeFull.control (countSlots M framed))
 (MachineInvokeFull.control (headerSlots M framed))

abbrev Label := BitMachineRawSequence.Label
 (BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2)
   (MachineInvokeFull.LabelFull FeatureMapListCount.machine))
 (MachineInvokeFull.LabelFull (FeatureMapHeaders.machine framed))
abbrev Control := (Option Bool × MachineInvokeFull.ControlFull FeatureMapListCount.machine) ×
 MachineInvokeFull.ControlFull (FeatureMapHeaders.machine framed)

def start : Label framed :=
 BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.scan 0))
def initial : Control framed :=
 ((none,MachineInvokeFull.control (countSlots M framed)),
   MachineInvokeFull.control (headerSlots M framed))

def resultBank (S : Bank M framed → List Bool) (context : List Bool)
 (items : List (List Bool)) : Bank M framed → List Bool :=
 Function.update (Function.update
   (FeatureMapInputParser.output S context (SourceListEncoding.encode items))
   (low 13) (List.replicate items.length true)) (low 9)
   (FeatureMapHeaders.output framed items.length)

def budget (context : List Bool) (items : List (List Bool)) : Nat :=
 5 * ((packet context (SourceListEncoding.encode items)).length+1) +
 MachineInvokeFull.uniformBound FeatureMapListCount.machine (SourceListEncoding.encode items)
   (FeatureMapListCount.bound items.length (SourceListEncoding.encode items)) + 1 +
 MachineInvokeFull.uniformBound (FeatureMapHeaders.machine framed)
   (List.replicate items.length true) (FeatureMapHeaders.bound framed items.length) + 1

theorem initialize_run (S : Bank M framed → List Bool)
 (context : List Bool) (items : List (List Bool))
 (h15 : S (low 15) = packet context (SourceListEncoding.encode items))
 (h12 : S (low 12) = []) (h8 : S (low 8) = [])
 (h16 : S (low 16) = []) (h17 : S (low 17) = [])
 (h13 : S (low 13) = []) (h9 : S (low 9) = []) (h14 : S (low 14) = [])
 (hcb : ∀ i,S (countRegion M framed i)=[])
 (hhb : ∀ i,S (headerRegion M framed i)=[]) :
 ∃ t ≤ budget framed context items,
 ((advance (program M framed))^[t])
   (⟨some (start framed),initial M framed,S⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none,initial M framed,resultBank M framed S context items⟩ := by
 let source := SourceListEncoding.encode items
 let P := FeatureMapInputParser.output S context source
 obtain ⟨a,ha,hr⟩ := FeatureMapInputParser.parse_run S context source h15 h12 h8 h16 h17
 have hp13 : P (low 13) = [] := by simpa [P,FeatureMapInputParser.output,low,Fin.ext_iff] using h13
 have hp14 : P (low 14) = [] := by simpa [P,FeatureMapInputParser.output,low,Fin.ext_iff] using h14
 have hpcb : ∀ i,P (countRegion M framed i)=[] := by
   intro i
   have hn (j : Fin 32) : countRegion M framed i ≠ low j := by
     intro h;have hh := congrArg Fin.val h
     change 32+(evaluator M framed).stackCount+i.val=j.val at hh
     have := j.isLt;omega
   simp [P,FeatureMapInputParser.output,Function.update_of_ne,hn,hcb]
 have hc := FeatureMapListCount.outputs items.length (SourceListEncoding.fields items)
 change FeatureMapListCount.machine.OutputsWithin source (List.replicate items.length true)
   (FeatureMapListCount.bound items.length source) at hc
 obtain ⟨b,hb,hs⟩ := MachineInvokeFull.invoke_run_uniform (countSlots M framed) P
   source (List.replicate items.length true) (FeatureMapListCount.bound items.length source)
   (by simp [countSlots,P,FeatureMapInputParser.output]) hp13 hp14 hpcb hc
 let Q := Function.update P (low 13) (List.replicate items.length true)
 have hq9 : Q (low 9)=[] := by simpa [Q,P,FeatureMapInputParser.output,low,Fin.ext_iff] using h9
 have hq14 : Q (low 14)=[] := by simpa [Q,P,FeatureMapInputParser.output,low,Fin.ext_iff] using h14
 have hqhb : ∀ i,Q (headerRegion M framed i)=[] := by
   intro i
   have hn (j : Fin 32) : headerRegion M framed i ≠ low j := by
     intro h;have hh := congrArg Fin.val h
     change 32+(evaluator M framed).stackCount+FeatureMapListCount.machine.stackCount+i.val=j.val at hh
     have := j.isLt;omega
   simp [Q,P,FeatureMapInputParser.output,Function.update_of_ne,hn,hhb]
 obtain ⟨c,hc,hu⟩ := MachineInvokeFull.invoke_run_uniform (headerSlots M framed) Q
   (List.replicate items.length true) (FeatureMapHeaders.output framed items.length)
   (FeatureMapHeaders.bound framed items.length)
   (by simp [headerSlots,Q]) hq9 hq14 hqhb (FeatureMapHeaders.outputs framed items.length)
 obtain ⟨ab,hab,heab⟩ := BitMachineRawSequence.runs
   (FeatureMapInputParser.program (N := count M framed)) (countProgram M framed)
   (.scan 0) (MachineInvokeFull.start (countSlots M framed))
   none (some true) (MachineInvokeFull.control (countSlots M framed))
   (MachineInvokeFull.control (countSlots M framed)) S P Q a b hr hs
 obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
   (firstProgram M framed) (headerProgram M framed)
   (BitMachineRawSequence.leftLabel (.scan 0))
   (MachineInvokeFull.start (headerSlots M framed))
   (none,MachineInvokeFull.control (countSlots M framed))
   (none,MachineInvokeFull.control (countSlots M framed))
   (MachineInvokeFull.control (headerSlots M framed))
   (MachineInvokeFull.control (headerSlots M framed)) S Q _ ab c heab hu
 exact ⟨t,by dsimp [budget];dsimp only [source] at ha hb;omega,he⟩

#print axioms initialize_run

end
end CurrentAdditive.FeatureMapInitialize
