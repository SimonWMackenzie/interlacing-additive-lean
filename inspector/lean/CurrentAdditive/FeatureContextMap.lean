import CurrentAdditive.FeatureMapInitialize
import CurrentAdditive.FeatureMapContract

set_option maxHeartbeats 3000000

/-! A fixed ordinary-input contextual list mapper. The program depends only
on the actual evaluator M and the output format. Context, item list, result
function and its execution proof are data/specification parameters, never
program-control data. Duplicate ordered items are preserved. -/

namespace CurrentAdditive.FeatureContextMap

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureMapPairLoader CurrentAdditive.FeatureMapInvoke
open CurrentAdditive.GaussListContext

noncomputable section
variable (M : BitMachine.Machine) (framed : Bool)

def scheduler := StatefulListScheduler.program (FeatureMapAppend.program M framed)
 .clear5 (FeatureMapAppend.initial M framed)

abbrev SchedulerLabel := StatefulListScheduler.Label (FeatureMapAppend.Label M framed)
abbrev SchedulerControl := StatefulListScheduler.Control (FeatureMapAppend.Control M framed)

def schedulerStart : SchedulerLabel M framed := .inr (.inr .check)
def schedulerInitial : SchedulerControl M framed :=
 StatefulListScheduler.getterControl (FeatureMapAppend.initial M framed)
   (CylinderContextScanStep.copyControl ((),none))

def program := BitMachineRawSequence.program (FeatureMapInitialize.program M framed)
 (scheduler M framed) (schedulerStart M framed)
 (FeatureMapInitialize.initial M framed) (schedulerInitial M framed)

abbrev Label := BitMachineRawSequence.Label (FeatureMapInitialize.Label framed)
 (SchedulerLabel M framed)
abbrev Control := FeatureMapInitialize.Control framed × SchedulerControl M framed

def start : Label M framed := BitMachineRawSequence.leftLabel (FeatureMapInitialize.start framed)
def initial : Control M framed :=
 (FeatureMapInitialize.initial M framed,schedulerInitial M framed)

def machine : BitMachine.Machine :=
 ofFinite (low 15 : Bank M framed) (low 9) (start M framed) (initial M framed)
   (program M framed)

def result (framed : Bool) (xs : List (List Bool)) (f : List Bool → List Bool) : List Bool :=
 if framed then SourceListEncoding.encode (xs.map f) else xs.flatMap f

theorem result_eq (framed : Bool) (xs : List (List Bool)) (f : List Bool → List Bool) :
 result framed xs f = FeatureMapHeaders.output framed xs.length ++
   FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) xs := by
 cases framed
 · rfl
 · change SourceListEncoding.encode (xs.map f) = EncodedCommunication.natField xs.length ++ _
   unfold SourceListEncoding.encode
   rw [List.length_map]
   congr 1
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [List.map_cons,SourceListEncoding.fields,FeatureMapSourceScheduler.joined,
       List.flatMap_cons,FeatureMapContract.piece,FeatureMapInvoke.piece,Bool.true_eq,↓reduceIte]
     exact congrArg (fun t => (EncodedCommunication.natField (f x).length ++ f x) ++ t) ih

def sumClock (context : List Bool) (xs : List (List Bool))
 (f : List Bool → List Bool) (b : List Bool → Nat)
 (hM : ∀ w∈xs,M.OutputsWithin (packet context w) (f w) (b w)) : Nat :=
 FeatureMapInitialize.budget framed context xs +
 FeatureMapSourceScheduler.remainingBudget (FeatureMapAppend.program M framed)
   .clear5 (FeatureMapAppend.initial M framed) (FeatureMapContract.piece framed f)
   (FeatureMapHeaders.output framed xs.length) context xs
   (FeatureMapContract.contract M framed context (FeatureMapHeaders.output framed xs.length)
     f b xs hM) [] xs + 1

theorem outputs (context : List Bool) (xs : List (List Bool))
 (f : List Bool → List Bool) (b : List Bool → Nat)
 (hM : ∀ w∈xs,M.OutputsWithin (packet context w) (f w) (b w)) :
 (machine M framed).OutputsWithin
   (packet context (SourceListEncoding.encode xs)) (result framed xs f)
   (sumClock M framed context xs f b hM) := by
 classical
 let input := packet context (SourceListEncoding.encode xs)
 let S := (rawInit (low 15 : Bank M framed) (start M framed) (initial M framed) input).stk
 have hblank (j : Bank M framed) (hj : j ≠ low 15) : S j = [] := by
   change (if j = (low 15 : Bank M framed) then input else []) = []
   rw [if_neg hj]
 have hcb : ∀ i,S (FeatureMapInitialize.countRegion M framed i)=[] := by
   intro i;apply hblank
   intro h;have hh := congrArg Fin.val h
   change 32+(evaluator M framed).stackCount+i.val=15 at hh;omega
 have hhb : ∀ i,S (FeatureMapInitialize.headerRegion M framed i)=[] := by
   intro i;apply hblank
   intro h;have hh := congrArg Fin.val h
   change 32+(evaluator M framed).stackCount+FeatureMapListCount.machine.stackCount+i.val=15 at hh
   omega
 obtain ⟨a,ha,hr⟩ := FeatureMapInitialize.initialize_run M framed S context xs
   (by simp [S,rawInit,input])
   (hblank _ (by simp [low,Fin.ext_iff])) (hblank _ (by simp [low,Fin.ext_iff]))
   (hblank _ (by simp [low,Fin.ext_iff])) (hblank _ (by simp [low,Fin.ext_iff]))
   (hblank _ (by simp [low,Fin.ext_iff])) (hblank _ (by simp [low,Fin.ext_iff]))
   (hblank _ (by simp [low,Fin.ext_iff])) hcb hhb
 let header := FeatureMapHeaders.output framed xs.length
 have hinitbank : FeatureMapInitialize.resultBank M framed S context xs =
     FeatureMapLayout.boundary (SourceListEncoding.encode xs) header context 0 xs.length := by
   have hs : Function.update S (low 15) [] = fun _ => [] := by
     funext k
     by_cases hk:k=low 15
     · subst k;simp
     · rw [Function.update_of_ne hk]
       exact hblank k hk
   unfold FeatureMapInitialize.resultBank FeatureMapInputParser.output
   rw [hs]
   funext k
   by_cases h8:k=low 8 <;> by_cases h9:k=low 9 <;>
     by_cases h12:k=low 12 <;> by_cases h13:k=low 13 <;> by_cases h10:k=low 10 <;>
     simp [FeatureMapLayout.boundary,StatefulListScheduler.initialBank,FeatureMapLayout.blank,
       Function.update_apply,header,low,Fin.ext_iff,Fin.ofNat] at * <;> simp_all
 rw [hinitbank] at hr
 let C := FeatureMapContract.contract M framed context header f b xs hM
 have hlist := FeatureMapSourceScheduler.run_remaining
   (FeatureMapAppend.program M framed) .clear5 (FeatureMapAppend.initial M framed)
   (FeatureMapContract.piece framed f) header context xs C [] xs (by simp)
   (schedulerInitial M framed)
 have hextra : C.extra = FeatureMapLayout.blank := rfl
 simp only [List.nil_append,List.length_nil,FeatureMapSourceScheduler.joined,
   List.flatMap_nil,List.append_nil,hextra] at hlist
 rw [FeatureMapLayout.frame_initial,FeatureMapLayout.frame_initial] at hlist
 obtain ⟨btime,hb,v,hbrun⟩ := hlist
 obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
   (FeatureMapInitialize.program M framed) (scheduler M framed)
   (FeatureMapInitialize.start framed) (schedulerStart M framed)
   (FeatureMapInitialize.initial M framed) (FeatureMapInitialize.initial M framed)
   (schedulerInitial M framed) v S _ _ a btime hr hbrun
 apply outputsWithin_of_raw_run (low 15 : Bank M framed) (low 9)
   (start M framed) (initial M framed) (program M framed) input
   (result framed xs f) t (sumClock M framed context xs f b hM)
 · dsimp [sumClock]
   dsimp [C,header] at hb
   omega
 · change (((advance (program M framed))^[t])
       (⟨some (start M framed),initial M framed,S⟩ : TM2.Cfg _ _ _)).l=none
   simpa only [program,start,initial] using congrArg (fun c => c.l) he
 · change (((advance (program M framed))^[t])
       (⟨some (start M framed),initial M framed,S⟩ : TM2.Cfg _ _ _)).stk (low 9)=_
   have hout := congrArg (fun c => c.stk (low 9 : Bank M framed)) he
   simp only [FeatureMapLayout.boundary_nine] at hout
   simpa only [program,start,initial,result_eq,header,FeatureMapSourceScheduler.joined] using hout

#print axioms outputs

end
end CurrentAdditive.FeatureContextMap
