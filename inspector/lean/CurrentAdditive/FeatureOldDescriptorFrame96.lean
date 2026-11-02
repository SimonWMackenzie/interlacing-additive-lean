import CurrentAdditive.FeatureGuardedDescriptor96
import CurrentAdditive.MovingContextScheduler96
import CurrentAdditive.CylinderSchedulerPost96

/-! The concrete outer descriptor frame, including retained coordinate-loop
and original-input banks. Only actual encoded descriptors are selected. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace CurrentAdditive.FeatureOldDescriptorFrame96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.Wide96ContextListScheduler

def words (cs : List (List (Nat × Nat))) := cs.map CylinderFeatureCodec.encodeFeature

def eligible (word : List Bool) : Bool :=
  match CylinderFeatureCodec.decodeFeature word with
  | none => false
  | some c => decide (c.length<8192)

def piece (j : Nat) (ys : List Nat) (word : List Bool) : List Bool :=
  match CylinderFeatureCodec.decodeFeature word with
  | none => []
  | some c => if c.length<8192 then FeatureEligibleDescriptor96.extensions j c ys else []

def countStep (ys : List Nat) (count word : List Bool) : List Bool :=
  if eligible word then List.replicate ys.length true++count else count

def context (count : List Bool) (ys : List Nat) (pre : List (List Bool)) : List Bool :=
  pre.foldl (countStep ys) count

theorem context_step (count : List Bool) (ys : List Nat)
    (pre : List (List Bool)) (word : List Bool) :
    context count ys (pre++[word])=countStep ys (context count ys pre) word := by
  simp [context,List.foldl_append]

def extra (j : Nat) (ys : List Nat) (qfuel jUnary carry : List Bool) :
    Fin 96 → List Bool := fun k =>
  if k=15 then j.bits else if k=17 then qfuel else if k=18 then jUnary
  else if k=29 then carry
  else if k=30 then SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)
  else if k=31 then List.replicate ys.length true else []

noncomputable def selected (j : Nat) (ys : List Nat)
    (qfuel jUnary carry : List Bool) (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) (body count : List Bool) :
    Fin 96 → List Bool :=
  (Wide96ContextPreservingScan.frame
    (foreignBank body count suffix.length (extra j ys qfuel jUnary carry))
    (⟨none,CylinderContextScanStep.getterControl
      (PreservingV2Program.v2Control (IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true,false),none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre++word::suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)).stk

theorem selected_extra (j : Nat) (ys : List Nat)
    (qfuel jUnary carry : List Bool) (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) (body count : List Bool)
    (k : Fin 96) (hk : 15≤k.val) :
    selected j ys qfuel jUnary carry pre word suffix body count k=
      extra j ys qfuel jUnary carry k := by
  unfold selected
  rw [Wide96ContextPreservingScan.frame_foreign]
  · exact foreignBank_extra body count suffix.length _ k hk
  · rintro ⟨i,hi⟩
    have hs : (Wide96ContextPreservingScan.locate i).val<15 := by fin_cases i <;> decide
    have hv := congrArg Fin.val hi
    omega

theorem selected_banks (j : Nat) (ys : List Nat)
    (qfuel jUnary carry : List Bool) (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) (body count : List Bool) :
    let S := selected j ys qfuel jUnary carry pre word suffix body count
    S 6=word ∧ S 8=SourceListEncoding.encode (pre++word::suffix) ∧
    S 9=body ∧ S 10=List.replicate pre.length true ∧
    S 12=count ∧ S 13=List.replicate suffix.length true := by
  let F := Wide96ContextPreservingScan.frame
    (foreignBank body count suffix.length (extra j ys qfuel jUnary carry))
    (⟨none,CylinderContextScanStep.getterControl
      (PreservingV2Program.v2Control (IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true,false),none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre++word::suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  have hi (i : Fin 12) := Wide96ContextPreservingScan.frame_bank
    (foreignBank body count suffix.length (extra j ys qfuel jUnary carry))
    (⟨none,CylinderContextScanStep.getterControl
      (PreservingV2Program.v2Control (IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true,false),none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre++word::suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) i
  have h9 := Wide96ContextPreservingScan.output_preserved
    (foreignBank body count suffix.length (extra j ys qfuel jUnary carry))
    (⟨none,CylinderContextScanStep.getterControl
      (PreservingV2Program.v2Control (IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true,false),none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre++word::suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  have hc := Wide96ContextPreservingScan.context_preserved
    (foreignBank body count suffix.length (extra j ys qfuel jUnary carry))
    (⟨none,CylinderContextScanStep.getterControl
      (PreservingV2Program.v2Control (IndexedV2Program.indexControl
        (SourceListMachineFields.coreControl (some true,false),none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre++word::suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simpa [selected,CylinderContextScanStep.selectedBank,Wide96ContextPreservingScan.locate] using hi 6
  · simpa [selected,CylinderContextScanStep.selectedBank,Wide96ContextPreservingScan.locate] using hi 8
  · simpa [selected,foreignBank] using h9
  · simpa [selected,CylinderContextScanStep.selectedBank,Wide96ContextPreservingScan.locate] using hi 10
  · simpa [selected,foreignBank] using hc.1
  · simpa [selected,foreignBank] using hc.2

#print axioms selected_banks
end CurrentAdditive.FeatureOldDescriptorFrame96
