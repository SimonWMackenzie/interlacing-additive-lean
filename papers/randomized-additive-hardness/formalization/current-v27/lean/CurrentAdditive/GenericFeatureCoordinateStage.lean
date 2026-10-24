import CurrentAdditive.FeaturePacketFinalize96
import CurrentAdditive.FeatureCoordinateStage96
import CurrentAdditive.GenericFeatureOldDescriptorTraversal
import CurrentAdditive.GenericFeatureOldDescriptorSemantics

/-! One complete coordinate stage: actual guarded old-descriptor traversal,
changing unary count, and physical rebuilding of the canonical feature packet.
The exact whole-bank endpoint is retained for the coordinate iteration. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.GenericFeatureCoordinateStage
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.Wide96ContextListScheduler
open CurrentAdditive.GenericFeatureOldDescriptorFrame
open CurrentAdditive.GenericFeatureOldDescriptorSemantics

def data (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) : GenericFeatureOldDescriptorTraversal.Data depth :=
  ⟨j,ys,cs,qfuel,jUnary,carry,SourceListEncoding.fields (words cs),
    List.replicate cs.length true⟩

abbrev frame := FeatureCoordinateStage96.frame
abbrev initialBank := FeatureCoordinateStage96.initialBank

def beforeHeader (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  frame (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next depth j ys cs)))
    (List.replicate (next depth j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry)

def finalBank (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  Function.update (beforeHeader depth j ys cs qfuel jUnary carry) 8
    (SourceListEncoding.encode (words (next depth j ys cs)))

def scanClock (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  let D := data depth j ys cs qfuel jUnary carry
  MovingContextScheduler96.remainingBudget (GenericFeatureGuardedDescriptor.program depth)
    (GenericFeatureGuardedDescriptor.start depth) (GenericFeatureGuardedDescriptor.control depth)
    D.piece D.body D.context D.original (GenericFeatureOldDescriptorTraversal.contract D)
    [] D.original

def loopProgram (depth : Nat) := Wide96ContextListScheduler.program (GenericFeatureGuardedDescriptor.program depth)
  (GenericFeatureGuardedDescriptor.start depth) (GenericFeatureGuardedDescriptor.control depth)
private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l

def loopStart (depth : Nat) := labelFor (loopProgram depth) (.inr (.inr .check))
def loopControl (depth : Nat) := Wide96ContextListScheduler.getterControl (GenericFeatureGuardedDescriptor.control depth)
  (CylinderContextScanStep.copyControl ((),none))

def program (depth : Nat) := BitMachineRawSequence.program (loopProgram depth) FeaturePacketFinalize96.program
  FeaturePacketFinalize96.start (loopControl depth) FeaturePacketFinalize96.control
def start (depth : Nat) := labelFor (program depth) (BitMachineRawSequence.leftLabel (loopStart depth))
def control (depth : Nat) := ((loopControl depth),FeaturePacketFinalize96.control)

def clock (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  scanClock depth j ys cs qfuel jUnary carry+
    FeaturePacketFinalize96.clock (beforeHeader depth j ys cs qfuel jUnary carry)
      (List.replicate (next depth j ys cs).length true)
      (SourceListEncoding.fields (words (next depth j ys cs)))+1

theorem run (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    ∃ t ≤ clock depth j ys cs qfuel jUnary carry,
      ((advance (program depth))^[t])
        (⟨some (start depth),control depth,initialBank j ys cs qfuel jUnary carry⟩ :
          TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control depth,finalBank depth j ys cs qfuel jUnary carry⟩ := by
  classical
  let D := data depth j ys cs qfuel jUnary carry
  obtain ⟨a,ha,v,haRun⟩ := GenericFeatureOldDescriptorTraversal.run D
  have hctx : context depth (List.replicate cs.length true) ys []=
      List.replicate cs.length true := rfl
  simp only [D,data,GenericFeatureOldDescriptorTraversal.Data.original,
    GenericFeatureOldDescriptorTraversal.Data.piece,
    GenericFeatureOldDescriptorTraversal.Data.context,
    GenericFeatureOldDescriptorTraversal.Data.extra,hctx] at haRun
  rw [body_exact,count_next] at haRun
  have haRun' : ((advance (loopProgram depth))^[a])
      ⟨some (loopStart depth),loopControl depth,initialBank j ys cs qfuel jUnary carry⟩ =
      ⟨none,v,beforeHeader depth j ys cs qfuel jUnary carry⟩ := by
    simpa only [loopProgram,loopStart,labelFor,loopControl,initialBank,beforeHeader,
      frame,Wide96ContextListScheduler.run,words,List.length_map] using haRun
  let T := beforeHeader depth j ys cs qfuel jUnary carry
  have hbody : T 9 = SourceListEncoding.fields (words (next depth j ys cs)) := by
    rw [show T=frame _ _ _ _ _ _ by rfl,frame,FeatureCoordinateStage96.frame,
      Wide96ContextPreservingScan.output_preserved]
    simp [foreignBank]
  have hcount : T 12 = List.replicate (next depth j ys cs).length true := by
    have h := Wide96ContextPreservingScan.context_preserved
      (foreignBank (SourceListEncoding.fields (words (next depth j ys cs)))
        (List.replicate (next depth j ys cs).length true) 0 (extra j ys qfuel jUnary carry))
      (CylinderContextScanStep.initial (SourceListEncoding.encode (words cs)) cs.length)
    simpa [T,beforeHeader,frame,foreignBank] using h.1
  have he (k : Fin 96) (hk : 15 ≤ k.val) : T k=extra j ys qfuel jUnary carry k :=
    frame_extra _ _ _ _ _ _ k hk
  have h16 : T 16=[] := by rw [he 16 (by decide)]; simp [extra]
  have h19 : T 19=[] := by rw [he 19 (by decide)]; simp [extra]
  have h20 : T 20=[] := by rw [he 20 (by decide)]; simp [extra]
  have hh (k : Fin 96) (hk : 32 ≤ k.val) : T k=[] := by
    rw [he k (by omega)]
    have h15 : k≠15 := by intro h; subst k; omega
    have h17 : k≠17 := by intro h; subst k; omega
    have h18 : k≠18 := by intro h; subst k; omega
    have h29 : k≠29 := by intro h; subst k; omega
    have h30 : k≠30 := by intro h; subst k; omega
    have h31 : k≠31 := by intro h; subst k; omega
    simp [extra,h15,h17,h18,h29,h30,h31]
  obtain ⟨b,hb,hbRun⟩ := FeaturePacketFinalize96.run T
    (List.replicate (next depth j ys cs).length true)
    (SourceListEncoding.fields (words (next depth j ys cs))) hcount hbody h16 h19 h20 hh
  have hpacket : EncodedCommunication.natField (List.replicate (next depth j ys cs).length true).length++
      SourceListEncoding.fields (words (next depth j ys cs))=
      SourceListEncoding.encode (words (next depth j ys cs)) := by
    simp [SourceListEncoding.encode,words]
  rw [hpacket] at hbRun
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs (loopProgram depth) FeaturePacketFinalize96.program
    (loopStart depth) FeaturePacketFinalize96.start (loopControl depth) v
    FeaturePacketFinalize96.control FeaturePacketFinalize96.control
    (initialBank j ys cs qfuel jUnary carry) T
    (finalBank depth j ys cs qfuel jUnary carry) a b haRun' hbRun
  refine ⟨t,?_,by simpa only [program,start,labelFor,control] using hr⟩
  change a ≤ scanClock depth j ys cs qfuel jUnary carry at ha
  change t ≤ scanClock depth j ys cs qfuel jUnary carry+
    FeaturePacketFinalize96.clock T (List.replicate (next depth j ys cs).length true)
      (SourceListEncoding.fields (words (next depth j ys cs)))+1
  omega

#print axioms run
end CurrentAdditive.GenericFeatureCoordinateStage
