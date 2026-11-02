import CurrentAdditive.FeaturePacketFinalize96

/-! One complete coordinate stage: actual guarded old-descriptor traversal,
changing unary count, and physical rebuilding of the canonical feature packet.
The exact whole-bank endpoint is retained for the coordinate iteration. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.FeatureCoordinateStage96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.Wide96ContextListScheduler
open CurrentAdditive.FeatureOldDescriptorFrame96
open CurrentAdditive.FeatureOldDescriptorSemantics96

def data (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) : FeatureOldDescriptorTraversal96.Data :=
  ⟨j,ys,cs,qfuel,jUnary,carry,SourceListEncoding.fields (words cs),
    List.replicate cs.length true⟩

def frame (source body count : List Bool) (index fuel : Nat)
    (extra : Fin 96 → List Bool) : Fin 96 → List Bool :=
  (Wide96ContextPreservingScan.frame (foreignBank body count fuel extra)
    (CylinderContextScanStep.initial source index)).stk

def initialBank (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  frame (SourceListEncoding.encode (words cs)) (SourceListEncoding.fields (words cs))
    (List.replicate cs.length true) 0 cs.length (extra j ys qfuel jUnary carry)

def beforeHeader (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  frame (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next j ys cs)))
    (List.replicate (next j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry)

def finalBank (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  Function.update (beforeHeader j ys cs qfuel jUnary carry) 8
    (SourceListEncoding.encode (words (next j ys cs)))

def scanClock (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  let D := data j ys cs qfuel jUnary carry
  MovingContextScheduler96.remainingBudget FeatureGuardedDescriptor96.program
    FeatureGuardedDescriptor96.start FeatureGuardedDescriptor96.control
    D.piece D.body D.context D.original (FeatureOldDescriptorTraversal96.contract D)
    [] D.original

def loopProgram := Wide96ContextListScheduler.program FeatureGuardedDescriptor96.program
  FeatureGuardedDescriptor96.start FeatureGuardedDescriptor96.control
private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l

def loopStart := labelFor loopProgram (.inr (.inr .check))
def loopControl := Wide96ContextListScheduler.getterControl FeatureGuardedDescriptor96.control
  (CylinderContextScanStep.copyControl ((),none))

def program := BitMachineRawSequence.program loopProgram FeaturePacketFinalize96.program
  FeaturePacketFinalize96.start loopControl FeaturePacketFinalize96.control
def start := labelFor program (BitMachineRawSequence.leftLabel loopStart)
def control := (loopControl,FeaturePacketFinalize96.control)

def clock (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  scanClock j ys cs qfuel jUnary carry+
    FeaturePacketFinalize96.clock (beforeHeader j ys cs qfuel jUnary carry)
      (List.replicate (next j ys cs).length true)
      (SourceListEncoding.fields (words (next j ys cs)))+1

theorem run (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    ∃ t ≤ clock j ys cs qfuel jUnary carry,
      ((advance program)^[t])
        (⟨some start,control,initialBank j ys cs qfuel jUnary carry⟩ :
          TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,finalBank j ys cs qfuel jUnary carry⟩ := by
  classical
  let D := data j ys cs qfuel jUnary carry
  obtain ⟨a,ha,v,haRun⟩ := FeatureOldDescriptorTraversal96.run D
  have hctx : context (List.replicate cs.length true) ys []=
      List.replicate cs.length true := rfl
  simp only [D,data,FeatureOldDescriptorTraversal96.Data.original,
    FeatureOldDescriptorTraversal96.Data.piece,
    FeatureOldDescriptorTraversal96.Data.context,
    FeatureOldDescriptorTraversal96.Data.extra,hctx] at haRun
  rw [body_exact,count_next] at haRun
  have haRun' : ((advance loopProgram)^[a])
      ⟨some loopStart,loopControl,initialBank j ys cs qfuel jUnary carry⟩ =
      ⟨none,v,beforeHeader j ys cs qfuel jUnary carry⟩ := by
    simpa only [loopProgram,loopStart,labelFor,loopControl,initialBank,beforeHeader,
      frame,Wide96ContextListScheduler.run,words,List.length_map] using haRun
  let T := beforeHeader j ys cs qfuel jUnary carry
  have hbody : T 9 = SourceListEncoding.fields (words (next j ys cs)) := by
    rw [show T=frame _ _ _ _ _ _ by rfl,frame,Wide96ContextPreservingScan.output_preserved]
    simp [foreignBank]
  have hcount : T 12 = List.replicate (next j ys cs).length true := by
    have h := Wide96ContextPreservingScan.context_preserved
      (foreignBank (SourceListEncoding.fields (words (next j ys cs)))
        (List.replicate (next j ys cs).length true) 0 (extra j ys qfuel jUnary carry))
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
    (List.replicate (next j ys cs).length true)
    (SourceListEncoding.fields (words (next j ys cs))) hcount hbody h16 h19 h20 hh
  have hpacket : EncodedCommunication.natField (List.replicate (next j ys cs).length true).length++
      SourceListEncoding.fields (words (next j ys cs))=
      SourceListEncoding.encode (words (next j ys cs)) := by
    simp [SourceListEncoding.encode,words]
  rw [hpacket] at hbRun
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs loopProgram FeaturePacketFinalize96.program
    loopStart FeaturePacketFinalize96.start loopControl v
    FeaturePacketFinalize96.control FeaturePacketFinalize96.control
    (initialBank j ys cs qfuel jUnary carry) T
    (finalBank j ys cs qfuel jUnary carry) a b haRun' hbRun
  refine ⟨t,?_,by simpa only [program,start,labelFor,control] using hr⟩
  change a ≤ scanClock j ys cs qfuel jUnary carry at ha
  change t ≤ scanClock j ys cs qfuel jUnary carry+
    FeaturePacketFinalize96.clock T (List.replicate (next j ys cs).length true)
      (SourceListEncoding.fields (words (next j ys cs)))+1
  omega

#print axioms run
end CurrentAdditive.FeatureCoordinateStage96
