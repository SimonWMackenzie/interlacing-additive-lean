import CurrentAdditive.FeatureCoordinateBank96
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-! One fixed physical coordinate transition, including actual packed-state
parsing and serialization. Its output is the input state of the next step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.FeatureCoordinateTransition96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureOldDescriptorFrame96
open CurrentAdditive.FeatureOldDescriptorSemantics96

def program := BitMachineRawSequence.program FeatureCoordinateStage96.program
  FeatureBankAdvance96.program FeatureBankAdvance96.start
  FeatureCoordinateStage96.control FeatureBankAdvance96.control
private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l
def start := labelFor program (BitMachineRawSequence.leftLabel FeatureCoordinateStage96.start)
def control := (FeatureCoordinateStage96.control,FeatureBankAdvance96.control)

def clock (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  FeatureCoordinateStage96.clock j ys cs qfuel jUnary carry+
    FeatureBankAdvance96.clock (FeatureCoordinateStage96.finalBank j ys cs qfuel jUnary carry)
      (List.replicate (next j ys cs).length true) j+1

theorem run (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    ∃ t ≤ clock j ys cs qfuel jUnary carry,
      ((advance program)^[t])
        (⟨some start,control,FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry⟩ :
          TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,FeatureCoordinateStage96.initialBank (j+1) ys (next j ys cs)
        qfuel jUnary carry⟩ := by
  obtain ⟨a,ha,har⟩ := FeatureCoordinateStage96.run j ys cs qfuel jUnary carry
  obtain ⟨h12,h13,h15,h19⟩ := FeatureCoordinateBank96.final_banks j ys cs qfuel jUnary carry
  obtain ⟨b,hb,hbr⟩ := FeatureBankAdvance96.run
    (FeatureCoordinateStage96.finalBank j ys cs qfuel jUnary carry)
    (List.replicate (next j ys cs).length true) j h12 h13 h15 h19
  rw [FeatureCoordinateBank96.advance_exact] at hbr
  obtain ⟨t,ht,htr⟩ := BitMachineRawSequence.runs FeatureCoordinateStage96.program
    FeatureBankAdvance96.program FeatureCoordinateStage96.start FeatureBankAdvance96.start
    FeatureCoordinateStage96.control FeatureCoordinateStage96.control
    FeatureBankAdvance96.control FeatureBankAdvance96.control
    (FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry)
    (FeatureCoordinateStage96.finalBank j ys cs qfuel jUnary carry)
    (FeatureCoordinateStage96.initialBank (j+1) ys (next j ys cs) qfuel jUnary carry) a b har hbr
  exact ⟨t,by dsimp only [clock]; omega,by simpa only [program,start,labelFor,control] using htr⟩

def stateWord (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  BitMachineBankCodec.encode (FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry)

def packetClock (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  193*((stateWord j ys cs qfuel jUnary carry).length+1)+
    clock j ys cs qfuel jUnary carry+
    2*(stateWord (j+1) ys (next j ys cs) qfuel jUnary carry).length+4

def machine : BitMachine.Machine := BitMachineBankWrapper.machine program start control

theorem outputs (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    machine.OutputsWithin (stateWord j ys cs qfuel jUnary carry)
      (stateWord (j+1) ys (next j ys cs) qfuel jUnary carry)
      (packetClock j ys cs qfuel jUnary carry) := by
  let A := FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry
  let B := FeatureCoordinateStage96.initialBank (j+1) ys (next j ys cs) qfuel jUnary carry
  let F : (Fin 96 → List Bool) → (Fin 96 → List Bool) := fun _ => B
  have h := BitMachineBankWrapper.outputs program start control F
    (BitMachineBankCodec.encode A) (clock j ys cs qfuel jUnary carry)
    (BitMachineBankCodec.encode B).length (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      have hs : A=S := Option.some.inj hd
      subst S
      obtain ⟨t,ht,hr⟩ := run j ys cs qfuel jUnary carry
      exact ⟨t,⟨none,control,B⟩,ht,hr,rfl,rfl⟩) (by
      intro S hd
      exact le_rfl)
  simpa only [machine,BitMachineBankWrapper.result,BitMachineBankCodec.decode_encode,
    F,packetClock,stateWord,A,B] using h

#print axioms run
#print axioms outputs
end CurrentAdditive.FeatureCoordinateTransition96
