import CurrentAdditive.GenericFeatureCoordinateBank
import CurrentAdditive.FeatureCoordinateTransition96
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-! One fixed physical coordinate transition, including actual packed-state
parsing and serialization. Its output is the input state of the next step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.GenericFeatureCoordinateTransition
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GenericFeatureOldDescriptorFrame
open CurrentAdditive.GenericFeatureOldDescriptorSemantics

def program (depth : Nat) := BitMachineRawSequence.program (GenericFeatureCoordinateStage.program depth)
  FeatureBankAdvance96.program FeatureBankAdvance96.start
  (GenericFeatureCoordinateStage.control depth) FeatureBankAdvance96.control
private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l
def start (depth : Nat) := labelFor (program depth) (BitMachineRawSequence.leftLabel (GenericFeatureCoordinateStage.start depth))
def control (depth : Nat) := ((GenericFeatureCoordinateStage.control depth),FeatureBankAdvance96.control)

def clock (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  GenericFeatureCoordinateStage.clock depth j ys cs qfuel jUnary carry+
    FeatureBankAdvance96.clock (GenericFeatureCoordinateStage.finalBank depth j ys cs qfuel jUnary carry)
      (List.replicate (next depth j ys cs).length true) j+1

theorem run (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    ∃ t ≤ clock depth j ys cs qfuel jUnary carry,
      ((advance (program depth))^[t])
        (⟨some (start depth),control depth,GenericFeatureCoordinateStage.initialBank j ys cs qfuel jUnary carry⟩ :
          TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control depth,GenericFeatureCoordinateStage.initialBank (j+1) ys (next depth j ys cs)
        qfuel jUnary carry⟩ := by
  obtain ⟨a,ha,har⟩ := GenericFeatureCoordinateStage.run depth j ys cs qfuel jUnary carry
  obtain ⟨h12,h13,h15,h19⟩ := (GenericFeatureCoordinateBank.final_banks depth) j ys cs qfuel jUnary carry
  obtain ⟨b,hb,hbr⟩ := FeatureBankAdvance96.run
    (GenericFeatureCoordinateStage.finalBank depth j ys cs qfuel jUnary carry)
    (List.replicate (next depth j ys cs).length true) j h12 h13 h15 h19
  rw [(GenericFeatureCoordinateBank.advance_exact depth)] at hbr
  obtain ⟨t,ht,htr⟩ := BitMachineRawSequence.runs (GenericFeatureCoordinateStage.program depth)
    FeatureBankAdvance96.program (GenericFeatureCoordinateStage.start depth) FeatureBankAdvance96.start
    (GenericFeatureCoordinateStage.control depth) (GenericFeatureCoordinateStage.control depth)
    FeatureBankAdvance96.control FeatureBankAdvance96.control
    (GenericFeatureCoordinateStage.initialBank j ys cs qfuel jUnary carry)
    (GenericFeatureCoordinateStage.finalBank depth j ys cs qfuel jUnary carry)
    (GenericFeatureCoordinateStage.initialBank (j+1) ys (next depth j ys cs) qfuel jUnary carry) a b har hbr
  exact ⟨t,by dsimp only [clock]; omega,by simpa only [program,start,labelFor,control] using htr⟩

abbrev stateWord := FeatureCoordinateTransition96.stateWord

def packetClock (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :=
  193*((stateWord j ys cs qfuel jUnary carry).length+1)+
    clock depth j ys cs qfuel jUnary carry+
    2*(stateWord (j+1) ys (next depth j ys cs) qfuel jUnary carry).length+4

def machine (depth : Nat) : BitMachine.Machine := BitMachineBankWrapper.machine (program depth) (start depth) (control depth)

theorem outputs (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    (machine depth).OutputsWithin (stateWord j ys cs qfuel jUnary carry)
      (stateWord (j+1) ys (next depth j ys cs) qfuel jUnary carry)
      (packetClock depth j ys cs qfuel jUnary carry) := by
  let A := GenericFeatureCoordinateStage.initialBank j ys cs qfuel jUnary carry
  let B := GenericFeatureCoordinateStage.initialBank (j+1) ys (next depth j ys cs) qfuel jUnary carry
  let F : (Fin 96 → List Bool) → (Fin 96 → List Bool) := fun _ => B
  have h := BitMachineBankWrapper.outputs (program depth) (start depth) (control depth) F
    (BitMachineBankCodec.encode A) (clock depth j ys cs qfuel jUnary carry)
    (BitMachineBankCodec.encode B).length (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      have hs : A=S := Option.some.inj hd
      subst S
      obtain ⟨t,ht,hr⟩ := run depth j ys cs qfuel jUnary carry
      exact ⟨t,⟨none,control depth,B⟩,ht,hr,rfl,rfl⟩) (by
      intro S hd
      exact le_rfl)
  simpa only [machine,BitMachineBankWrapper.result,BitMachineBankCodec.decode_encode,
    F,packetClock,stateWord,A,B] using h

#print axioms run
#print axioms outputs
end CurrentAdditive.GenericFeatureCoordinateTransition
