import CurrentAdditive.FeatureCoordinateStage96
import EthInapproximability.CurrentPaper.BinarySuccessorMachine

/-! Physical reset of the descriptor scan and binary coordinate successor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.FeatureBankAdvance96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding

def incrementSlots : Fin 2 ↪ Fin 96 where
  toFun k := if k=0 then 15 else 19
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def incrementProgram (l : BinarySuccessorMachine.Label) :=
  BitMachineStackEmbedding.stmt incrementSlots id id id none
    (BinarySuccessorMachine.program l)

theorem increment_run (S : Fin 96 → List Bool) (j : Nat)
    (h15 : S 15=j.bits) (h19 : S 19=[]) :
    ∃ t ≤ 2*j.bits.length+2,
      ((advance incrementProgram)^[t])
        (⟨some .carry,none,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,none,Function.update S 15 (j+1).bits⟩ := by
  classical
  let c := BinarySuccessorMachine.cfg (some .carry) none j.bits []
  have hbank : BitMachineStackEmbedding.bank incrementSlots S c.stk=S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c,BinarySuccessorMachine.cfg,incrementSlots,h15,h19]
  have hrun : ((advance BinarySuccessorMachine.program)^[2*BinarySuccessorMachine.carryCount j.bits+2]) c=
      BinarySuccessorMachine.cfg none none (j+1).bits [] := by
    simpa [c,BinarySuccessorMachine.run,BinarySuccessorMachine.successor_bits] using
      BinarySuccessorMachine.run_correct none j.bits []
  have hhalt : (((advance BinarySuccessorMachine.program)^[2*BinarySuccessorMachine.carryCount j.bits+2]) c).l=none := by
    rw [hrun]
    rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs incrementSlots S
    id id id (by intro v; rfl) none BinarySuccessorMachine.program incrementProgram
    (by intro l; rfl) c (2*BinarySuccessorMachine.carryCount j.bits+2) hhalt
  rw [hrun] at he
  have hu : (BinarySuccessorMachine.cfg none none (j+1).bits []).stk=
      Function.update c.stk 0 (j+1).bits := by
    funext k
    fin_cases k <;> rfl
  change ((advance incrementProgram)^[t])
    ⟨some .carry,none,BitMachineStackEmbedding.bank incrementSlots S c.stk⟩ =
    ⟨none,none,BitMachineStackEmbedding.bank incrementSlots S
      (BinarySuccessorMachine.cfg none none (j+1).bits []).stk⟩ at he
  rw [hbank,hu,BitMachineStackEmbedding.bank_update,hbank] at he
  have hc := BinarySuccessorMachine.carryCount_le_length j.bits
  exact ⟨t,by omega,he⟩

def copySlots : Fin 3 ↪ Fin 96 where
  toFun k := ![12,13,19] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def copyProgram := ExactParameterBranchInstall.copyProgram copySlots
def clearProgram := FeaturePacketFinalize96.clearProgram 10
private def labelFor {L V : Type}
    (_P : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V) (l : L) := l
def firstProgram := BitMachineRawSequence.program clearProgram copyProgram .scan
  (((),none) : Unit × Option Bool) none
def firstStart := labelFor firstProgram (BitMachineRawSequence.leftLabel (false : Bool))
def firstControl := ((((),none) : Unit × Option Bool),(none : Option Bool))
def program := BitMachineRawSequence.program firstProgram incrementProgram .carry firstControl none
def start := labelFor program (BitMachineRawSequence.leftLabel firstStart)
def control := (firstControl,(none : Option Bool))

def result (S : Fin 96 → List Bool) (count : List Bool) (j : Nat) :=
  Function.update (Function.update (Function.update S 10 []) 13 count) 15 (j+1).bits
def clock (S : Fin 96 → List Bool) (count : List Bool) (j : Nat) :=
  (S 10).length+2*count.length+2*j.bits.length+8

theorem run (S : Fin 96 → List Bool) (count : List Bool) (j : Nat)
    (h12 : S 12=count) (h13 : S 13=[]) (h15 : S 15=j.bits) (h19 : S 19=[]) :
    ∃ t ≤ clock S count j,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,result S count j⟩ := by
  classical
  let A := Function.update S 10 []
  let B := Function.update A 13 count
  let a := (S 10).length+2
  have har := FeaturePacketFinalize96.clear_run 10 S
  obtain ⟨b,hb,hbr⟩ := ExactParameterBranchInstall.copy_run copySlots A count
    (by simpa [copySlots,A] using h12)
    (by simpa [copySlots,A] using h13)
    (by simpa [copySlots,A] using h19)
  change ((advance copyProgram)^[b]) ⟨some .scan,none,A⟩=⟨none,none,B⟩ at hbr
  obtain ⟨ab,hab,habr⟩ := BitMachineRawSequence.runs clearProgram copyProgram
    false .scan (((),none) : Unit × Option Bool) (((),none) : Unit × Option Bool)
    none none S A B a b har hbr
  obtain ⟨c,hc,hcr⟩ := increment_run B j
    (by simpa [B,A] using h15) (by simpa [B,A] using h19)
  obtain ⟨t,ht,htr⟩ := BitMachineRawSequence.runs firstProgram incrementProgram
    firstStart .carry firstControl firstControl none none S B (result S count j) ab c habr hcr
  refine ⟨t,?_,by simpa only [program,start,control] using htr⟩
  dsimp only [clock]
  dsimp only [a] at hab
  omega

#print axioms increment_run
#print axioms run
end CurrentAdditive.FeatureBankAdvance96
