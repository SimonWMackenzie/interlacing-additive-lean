import CurrentAdditive.FeatureCountHeader96
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Two source-preserving copies concatenate the actual count header and
body into an empty retained packet bank. The whole-bank result is exact. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeaturePacketJoin96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding

theorem append_run (ι : Fin 3 ↪ Fin 96) (S : Fin 96 → List Bool)
    (bits tail : List Bool) (hs : S (ι 0)=bits) (ht : S (ι 1)=tail)
    (hw : S (ι 2)=[]) :
    ∃ t≤2*bits.length+2,
      ((advance (ExactParameterBranchInstall.copyProgram ι))^[t])
        (⟨some .scan,none,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,none,Function.update S (ι 1) (bits++tail)⟩ := by
  let I := BitMachineCopy.cfg (some .scan) none bits tail []
  have hb : BitMachineStackEmbedding.bank ι S I.stk=S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [I,BitMachineCopy.cfg,BitMachineCopy.stackContents,hs,ht,hw]
  have hr := BitMachineCopy.run_correct none bits tail
  have hh : (((advance BitMachineCopy.program)^[2*bits.length+2]) I).l=none := by
    change (BitMachineCopy.run (2*bits.length+2) I).l=none
    rw [hr]
    rfl
  obtain ⟨t,hbound,he⟩ := BitMachineStackEmbedding.outputs ι S id id id
    (by intro v; rfl) none BitMachineCopy.program
    (ExactParameterBranchInstall.copyProgram ι) (by intro l; rfl) I
    (2*bits.length+2) hh
  change ((advance (ExactParameterBranchInstall.copyProgram ι))^[t])
      (BitMachineStackEmbedding.cfg ι S id id none I)=
    BitMachineStackEmbedding.cfg ι S id id none
      (BitMachineCopy.run (2*bits.length+2) I) at he
  rw [hr] at he
  have hl : BitMachineCopy.stackContents bits (bits++tail) []=
      Function.update I.stk 1 (bits++tail) := by funext k; fin_cases k <;> rfl
  change ((advance (ExactParameterBranchInstall.copyProgram ι))^[t])
      ⟨some .scan,none,BitMachineStackEmbedding.bank ι S I.stk⟩=
    ⟨none,none,BitMachineStackEmbedding.bank ι S
      (BitMachineCopy.stackContents bits (bits++tail) [])⟩ at he
  rw [hb,hl,BitMachineStackEmbedding.bank_update,hb] at he
  exact ⟨t,hbound,he⟩

def bodySlots : Fin 3 ↪ Fin 96 := ⟨![9,8,19],by decide⟩
def headerSlots : Fin 3 ↪ Fin 96 := ⟨![16,8,19],by decide⟩
def program := BitMachineRawSequence.program
  (ExactParameterBranchInstall.copyProgram bodySlots)
  (ExactParameterBranchInstall.copyProgram headerSlots)
  BitMachineCopy.Label.scan (none : Option Bool) (none : Option Bool)
def start : BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label :=
  BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def control := ((none : Option Bool),(none : Option Bool))
def clock (header body : List Bool) := 2*body.length+2*header.length+5

theorem run (S : Fin 96 → List Bool) (header body : List Bool)
    (h16 : S 16=header) (h9 : S 9=body) (h19 : S 19=[]) (h8 : S 8=[]) :
    ∃ t≤clock header body,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,control,Function.update S 8 (header++body)⟩ := by
  obtain ⟨a,ha,haRun⟩ := append_run bodySlots S body []
    (by simpa [bodySlots] using h9) (by simpa [bodySlots] using h8)
    (by simpa [bodySlots] using h19)
  let U := Function.update S (8 : Fin 96) body
  have haRun' : ((advance (ExactParameterBranchInstall.copyProgram bodySlots))^[a])
      ⟨some .scan,none,S⟩=⟨none,none,U⟩ := by simpa [U,bodySlots] using haRun
  obtain ⟨b,hb,hbRun⟩ := append_run headerSlots U header body
    (by simpa [U,headerSlots] using h16) (by simp [U,headerSlots])
    (by simpa [U,headerSlots] using h19)
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram bodySlots)
    (ExactParameterBranchInstall.copyProgram headerSlots)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    (none : Option Bool) (none : Option Bool) (none : Option Bool) (none : Option Bool)
    S U (Function.update S 8 (header++body)) a b haRun'
    (by simpa [U,headerSlots] using hbRun)
  exact ⟨t,by unfold clock; omega,by simpa only [program,start,control] using hr⟩

#print axioms run
end CurrentAdditive.FeaturePacketJoin96
