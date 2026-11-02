import CurrentAdditive.GaussAnyWidthCertifiedVector
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Real Bank2 parsing into the complete wide post-Gauss vector bank.
The input is precisely [state packet, unary retained column count]. -/

namespace CurrentAdditive.GaussPostloopSerialized
noncomputable section

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open GaussWideVectorInvoke GaussFirstFreeCandidate GaussCertificateVectorABI

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev Stack := GaussWideVectorInvoke.Bank ⊕ Fin 3
def inputCell : Stack := .inr 0
def outputCell : Stack := .inl GaussWideVectorInvoke.slots.target
def fieldSlot (i : Fin 2) : Stack :=
  .inl (GaussWideVectorInvoke.oldEmbed (![ (0:OldBank), (3:OldBank)] i))
def parseMap : Fin 2 ⊕ Fin 3 → Stack
  | .inl i => fieldSlot i
  | .inr i => .inr i

theorem parseMap_injective : Function.Injective parseMap := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hh := GaussWideVectorInvoke.oldEmbed.injective (Sum.inl.inj h)
      fin_cases a <;> fin_cases b <;> simp [fieldSlot,parseMap] at hh ⊢
    | inr b => simp [parseMap,fieldSlot] at h
  | inr a =>
    cases b with
    | inl b => simp [parseMap,fieldSlot] at h
    | inr b => exact congrArg Sum.inr (Sum.inr.inj h)

def parseSlots : (Fin 2 ⊕ Fin 3) ↪ Stack := ⟨parseMap,parseMap_injective⟩
def parserProgram (l : BitMachineBankCodec.ParserLabel 2) :=
  BitMachineStackEmbedding.stmt parseSlots id id id none (BitMachineBankCodec.parser 2 l)
def localFinal (w : Fin 2 → List Bool) :=
  (BitMachineBankCodec.parserCfg (K:=2) none (some true) w [] [] []).stk
def parsed (w : Fin 2 → List Bool) : Stack → List Bool :=
  BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)

theorem parsed_at (w : Fin 2 → List Bool) (i : Fin 2) : parsed w (fieldSlot i)=w i := by
  change BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)
    (parseSlots (.inl i))=w i
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem parsed_aux (w : Fin 2 → List Bool) (i : Fin 3) : parsed w (.inr i)=[] := by
  change BitMachineStackEmbedding.bank parseSlots (fun _ => []) (localFinal w)
    (parseSlots (.inr i))=[]
  rw [BitMachineStackEmbedding.bank_at]
  fin_cases i <;> rfl

theorem parsed_other (w : Fin 2 → List Bool) (b : GaussWideVectorInvoke.Bank)
    (h0 : b≠oldEmbed (0:OldBank)) (h3 : b≠oldEmbed (3:OldBank)) :
    parsed w (.inl b)=[] := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨z,hz⟩
  cases z with
  | inl z => fin_cases z <;> simp [parseSlots,parseMap,fieldSlot] at hz
             all_goals first | exact h0 hz.symm | exact h3 hz.symm
  | inr z => simp [parseSlots,parseMap] at hz

theorem parse_run (w : Fin 2 → List Bool) :
    ∃ t≤5*((BitMachineBankCodec.encode w).length+1),
      ((advance parserProgram)^[t])
        (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2)
          (none:Option Bool) (BitMachineBankCodec.encode w))=
        ⟨none,some true,parsed w⟩ := by
  obtain ⟨a,ha,hparse⟩:=BitMachineBankCodec.parser_correct 2 (BitMachineBankCodec.encode w) []
  rw [BitMachineBankCodec.decode_encode] at hparse
  change BitMachineBankCodec.parserRun a
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
      (BitMachineBankCodec.encode w) [] [])=
    BitMachineBankCodec.parserCfg none (some true) w [] [] [] at hparse
  let c:=BitMachineBankCodec.parserCfg (K:=2) (some (.scan 0)) none (fun _ => [])
    (BitMachineBankCodec.encode w) [] []
  have hc : c.stk=Function.update (fun _ : Fin 2 ⊕ Fin 3 => []) (.inr 0)
      (BitMachineBankCodec.encode w) := by
    funext z
    cases z with
    | inl z => simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr z => fin_cases z <;> simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hempty : BitMachineStackEmbedding.bank parseSlots (fun _ => []) (fun _ => [])=
      (fun _ : Stack => []) := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro z
    rfl
  have hinit : BitMachineStackEmbedding.bank parseSlots (fun _ => []) c.stk=
      (rawInit inputCell (.scan 0 : BitMachineBankCodec.ParserLabel 2) (none:Option Bool)
        (BitMachineBankCodec.encode w)).stk := by
    rw [hc,BitMachineStackEmbedding.bank_update,hempty]
    funext z
    simp [parseSlots,parseMap,inputCell,rawInit,Function.update_apply]
  have hp : ((advance (BitMachineBankCodec.parser 2))^[a]) c=
      BitMachineBankCodec.parserCfg none (some true) w [] [] [] := hparse
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs parseSlots (fun _ => []) id id id
    (by intro z; rfl) none (BitMachineBankCodec.parser 2) parserProgram (by intro l; rfl)
    c a (by rw [hp]; rfl)
  rw [hp] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq] at he
  rw [hinit] at he
  exact ⟨t,ht.trans ha,he⟩

def words (state : List Bool) (k : Nat) : Fin 2 → List Bool :=
  ![state,List.replicate k true]
def packet (state : List Bool) (k : Nat) : List Bool := BitMachineBankCodec.encode (words state k)
def installed (state : List Bool) (k : Nat) : Stack → List Bool :=
  Sum.elim (wide (GaussStateMatrixContext.inputBank state k)) (fun _ => [])

theorem parsed_exact (state : List Bool) (k : Nat) : parsed (words state k)=installed state k := by
  funext z
  cases z with
  | inr i => exact parsed_aux _ i
  | inl b =>
    by_cases h0 : b=oldEmbed (0:OldBank)
    · subst b
      have hp := parsed_at (words state k) 0
      simpa [fieldSlot,words,installed,wide_at,GaussStateMatrixContext.inputBank,
        GaussStateMatrixContext.selectorSlots] using hp
    by_cases h3 : b=oldEmbed (3:OldBank)
    · subst b
      have hp := parsed_at (words state k) 1
      simpa [fieldSlot,words,installed,wide_at,GaussStateMatrixContext.inputBank,
        GaussStateMatrixContext.selectorSlots] using hp
    rw [parsed_other _ b h0 h3]
    change []=wide (GaussStateMatrixContext.inputBank state k) b
    unfold wide BitMachineStackEmbedding.bank
    split
    · rename_i hi
      have hi0 : Classical.choose hi≠(0:OldBank) := by
        intro h
        exact h0 (by simpa [h] using (Classical.choose_spec hi).symm)
      have hi3 : Classical.choose hi≠(3:OldBank) := by
        intro h
        exact h3 (by simpa [h] using (Classical.choose_spec hi).symm)
      have hthree : (3:OldBank)=⟨3,by omega⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt (by change 3<32+BaseCount; omega)
      simp only [hthree] at hi3
      simp [GaussStateMatrixContext.inputBank,GaussStateMatrixContext.selectorSlots,hi0,hi3]
    · rfl

def bodySlots : GaussWideVectorInvoke.Bank ↪ Stack := ⟨Sum.inl,Sum.inl_injective⟩
def bodyProgram (l : BitMachineRawSequence.Label OldLabel NewLabel) :=
  BitMachineStackEmbedding.stmt bodySlots id id id none (GaussWideVectorInvoke.program l)

def program := BitMachineRawSequence.program parserProgram bodyProgram
  GaussWideVectorInvoke.start (none:Option Bool) GaussWideVectorInvoke.control
abbrev Label := BitMachineRawSequence.Label (BitMachineBankCodec.ParserLabel 2)
  (BitMachineRawSequence.Label OldLabel NewLabel)
def start : Label := BitMachineRawSequence.leftLabel (.scan 0)
def control := ((none:Option Bool),GaussWideVectorInvoke.control)

#print axioms parse_run
#print axioms parsed_exact

end
end CurrentAdditive.GaussPostloopSerialized
