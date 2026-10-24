import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A literal parser followed by a fixed finite-bank program. The adapter
installs every bank cell from ordinary framed bytes and starts all scratch
cells empty. It supplies no semantic operation to its finite control. -/
namespace CurrentAdditive.V40PackedProgram
noncomputable section
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open BitMachineStackEmbedding
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
variable {K L V : Type} [Fintype K] [DecidableEq K]
  [Fintype L] [Fintype V]

abbrev Stack (K : Type) := K ⊕ Fin 3
def numbering : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
def pack (S : K → List Bool) := BitMachineBankCodec.encode (fun i => S ((numbering (K:=K)).symm i))
def parseSlots : (Fin (Fintype.card K) ⊕ Fin 3) ↪ Stack K :=
  ⟨Sum.map (numbering (K:=K)).symm id,by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl ((numbering (K:=K)).symm.injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a => cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj h)⟩
def parserProgram (l : BitMachineBankCodec.ParserLabel (Fintype.card K)) :=
  BitMachineStackEmbedding.stmt (parseSlots (K:=K)) id id id none (BitMachineBankCodec.parser _ l)
def bodySlots : K ↪ Stack K := ⟨Sum.inl,Sum.inl_injective⟩
def bodyProgram (P : L → TM2.Stmt (fun _ : K => Bool) L V) (l : L) :=
  BitMachineStackEmbedding.stmt (bodySlots (K:=K)) id id id none (P l)
def program (P : L → TM2.Stmt (fun _ : K => Bool) L V) (start : L) (initial : V) :=
  BitMachineRawSequence.program (parserProgram (K:=K)) (bodyProgram P) start none initial
def machine (P : L → TM2.Stmt (fun _ : K => Bool) L V) (start : L) (initial : V) (port : K) :
    BitMachine.Machine :=
  ofFinite (.inr 0:Stack K) (.inl port) (BitMachineRawSequence.leftLabel (.scan 0))
    ((none:Option Bool),initial) (program P start initial)

def parsed (S : K → List Bool) : Stack K → List Bool := Sum.elim S (fun _ => [])
theorem parser_final (S : K → List Bool) :
    bank (parseSlots (K:=K)) (fun _ : Stack K => [])
      (BitMachineBankCodec.parserCfg (K:=Fintype.card K) none (some true)
        (fun i => S ((numbering (K:=K)).symm i)) [] [] []).stk=parsed S := by
  funext j
  cases j with
  | inl j =>
    rw [show (Sum.inl j:Stack K)=parseSlots (.inl (numbering j)) by simp [parseSlots]]
    rw [bank_at]
    simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,parsed,parseSlots]
  | inr j =>
    change bank _ _ _ (parseSlots (.inr j))=_
    rw [bank_at]
    fin_cases j <;> rfl

theorem parse_run (S : K → List Bool) :
    ∃t ≤ (2*Fintype.card K+1)*((pack S).length+1),
      ((advance (parserProgram (K:=K)))^[t])
        (rawInit (.inr 0:Stack K) (.scan 0 : BitMachineBankCodec.ParserLabel (Fintype.card K))
          (none:Option Bool) (pack S))=⟨none,some true,parsed S⟩ := by
  let W := fun i => S ((numbering (K:=K)).symm i)
  obtain ⟨a,ha,hparse⟩:=BitMachineBankCodec.parser_correct (Fintype.card K)
    (BitMachineBankCodec.encode W) []
  rw [BitMachineBankCodec.decode_encode] at hparse
  let c:=BitMachineBankCodec.parserCfg (K:=Fintype.card K) (some (.scan 0)) none
    (fun _ => []) (pack S) [] []
  have hp : ((advance (BitMachineBankCodec.parser (Fintype.card K)))^[a]) c=
      BitMachineBankCodec.parserCfg none (some true) W [] [] [] := hparse
  have hc : c.stk=Function.update (fun _ : Fin (Fintype.card K) ⊕ Fin 3 => []) (.inr 0) (pack S) := by
    funext z
    cases z with
    | inl z => simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr z => fin_cases z <;> simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hz : bank (parseSlots (K:=K)) (fun _ : Stack K => []) (fun _ => [])=(fun _ : Stack K => []) :=
    bank_eq_self _ _ _ (fun _ => rfl)
  have hi : bank (parseSlots (K:=K)) (fun _ : Stack K => []) c.stk=
      (rawInit (.inr 0:Stack K) (.scan 0 : BitMachineBankCodec.ParserLabel (Fintype.card K))
        (none:Option Bool) (pack S)).stk := by
    rw [hc,bank_update,hz]
    funext z
    simp [parseSlots,rawInit,Function.update_apply]
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs (parseSlots (K:=K)) (fun _ => [])
    id id id (fun _ => rfl) none (BitMachineBankCodec.parser (Fintype.card K))
    parserProgram (fun _ => rfl) c a (by rw [hp]; rfl)
  rw [hp] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq] at he
  rw [hi] at he
  have hf:=parser_final S
  change bank _ _ (BitMachineBankCodec.parserCfg (K:=Fintype.card K) none (some true) W [] [] []).stk=_ at hf
  rw [hf] at he
  exact ⟨t,ht.trans ha,he⟩

theorem outputs (P : L → TM2.Stmt (fun _ : K => Bool) L V) (start : L) (initial : V) (port : K)
    (S T : K → List Bool) (last : V) (b B : Nat)
    (hb : b ≤ B)
    (hr : ((advance P)^[b]) (⟨some start,initial,S⟩ : TM2.Cfg (fun _ : K => Bool) L V)=⟨none,last,T⟩) :
    (machine P start initial port).OutputsWithin (pack S) (T port)
      ((2*Fintype.card K+1)*((pack S).length+1)+B+1) := by
  obtain ⟨a,ha,hparse⟩:=parse_run S
  let c : TM2.Cfg (fun _ : K => Bool) L V:=⟨some start,initial,S⟩
  obtain ⟨d,hd,he⟩:=BitMachineStackEmbedding.outputs (bodySlots (K:=K)) (fun _ : Stack K => [])
    id id id (fun _ => rfl) none P (bodyProgram P) (fun _ => rfl) c b (by rw [hr])
  change ((advance P)^[b]) c=⟨none,last,T⟩ at hr
  rw [hr] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq] at he
  have hbank (W : K → List Bool) : bank (bodySlots (K:=K)) (fun _ : Stack K => []) W=parsed W := by
    funext z
    cases z with
    | inl z => exact bank_at _ _ _ z
    | inr z => exact bank_outside _ _ _ _ (by rintro ⟨i,h⟩; cases h)
  simp only [c,hbank] at he
  obtain ⟨t,ht,hfull⟩:=BitMachineRawSequence.runs (parserProgram (K:=K)) (bodyProgram P)
    (.scan 0) start none (some true) initial last
    (rawInit (.inr 0:Stack K) (.scan 0 : BitMachineBankCodec.ParserLabel (Fintype.card K))
      (none:Option Bool) (pack S)).stk (parsed S) (parsed T) a d hparse he
  apply outputsWithin_of_raw_run (.inr 0:Stack K) (.inl port)
    (BitMachineRawSequence.leftLabel (.scan 0)) ((none:Option Bool),initial)
    (program P start initial) (pack S) (T port) t _ (by omega)
  · exact congrArg TM2.Cfg.l hfull
  · exact congrArg (fun c => c.stk (.inl port)) hfull

#print axioms outputs
end
end CurrentAdditive.V40PackedProgram
