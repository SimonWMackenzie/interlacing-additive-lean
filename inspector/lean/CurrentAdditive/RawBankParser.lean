import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

namespace CurrentAdditive.RawBankParser
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
variable {K : Nat} {J : Type*} [DecidableEq J]

def program (slots : (Fin K ⊕ Fin 3) ↪ J) (l : BitMachineBankCodec.ParserLabel K):=
  BitMachineStackEmbedding.stmt slots id id id none (BitMachineBankCodec.parser K l)
def parsed (slots : (Fin K ⊕ Fin 3) ↪ J) (w : Fin K → List Bool):=
  BitMachineStackEmbedding.bank slots (fun _ : J => [])
    (BitMachineBankCodec.parserCfg (K:=K) none (some true) w [] [] []).stk

/-- The literal bank parser installs every field and leaves all remaining
ambient stacks empty; only the original serialized packet is supplied. -/
theorem physical_parse (slots : (Fin K ⊕ Fin 3) ↪ J) (w : Fin K → List Bool) :
    ∃t ≤ (2*K+1)*((BitMachineBankCodec.encode w).length+1),
      ((advance (program slots))^[t])
        (rawInit (slots (.inr 0)) (.scan 0 : BitMachineBankCodec.ParserLabel K)
          (none : Option Bool) (BitMachineBankCodec.encode w))=
      ⟨none,some true,parsed slots w⟩ := by
  obtain ⟨a,ha,hparse⟩:=BitMachineBankCodec.parser_correct K (BitMachineBankCodec.encode w) []
  rw [BitMachineBankCodec.decode_encode] at hparse
  let c:=BitMachineBankCodec.parserCfg (K:=K) (some (.scan 0)) none (fun _ => [])
    (BitMachineBankCodec.encode w) [] []
  have hc : c.stk=Function.update (fun _ : Fin K ⊕ Fin 3 => []) (.inr 0) (BitMachineBankCodec.encode w) := by
    funext z
    cases z with
    | inl z => simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
    | inr z => fin_cases z <;> simp [c,BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents]
  have hempty : BitMachineStackEmbedding.bank slots (fun _ : J => []) (fun _ => [])=
      (fun _ : J => []) := BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hinit : BitMachineStackEmbedding.bank slots (fun _ => []) c.stk=
      (rawInit (slots (.inr 0)) (.scan 0 : BitMachineBankCodec.ParserLabel K)
        (none : Option Bool) (BitMachineBankCodec.encode w)).stk := by
    rw [hc,BitMachineStackEmbedding.bank_update,hempty]
    funext z
    simp [rawInit,Function.update_apply]
  have hp : ((advance (BitMachineBankCodec.parser K))^[a]) c=
      BitMachineBankCodec.parserCfg none (some true) w [] [] []:=hparse
  obtain ⟨t,ht,he⟩:=BitMachineStackEmbedding.outputs slots (fun _ => [])
    id id id (fun _ => rfl) none (BitMachineBankCodec.parser K) (program slots)
    (fun _ => rfl) c a (by rw [hp]; rfl)
  rw [hp] at he
  simp only [BitMachineStackEmbedding.cfg,BitMachineStackEmbedding.stackCfg,BitMachineInline.cfg,id_eq] at he
  rw [hinit] at he
  exact ⟨t,ht.trans ha,he⟩

theorem parsed_at (slots : (Fin K ⊕ Fin 3) ↪ J) (w : Fin K → List Bool) (i : Fin K) :
    parsed slots w (slots (.inl i))=w i :=
  BitMachineStackEmbedding.bank_at slots _ _ (.inl i)

end
end CurrentAdditive.RawBankParser
