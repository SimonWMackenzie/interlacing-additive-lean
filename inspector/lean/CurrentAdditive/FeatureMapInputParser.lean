import CurrentAdditive.FeatureMapPairLoader

/-! Literal ordinary-input Bank2 loader: input15 is consumed, context12
and source8 are installed; all other ambient banks are preserved. -/

namespace CurrentAdditive.FeatureMapInputParser

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureMapPairLoader

variable {N : Nat}

def slots : BitMachineBankCodec.Stack 2 ↪ Stack N where
 toFun
  | .inl i => ![low 12,low 8] i
  | .inr i => ![low 15,low 16,low 17] i
 inj' := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [low,Fin.ext_iff]
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [low,Fin.ext_iff]
  | inr a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [low,Fin.ext_iff]
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [low,Fin.ext_iff]

def program (l : BitMachineBankCodec.ParserLabel 2) :=
 BitMachineStackEmbedding.stackStmt (slots (N := N)) (BitMachineBankCodec.parser 2 l)

def output (S : Stack N → List Bool) (context source : List Bool) :=
 Function.update (Function.update (Function.update S (low 15) []) (low 12) context)
   (low 8) source

theorem parse_run (S : Stack N → List Bool) (context source : List Bool)
 (h15 : S (low 15) = packet context source)
 (h12 : S (low 12) = []) (h8 : S (low 8) = [])
 (h16 : S (low 16) = []) (h17 : S (low 17) = []) :
 ∃ t ≤ 5*((packet context source).length+1),
 ((advance (program (N := N)))^[t])
   (⟨some (.scan 0), none, S⟩ : TM2.Cfg (fun _ : Stack N => Bool) _ _) =
   ⟨none,some true,output S context source⟩ := by
 obtain ⟨t,ht,hr⟩ := BitMachineBankCodec.parser_correct 2 (packet context source) []
 have hd : BitMachineBankCodec.decode 2 (packet context source) =
     some (![context,source] : Fin 2 → List Bool) :=
   BitMachineBankCodec.decode_encode _
 rw [hd] at hr
 have hin : ∀ k, (BitMachineBankCodec.parserCfg (some (.scan 0)) none
     (fun _ : Fin 2 => []) (packet context source) [] []).stk k = S (slots k) := by
   intro k
   cases k with
   | inl k => fin_cases k <;>
       simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,slots,h12,h8]
   | inr k => fin_cases k <;>
       simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,slots,h15,h16,h17]
 have h := WeightedRawWords.region_run (slots (N := N))
   (BitMachineBankCodec.parser 2) _ _ _ hr S hin
 refine ⟨t,ht,?_⟩
 change ((advance (program (N := N)))^[t]) _ = _ at h
 refine h.trans ?_
 congr 1
 have hb : BitMachineBankCodec.contents (![context,source] : Fin 2 → List Bool) [] [] [] =
     Function.update (Function.update (Function.update (fun k => S (slots k))
       (.inr 0) []) (.inl 0) context) (.inl 1) source := by
   funext k
   cases k with
   | inl k => fin_cases k <;> rfl
   | inr k =>
     fin_cases k
     · rfl
     · change [] = _
       simp [Function.update_apply,slots,h16]
     · change [] = _
       simp [Function.update_apply,slots,h17]
 change BitMachineStackEmbedding.bank slots S
   (BitMachineBankCodec.contents (![context,source] : Fin 2 → List Bool) [] [] []) = _
 rw [hb,BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_update,
   BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_restrict]
 rfl

#print axioms parse_run

end CurrentAdditive.FeatureMapInputParser
