import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.WeightedRawWordsCore

namespace CurrentAdditive.WeightedIterationLoader

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

variable (M : BitMachine.Machine)

abbrev Stack := BitMachineIteration.Stack M ⊕ Fin 3

def slots : BitMachineBankCodec.Stack 2 ↪ Stack M where
  toFun
    | .inl i => if i=0 then .inl (.inl M.input) else .inl (.inr 0)
    | .inr i => .inr i
  inj' := by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all
      | inr b => fin_cases a <;> simp_all
    | inr a => cases b with
      | inl b => fin_cases b <;> simp_all
      | inr b => simpa using h

def packet (state fuel : List Bool) : List Bool :=
  BitMachineBankCodec.encode (![state,fuel] : Fin 2 → List Bool)

def program (l : BitMachineBankCodec.ParserLabel 2) :=
  BitMachineStackEmbedding.stackStmt (slots M) (BitMachineBankCodec.parser 2 l)

def initialBank (input : List Bool) : Stack M → List Bool :=
  fun i => if i=.inr 0 then input else []

def readyBank (state fuel : List Bool) : Stack M → List Bool :=
  Sum.elim (BitMachineIteration.ready M state fuel).stk (fun _ => [])

theorem parse (state fuel : List Bool) :
  ∃ t ≤ 5*((packet state fuel).length+1),
    ((advance (program M))^[t])
      (⟨some (.scan 0),none,initialBank M (packet state fuel)⟩ : TM2.Cfg _ _ _) =
      ⟨none,some true,readyBank M state fuel⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineBankCodec.parser_correct 2 (packet state fuel) []
  have hd : BitMachineBankCodec.decode 2 (packet state fuel) =
      some (![state,fuel] : Fin 2 → List Bool) := BitMachineBankCodec.decode_encode _
  rw [hd] at hr
  have hin : ∀ k,
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ : Fin 2 => []) (packet state fuel) [] []).stk k =
      initialBank M (packet state fuel) (slots M k) := by
    intro k
    cases k with
    | inl k => fin_cases k <;>
        simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,slots,initialBank]
    | inr k => fin_cases k <;>
        simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,slots,initialBank]
  have he := WeightedRawWords.region_run (slots M) (BitMachineBankCodec.parser 2)
    _ _ _ hr (initialBank M (packet state fuel)) hin
  refine ⟨t,ht,?_⟩
  change ((advance (program M))^[t]) _ = _ at he
  refine he.trans ?_
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k =>
        by_cases hk:k=M.input
        · subst k
          change BitMachineStackEmbedding.bank (slots M) _ _ (slots M (.inl 0)) = _
          rw [BitMachineStackEmbedding.bank_at]
          simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,readyBank,BitMachineIteration.ready,
            BitMachineIteration.adminCfg,BitMachine.Machine.init]
        · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ (by
            intro ⟨j,hj⟩
            cases j with
            | inl j => fin_cases j <;> simp_all [slots]
            | inr j => simp [slots] at hj)]
          simp [initialBank,readyBank,BitMachineIteration.ready,
            BitMachineIteration.adminCfg,BitMachine.Machine.init,hk]
    | inr k =>
        fin_cases k
        · change BitMachineStackEmbedding.bank (slots M) _ _ (slots M (.inl 1)) = _
          rw [BitMachineStackEmbedding.bank_at]
          simp [BitMachineBankCodec.parserCfg,BitMachineBankCodec.contents,readyBank,BitMachineIteration.ready,
            BitMachineIteration.adminCfg,BitMachineIteration.foreign]
        · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ (by
            intro ⟨j,hj⟩
            cases j with
            | inl j => fin_cases j <;> simp [slots] at hj
            | inr j => simp [slots] at hj)]
          simp [initialBank,readyBank,BitMachineIteration.ready,
            BitMachineIteration.adminCfg,BitMachineIteration.foreign]
  | inr k =>
      change BitMachineStackEmbedding.bank (slots M) _ _ (slots M (.inr k)) = _
      rw [BitMachineStackEmbedding.bank_at]
      fin_cases k <;> rfl

#print axioms parse

end CurrentAdditive.WeightedIterationLoader
