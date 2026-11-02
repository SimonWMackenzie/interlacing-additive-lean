import EthInapproximability.CurrentPaper.WeightedRawWordsCore

/-! # S1: unpack the branch packet and write the fixed constant

The literal packet `SourceOriginalBranchPackets.packet n w` is parsed by the
production `BankFieldProjection.program` (K = 2, j = 1), embedded into the
global bank: field 0 (unary `n`) lands in master `N`, field 1 (the graph word
`w`) lands in master `Gw`, and the input stack is consumed. A rejected parse
halts the same fixed program in the charged handoff. Then the production
`SourceClauseFixedUnary.program` pushes unary `c` into master `C`; `c` is a
program constant fixed before the machine. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

/-- Embedding of the packet parser's stacks. -/
def parseSlots : BitMachineBankCodec.Stack 2 ↪ Global where
  toFun
    | .inl 0 => aux .N
    | .inl 1 => aux (.parse 0)
    | .inr 0 => aux .input
    | .inr 1 => aux (.parse 1)
    | .inr 2 => aux .Gw
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;>
      fin_cases a <;> fin_cases b <;> simp_all [aux]

def parseProgram := fun l => stackStmt parseSlots
  (BankFieldProjection.program (1 : Fin 2) l)

/-- Guard: the parser's rejecting halt is exactly control `some false`. -/
def parseOk : BitMachineBankCodec.Control → Bool
  | some false => false
  | _ => true

/-- Bank after the parse: `N = unary n`, `Gw = w`, all else empty. -/
def afterParse (n : ℕ) (w : List Bool) : Global → List Bool :=
  Function.update (Function.update (fun _ => []) (aux .N) (List.replicate n true))
    (aux .Gw) w

/-- Bank at the end of S1. -/
def afterUnpack (n : ℕ) (w : List Bool) (c : ℕ) : Global → List Bool :=
  Function.update (afterParse n w) (aux .C) (List.replicate c true)

theorem parse_valid (n : ℕ) (w : List Bool) :
    ∃ t ≤ 7 * ((SourceOriginalBranchPackets.packet n w).length + 1) + 1,
      ((advance parseProgram)^[t])
        (⟨some (.inl (.scan 0)), none,
          startBank (SourceOriginalBranchPackets.packet n w)⟩ :
          TM2.Cfg (fun _ : Global => Bool) (BankFieldProjection.Label 2)
            BitMachineBankCodec.Control) =
        ⟨none, none, afterParse n w⟩ := by
  obtain ⟨t, ht, hr⟩ := BankFieldProjection.valid_run (1 : Fin 2)
    (SourceOriginalBranchPackets.packet n w)
    (SourceOriginalBranchPackets.bank n w)
    (SourceOriginalBranchPackets.packet_decode n w)
  refine ⟨t, by simpa using ht, ?_⟩
  have h := region_run parseSlots (BankFieldProjection.program (1 : Fin 2))
    _ _ t hr (startBank (SourceOriginalBranchPackets.packet n w))
    (by
      intro k
      rcases k with k | k <;> fin_cases k <;>
        simp [BankFieldProjection.cfg, BitMachineBankCodec.contents, startBank,
          parseSlots, aux])
  refine h.trans ?_
  simp only [BankFieldProjection.cfg]
  congr 1
  have hloc : BitMachineBankCodec.contents
      (Function.update (SourceOriginalBranchPackets.bank n w) 1 []) [] []
      (SourceOriginalBranchPackets.bank n w 1) =
      Function.update (Function.update (Function.update
        (fun k => startBank (SourceOriginalBranchPackets.packet n w) (parseSlots k))
        (.inr 0) []) (.inl 0) (List.replicate n true)) (.inr 2) w := by
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [BitMachineBankCodec.contents, SourceOriginalBranchPackets.bank,
        startBank, parseSlots, aux]
  rw [hloc, bank_update, bank_update, bank_update, bank_restrict]
  funext j
  simp only [afterParse, startBank, Function.update_apply]
  by_cases h1 : j = parseSlots (.inr 2) <;> by_cases h2 : j = parseSlots (.inl 0) <;>
    by_cases h3 : j = parseSlots (.inr 0) <;>
    simp_all [parseSlots, aux]

/-- The rejecting branch: on an undecodable input the embedded parser halts
with control `some false`; the output stack is empty. -/
theorem parse_reject (input : List Bool)
    (hd : BitMachineBankCodec.decode 2 input = none) :
    ∃ t ≤ 5 * (input.length + 1) + 1, ∃ T : Global → List Bool,
      ((advance parseProgram)^[t])
        (⟨some (.inl (.scan 0)), none, startBank input⟩ :
          TM2.Cfg (fun _ : Global => Bool) (BankFieldProjection.Label 2)
            BitMachineBankCodec.Control) =
        ⟨none, some false, T⟩ := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct 2 input []
  rw [hd] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool)
      (BitMachineBankCodec.ParserLabel 2) BitMachineBankCodec.Control :=
    BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 2 → BankFieldProjection.Label 2)
    id id (fun _ => rfl) (some (.inr .parsed)) (BitMachineBankCodec.parser 2)
    (BankFieldProjection.program (1 : Fin 2)) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] [])
    t hp.1
  have hf : advance (BankFieldProjection.program (1 : Fin 2))
      (BitMachineInline.cfg
        (Sum.inl : BitMachineBankCodec.ParserLabel 2 → BankFieldProjection.Label 2)
        id (some (.inr .parsed)) c) =
      (⟨none, some false, c.stk⟩ : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool)
        (BankFieldProjection.Label 2) BitMachineBankCodec.Control) := by
    simp only [BitMachineInline.cfg, hp.1, hp.2.1, id_eq, advance, TM2.step,
      BankFieldProjection.program, TM2.stepAux, Option.getD_some, cond_false]
  have hlocal : ((advance (BankFieldProjection.program (1 : Fin 2)))^[u + 1])
      (BankFieldProjection.cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
      ⟨none, some false, c.stk⟩ := by
    rw [Function.iterate_succ_apply']
    change advance _ (((advance (BankFieldProjection.program (1 : Fin 2)))^[u])
      (BitMachineInline.cfg
        (Sum.inl : BitMachineBankCodec.ParserLabel 2 → BankFieldProjection.Label 2)
        id (some (.inr .parsed))
        (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => []) input [] []))) = _
    rw [hr]
    exact hf
  have h := region_run parseSlots (BankFieldProjection.program (1 : Fin 2))
    _ _ (u + 1) hlocal (startBank input)
    (by
      intro k
      rcases k with k | k <;> fin_cases k <;>
        simp [BankFieldProjection.cfg, BitMachineBankCodec.contents, startBank,
          parseSlots, aux])
  exact ⟨u + 1, by omega, _, h⟩

/-- The fixed constant `c` (a program constant) written into master `C`. -/
def constProgram (c : ℕ) := SourceClauseFixedUnary.program (aux .C) c

theorem const_run (n : ℕ) (w : List Bool) (c : ℕ) :
    ((advance (constProgram c))^[c + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label c), (), afterParse n w⟩ :
        TM2.Cfg (fun _ : Global => Bool) (SourceClauseFixedUnary.Label c) Unit) =
      ⟨none, (), afterUnpack n w c⟩ :=
  SourceClauseFixedUnary.run (aux .C) (afterParse n w) c
    (by simp [afterParse, aux])

section Composite

variable {LB VB : Type*}

/-- S1 as the head of one fixed program: guarded parse, charged handoff,
constant writer, charged handoff, then an arbitrary continuation `B`. -/
def unpackProgram (c : ℕ) (B : LB → TM2.Stmt (fun _ : Global => Bool) LB VB)
    (b₀ : LB) (w₀ : VB) :=
  gprogram parseProgram
    (BitMachineRawSequence.program (constProgram c) B b₀ () w₀) parseOk
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label c))
    none ((), w₀)

def unpackStart (c : ℕ) (input : List Bool) (w₀ : VB) :
    TM2.Cfg (fun _ : Global => Bool)
      (BitMachineRawSequence.Label (BankFieldProjection.Label 2)
        (BitMachineRawSequence.Label (SourceClauseFixedUnary.Label c) LB))
      (BitMachineRawSequence.Control BitMachineBankCodec.Control
        (BitMachineRawSequence.Control Unit VB)) :=
  ⟨some (BitMachineRawSequence.leftLabel (.inl (.scan 0))), (none, ((), w₀)),
    startBank input⟩

/-- Valid packet: the continuation starts from `afterUnpack n w c`. -/
theorem unpack_valid (n : ℕ) (w : List Bool) (c : ℕ)
    (B : LB → TM2.Stmt (fun _ : Global => Bool) LB VB) (b₀ : LB) (w₀ w₁ : VB)
    (U : Global → List Bool) (tb : ℕ)
    (hb : ((advance B)^[tb]) (⟨some b₀, w₀, afterUnpack n w c⟩ :
      TM2.Cfg (fun _ : Global => Bool) LB VB) = ⟨none, w₁, U⟩) :
    ∃ t ≤ (7 * ((SourceOriginalBranchPackets.packet n w).length + 1) + 1) +
        ((c + 1) + tb + 1) + 1,
      ((advance (unpackProgram c B b₀ w₀))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n w) w₀) =
        ⟨none, (none, ((), w₁)), U⟩ := by
  obtain ⟨ta, hta, ha⟩ := parse_valid n w
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs (constProgram c) B
    (0 : SourceClauseFixedUnary.Label c) b₀ () () w₀ w₁
    (afterParse n w) (afterUnpack n w c) U (c + 1) tb (const_run n w c) hb
  obtain ⟨t, ht, h⟩ := gruns parseProgram
    (BitMachineRawSequence.program (constProgram c) B b₀ () w₀) parseOk
    (.inl (.scan 0)) (BitMachineRawSequence.leftLabel 0) none none ((), w₀)
    ((), w₁) (startBank (SourceOriginalBranchPackets.packet n w))
    (afterParse n w) U ta t2 ha rfl h2
  exact ⟨t, by omega, h⟩

/-- Undecodable input: the same fixed program halts in the guard. -/
theorem unpack_reject (c : ℕ) (input : List Bool)
    (hd : BitMachineBankCodec.decode 2 input = none)
    (B : LB → TM2.Stmt (fun _ : Global => Bool) LB VB) (b₀ : LB) (w₀ : VB) :
    ∃ t ≤ 5 * (input.length + 1) + 2, ∃ T : Global → List Bool,
      ((advance (unpackProgram c B b₀ w₀))^[t]) (unpackStart c input w₀) =
        ⟨none, (some false, ((), w₀)), T⟩ := by
  obtain ⟨ta, hta, T, ha⟩ := parse_reject input hd
  obtain ⟨t, ht, h⟩ := greject parseProgram
    (BitMachineRawSequence.program (constProgram c) B b₀ () w₀) parseOk
    (.inl (.scan 0)) (BitMachineRawSequence.leftLabel 0) none (some false) ((), w₀)
    (startBank input) T ta ha rfl
  exact ⟨t, by omega, T, h⟩

end Composite

#print axioms parse_valid
#print axioms parse_reject
#print axioms const_run
#print axioms unpack_valid
#print axioms unpack_reject

end
end EthInapproximability.CurrentPaper.WeightedRawWords
