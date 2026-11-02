import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Embed a cited, finite bit machine into the second field of an original-n
packet. The first field is a preserved physical stack, not recomputed. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCore

open Turing BitMachineEncoding

variable (M : BitMachine.Machine)

abbrev Stack := Fin 1 ⊕ (Fin M.stackCount ⊕ Fin 3)
abbrev Label := BitMachineBankCodec.ParserLabel 2 ⊕
  (Fin M.labelCount ⊕ (Unit ⊕ BitMachineBankSerialize.Label 2))
abbrev Control := Option Bool × (Fin M.controlCount × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def parserStack : BitMachineBankCodec.Stack 2 ↪ Stack M where
  toFun
    | .inl k => if k = 0 then .inl 0 else .inr (.inl M.input)
    | .inr j => .inr (.inr j)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp at h ⊢
        | inr b => fin_cases a <;> fin_cases b <;> simp at h
    | inr a =>
        cases b with
        | inl b => fin_cases b <;> simp at h
        | inr b => simpa using h

def machineStack : Fin M.stackCount ↪ Stack M where
  toFun k := .inr (.inl k)
  inj' := by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)

def serializerStack : BitMachineBankSerialize.Stack 2 ↪ Stack M where
  toFun
    | .inl k => if k = 0 then .inl 0 else .inr (.inl M.output)
    | .inr j => .inr (.inr j)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp at h ⊢
        | inr b => fin_cases a <;> fin_cases b <;> simp at h
    | inr a =>
        cases b with
        | inl b => fin_cases b <;> simp at h
        | inr b => simpa using h

def parserControl (v : Option Bool) : Control M := (v,(M.initial,none))
def machineControl (v : Fin M.controlCount) : Control M := (some true,(v,none))
def serializerControl (v : Option Bool) : Control M := (some true,(M.initial,v))

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => BitMachineStackEmbedding.stmt (parserStack M) Sum.inl
      (parserControl M) Prod.fst (some (.inr (.inl M.start)))
      (BitMachineBankCodec.parser 2 l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt (machineStack M)
      (fun l => .inr (.inl l)) (machineControl M) (fun v => v.2.1)
      (some (.inr (.inr (.inl ())))) (M.program l)
  | .inr (.inr (.inl ())) =>
      TM2.Stmt.load (fun _ => serializerControl M none)
        (TM2.Stmt.goto (fun _ => .inr (.inr (.inr (.emit 0)))))
  | .inr (.inr (.inr l)) => BitMachineStackEmbedding.stmt (serializerStack M)
      (fun l => .inr (.inr (.inr l))) (serializerControl M) (fun v => v.2.2)
      none (BitMachineBankSerialize.program 2 l)

def run (t : ℕ) (c : Config M) : Config M := ((advance (program M))^[t]) c

noncomputable def entry (packet : List Bool) : Config M :=
  BitMachineStackEmbedding.cfg (parserStack M) (fun _ => []) Sum.inl
    (parserControl M) (some (.inr (.inl M.start)))
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) packet [] [])

noncomputable def afterParse (n : ℕ) (word : List Bool) : Config M :=
  BitMachineStackEmbedding.cfg (parserStack M) (fun _ => []) Sum.inl
    (parserControl M) (some (.inr (.inl M.start)))
    (BitMachineBankCodec.parserCfg none (some true)
      (SourceOriginalBranchPackets.bank n word) [] [] [])

private theorem parser_program_eq (l : BitMachineBankCodec.ParserLabel 2) :
    program M (.inl l) = BitMachineStackEmbedding.stmt (parserStack M)
      Sum.inl (parserControl M) Prod.fst (some (.inr (.inl M.start)))
      (BitMachineBankCodec.parser 2 l) := rfl

theorem parse_run (n : ℕ) (word : List Bool) :
    ∃ t ≤ 5 * ((SourceOriginalBranchPackets.packet n word).length + 1),
      run M t (entry M (SourceOriginalBranchPackets.packet n word)) =
        afterParse M n word := by
  let packet := SourceOriginalBranchPackets.packet n word
  let bank := SourceOriginalBranchPackets.bank n word
  obtain ⟨t,ht,hparse⟩ := BitMachineBankCodec.parser_correct 2 packet []
  have hd : BitMachineBankCodec.decode 2 packet = some bank :=
    SourceOriginalBranchPackets.packet_decode n word
  rw [hd] at hparse
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) packet [] []) =
    BitMachineBankCodec.parserCfg none (some true) bank [] [] [] at hparse
  have hh := congrArg (fun c => c.l) hparse
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs (parserStack M)
    (fun _ => []) Sum.inl (parserControl M) Prod.fst
    (by intro v; rfl) (some (.inr (.inl M.start)))
    (BitMachineBankCodec.parser 2) (program M) (parser_program_eq M)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) packet [] []) t
    (by simpa only [BitMachineBankCodec.parserRun] using hh)
  refine ⟨u,hu.trans ht,?_⟩
  change ((advance (program M))^[u]) _ = _ at hr
  unfold BitMachineBankCodec.parserRun at hparse
  rw [hparse] at hr
  simpa only [run, entry, afterParse, packet, bank] using hr

private theorem afterParse_machine_stack (n : ℕ) (word : List Bool)
    (k : Fin M.stackCount) :
    (afterParse M n word).stk (machineStack M k) =
      if k = M.input then word else [] := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  by_cases hk : k = M.input
  · subst k
    rw [show machineStack M M.input =
      parserStack M (.inl (1 : Fin 2)) by simp [machineStack, parserStack]]
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents,
      SourceOriginalBranchPackets.bank]
  · have hout : ¬ ∃ p : BitMachineBankCodec.Stack 2,
        parserStack M p = machineStack M k := by
      rintro ⟨p,hp⟩
      cases p with
      | inl p =>
          fin_cases p
          · simp [parserStack, machineStack] at hp
          · simp [parserStack, machineStack] at hp
            exact hk hp.symm
      | inr p => simp [parserStack, machineStack] at hp
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout]
    simp [hk]

private theorem afterParse_originalN (n : ℕ) (word : List Bool) :
    (afterParse M n word).stk (.inl (0 : Fin 1)) =
      List.replicate n true := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [show (.inl (0 : Fin 1) : Stack M) =
    parserStack M (.inl (0 : Fin 2)) by simp [parserStack]]
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents,
    SourceOriginalBranchPackets.bank]

private theorem afterParse_work (n : ℕ) (word : List Bool) (j : Fin 3) :
    (afterParse M n word).stk (.inr (.inr j)) = [] := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [show (.inr (.inr j) : Stack M) =
    parserStack M (.inr j) by simp [parserStack]]
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]

private theorem machine_initial (n : ℕ) (word : List Bool) :
    afterParse M n word =
      BitMachineStackEmbedding.cfg (machineStack M) (afterParse M n word).stk
        (fun l => .inr (.inl l)) (machineControl M)
        (some (.inr (.inr (.inl ())))) (M.init word) := by
  have hb := BitMachineStackEmbedding.bank_eq_self (machineStack M)
    (afterParse M n word).stk (M.init word).stk (by
      intro k
      simpa only [BitMachine.Machine.init] using
        (afterParse_machine_stack M n word k).symm)
  change (⟨some (.inr (.inl M.start)), parserControl M (some true),
      (afterParse M n word).stk⟩ : Config M) =
    ⟨some (.inr (.inl M.start)), machineControl M M.initial,
      BitMachineStackEmbedding.bank (machineStack M) (afterParse M n word).stk
        (M.init word).stk⟩
  rw [hb]
  rfl

noncomputable def afterMachine (n : ℕ) (word : List Bool) (c : M.Config) :
    Config M :=
  BitMachineStackEmbedding.cfg (machineStack M) (afterParse M n word).stk
    (fun l => .inr (.inl l)) (machineControl M)
    (some (.inr (.inr (.inl ())))) c

private theorem machine_program_eq (l : Fin M.labelCount) :
    program M (.inr (.inl l)) = BitMachineStackEmbedding.stmt (machineStack M)
      (fun l => .inr (.inl l)) (machineControl M) (fun v => v.2.1)
      (some (.inr (.inr (.inl ())))) (M.program l) := rfl

theorem machine_run (n : ℕ) (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    ∃ (u : ℕ) (c : M.Config), u ≤ T ∧
      run M u (afterParse M n word) = afterMachine M n word c ∧
      c.l = none ∧ c.stk M.output = output := by
  obtain ⟨t,ht,hhalt,hout⟩ := h
  let c := M.run t (M.init word)
  have hh : (((advance M.program)^[t]) (M.init word)).l = none := hhalt
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (machineStack M)
    (afterParse M n word).stk (fun l => .inr (.inl l))
    (machineControl M) (fun v => v.2.1) (by intro v; rfl)
    (some (.inr (.inr (.inl ())))) M.program (program M)
    (machine_program_eq M) (M.init word) t hh
  refine ⟨u,c,hu.trans ht,?_,hhalt,hout⟩
  change ((advance (program M))^[u]) _ = _ at he
  exact (congrArg (run M u) (machine_initial M n word)).trans he

private theorem afterMachine_originalN (n : ℕ) (word : List Bool)
    (c : M.Config) :
    (afterMachine M n word c).stk (.inl (0 : Fin 1)) =
      List.replicate n true := by
  have ho : ¬ ∃ k : Fin M.stackCount,
      machineStack M k = (.inl (0 : Fin 1) : Stack M) := by
    rintro ⟨k,hk⟩
    exact Sum.inr_ne_inl hk
  change BitMachineStackEmbedding.bank (machineStack M) _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterParse_originalN M n word

private theorem afterMachine_result (n : ℕ) (word : List Bool)
    (c : M.Config) :
    (afterMachine M n word c).stk (machineStack M M.output) = c.stk M.output := by
  change BitMachineStackEmbedding.bank (machineStack M) _ _
    (machineStack M M.output) = _
  exact BitMachineStackEmbedding.bank_at _ _ _ _

private theorem afterMachine_work (n : ℕ) (word : List Bool)
    (c : M.Config) (j : Fin 3) :
    (afterMachine M n word c).stk (.inr (.inr j)) = [] := by
  have ho : ¬ ∃ k : Fin M.stackCount,
      machineStack M k = (.inr (.inr j) : Stack M) := by
    rintro ⟨k,hk⟩
    exact Sum.inl_ne_inr (Sum.inr_injective hk)
  change BitMachineStackEmbedding.bank (machineStack M) _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterParse_work M n word j

noncomputable def beginSerializer (n : ℕ) (word : List Bool)
    (c : M.Config) : Config M :=
  ⟨some (.inr (.inr (.inr (.emit 0)))), serializerControl M none,
    (afterMachine M n word c).stk⟩

theorem handoff_step (n : ℕ) (word : List Bool) (c : M.Config)
    (hc : c.l = none) :
    advance (program M) (afterMachine M n word c) =
      beginSerializer M n word c := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none =>
      simp [afterMachine, beginSerializer, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        advance, TM2.step, TM2.stepAux, program]
  | some l => cases hc

def resultBank (n : ℕ) (output : List Bool) : Fin 2 → List Bool :=
  SourceOriginalBranchPackets.bank n output

noncomputable def serializerInitial (n : ℕ) (output : List Bool) :
    TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool) :=
  BitMachineBankSerialize.cfg (some (.emit 0)) none
    (resultBank n output) [] [] []

private theorem serializer_initial (n : ℕ) (word output : List Bool)
    (c : M.Config) (hout : c.stk M.output = output) :
    beginSerializer M n word c =
      BitMachineStackEmbedding.cfg (serializerStack M)
        (afterMachine M n word c).stk
        (fun l => .inr (.inr (.inr l))) (serializerControl M) none
        (serializerInitial n output) := by
  have hb := BitMachineStackEmbedding.bank_eq_self (serializerStack M)
    (afterMachine M n word c).stk (serializerInitial n output).stk (by
      intro k
      cases k with
      | inl k =>
          fin_cases k
          · simp [serializerInitial, BitMachineBankSerialize.cfg,
              BitMachineBankSerialize.contents, resultBank,
              SourceOriginalBranchPackets.bank, serializerStack,
              afterMachine_originalN M n word c]
          · simp [serializerInitial, BitMachineBankSerialize.cfg,
              BitMachineBankSerialize.contents, resultBank,
              SourceOriginalBranchPackets.bank, serializerStack,
              ]
            exact ((afterMachine_result M n word c).trans hout).symm
      | inr k =>
          simp [serializerInitial, BitMachineBankSerialize.cfg,
            BitMachineBankSerialize.contents, serializerStack,
            afterMachine_work M n word c k])
  change (⟨some (.inr (.inr (.inr (.emit 0)))), serializerControl M none,
      (afterMachine M n word c).stk⟩ : Config M) =
    ⟨some (.inr (.inr (.inr (.emit 0)))), serializerControl M none,
      BitMachineStackEmbedding.bank (serializerStack M)
        (afterMachine M n word c).stk (serializerInitial n output).stk⟩
  rw [hb]

noncomputable def afterSerialize (n : ℕ) (word output : List Bool)
    (c : M.Config) (S' : BitMachineBankSerialize.Bank 2) : Config M :=
  BitMachineStackEmbedding.cfg (serializerStack M)
    (afterMachine M n word c).stk
    (fun l => .inr (.inr (.inr l))) (serializerControl M) none
    (BitMachineBankSerialize.cfg none none S' [] []
      (SourceOriginalBranchPackets.packet n output))

private theorem serializer_program_eq (l : BitMachineBankSerialize.Label 2) :
    program M (.inr (.inr (.inr l))) =
      BitMachineStackEmbedding.stmt (serializerStack M)
        (fun l => .inr (.inr (.inr l))) (serializerControl M)
        (fun v => v.2.2) none (BitMachineBankSerialize.program 2 l) := rfl

theorem serialize_run (n : ℕ) (word output : List Bool)
    (c : M.Config) (hout : c.stk M.output = output) :
    ∃ (u : ℕ) (S' : BitMachineBankSerialize.Bank 2),
      u ≤ 2 * (SourceOriginalBranchPackets.packet n output).length + 2 ∧
      run M u (beginSerializer M n word c) =
        afterSerialize M n word output c S' := by
  let S := resultBank n output
  have hpacket : BitMachineBankSerialize.encode (List.ofFn S) =
      SourceOriginalBranchPackets.packet n output := by
    rw [SourceOriginalBranchPackets.packet, BitMachineBankCodec.encode_eq_list]
    rfl
  obtain ⟨t,S',ht,hr⟩ := BitMachineBankSerialize.serialize S [] []
  rw [hpacket] at ht hr
  have hh : (BitMachineBankSerialize.run t (serializerInitial n output)).l = none := by
    change (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none S [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (serializerStack M)
    (afterMachine M n word c).stk (fun l => .inr (.inr (.inr l)))
    (serializerControl M) (fun v => v.2.2) (by intro v; rfl) none
    (BitMachineBankSerialize.program 2) (program M) (serializer_program_eq M)
    (serializerInitial n output) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u,S',hu.trans ht,?_⟩
  change ((advance (program M))^[u]) _ = _ at he
  unfold BitMachineBankSerialize.run at hr
  have hr' : ((advance (BitMachineBankSerialize.program 2))^[t])
      (serializerInitial n output) =
      BitMachineBankSerialize.cfg none none S' [] []
        (SourceOriginalBranchPackets.packet n output) := by
    simpa only [serializerInitial, List.append_nil] using hr
  rw [hr'] at he
  exact (congrArg (run M u) (serializer_initial M n word output c hout)).trans he

theorem final_packet (n : ℕ) (word output : List Bool)
    (c : M.Config) (S' : BitMachineBankSerialize.Bank 2) :
    (afterSerialize M n word output c S').stk (.inr (.inr (2 : Fin 3))) =
      SourceOriginalBranchPackets.packet n output := by
  change BitMachineStackEmbedding.bank (serializerStack M) _ _
    (serializerStack M (.inr (2 : Fin 3))) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem run_add {c d : Config M} {t : ℕ}
    (h : run M t c = d) (u : ℕ) :
    run M (t + u) c = run M u d := by
  simp only [run] at h ⊢
  rw [show t + u = u + t by omega, Function.iterate_add_apply, h]

theorem canonical_packet_run (n : ℕ) (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    ∃ u ≤ 5 * ((SourceOriginalBranchPackets.packet n word).length + 1) +
      T + 1 + 2 * (SourceOriginalBranchPackets.packet n output).length + 2,
      (run M u (entry M (SourceOriginalBranchPackets.packet n word))).l = none ∧
      (run M u (entry M (SourceOriginalBranchPackets.packet n word))).stk
        (.inr (.inr (2 : Fin 3))) =
          SourceOriginalBranchPackets.packet n output := by
  obtain ⟨p,hp,hparse⟩ := parse_run M n word
  obtain ⟨q,c,hq,hmachine,hhalt,hout⟩ := machine_run M n word output T h
  obtain ⟨r,S',hr,hserialize⟩ := serialize_run M n word output c hout
  have hpart : run M (p + q)
      (entry M (SourceOriginalBranchPackets.packet n word)) =
      afterMachine M n word c := (run_add M hparse q).trans hmachine
  have hbegin : run M (p + q + 1)
      (entry M (SourceOriginalBranchPackets.packet n word)) =
      beginSerializer M n word c := by
    rw [run_add M hpart 1]
    exact handoff_step M n word c hhalt
  have hfull : run M (p + q + 1 + r)
      (entry M (SourceOriginalBranchPackets.packet n word)) =
      afterSerialize M n word output c S' :=
    (run_add M hbegin r).trans hserialize
  refine ⟨p + q + 1 + r, by omega, ?_, ?_⟩
  · rw [hfull]
    rfl
  · rw [hfull]
    exact final_packet M n word output c S'

end EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCore
