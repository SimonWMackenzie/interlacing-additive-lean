import CurrentAdditive.V40LawPacket
import EthInapproximability.CurrentPaper.SourceOriginalPacketLiftCore

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
namespace CurrentAdditive.V40LawBankCore
open Turing
open EthInapproximability.CurrentPaper BitMachineEncoding
variable (M : BitMachine.Machine)
abbrev Stack := SourceOriginalPacketLiftCore.Stack M
abbrev Label := SourceOriginalPacketLiftCore.Label M
abbrev Control := SourceOriginalPacketLiftCore.Control M
abbrev Config := SourceOriginalPacketLiftCore.Config M
abbrev parserStack := SourceOriginalPacketLiftCore.parserStack M
abbrev machineStack := SourceOriginalPacketLiftCore.machineStack M
abbrev serializerStack := SourceOriginalPacketLiftCore.serializerStack M
abbrev parserControl := SourceOriginalPacketLiftCore.parserControl M
abbrev machineControl := SourceOriginalPacketLiftCore.machineControl M
abbrev serializerControl := SourceOriginalPacketLiftCore.serializerControl M
abbrev program := SourceOriginalPacketLiftCore.program M
def run (t : ℕ) (c : Config M) : Config M := ((advance (program M))^[t]) c
noncomputable abbrev entry := SourceOriginalPacketLiftCore.entry M
attribute [local simp] SourceOriginalPacketLiftCore.parserStack
  SourceOriginalPacketLiftCore.machineStack SourceOriginalPacketLiftCore.serializerStack

noncomputable def afterParse (header : List Bool) (word : List Bool) : Config M :=
  BitMachineStackEmbedding.cfg (parserStack M) (fun _ => []) Sum.inl
    (parserControl M) (some (.inr (.inl M.start)))
    (BitMachineBankCodec.parserCfg none (some true)
      (CurrentAdditive.V40LawPacket.bank header word) [] [] [])

private theorem parser_program_eq (l : BitMachineBankCodec.ParserLabel 2) :
    program M (.inl l) = BitMachineStackEmbedding.stmt (parserStack M)
      Sum.inl (parserControl M) Prod.fst (some (.inr (.inl M.start)))
      (BitMachineBankCodec.parser 2 l) := rfl

theorem parse_run (header : List Bool) (word : List Bool) :
    ∃ t ≤ 5 * ((CurrentAdditive.V40LawPacket.packet header word).length + 1),
      run M t (entry M (CurrentAdditive.V40LawPacket.packet header word)) =
        afterParse M header word := by
  let packet := CurrentAdditive.V40LawPacket.packet header word
  let bank := CurrentAdditive.V40LawPacket.bank header word
  obtain ⟨t,ht,hparse⟩ := BitMachineBankCodec.parser_correct 2 packet []
  have hd : BitMachineBankCodec.decode 2 packet = some bank :=
    CurrentAdditive.V40LawPacket.packet_decode header word
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

private theorem afterParse_machine_stack (header : List Bool) (word : List Bool)
    (k : Fin M.stackCount) :
    (afterParse M header word).stk (machineStack M k) =
      if k = M.input then word else [] := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  by_cases hk : k = M.input
  · subst k
    rw [show machineStack M M.input =
      parserStack M (.inl (1 : Fin 2)) by simp [machineStack, parserStack]]
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents,
      CurrentAdditive.V40LawPacket.bank]
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

private theorem afterParse_originalN (header : List Bool) (word : List Bool) :
    (afterParse M header word).stk (.inl (0 : Fin 1)) =
      header := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [show (.inl (0 : Fin 1) : Stack M) =
    parserStack M (.inl (0 : Fin 2)) by simp [parserStack]]
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents,
    CurrentAdditive.V40LawPacket.bank]

private theorem afterParse_work (header : List Bool) (word : List Bool) (j : Fin 3) :
    (afterParse M header word).stk (.inr (.inr j)) = [] := by
  dsimp only [afterParse, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [show (.inr (.inr j) : Stack M) =
    parserStack M (.inr j) by simp [parserStack]]
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachineBankCodec.parserCfg, BitMachineBankCodec.contents]

private theorem machine_initial (header : List Bool) (word : List Bool) :
    afterParse M header word =
      BitMachineStackEmbedding.cfg (machineStack M) (afterParse M header word).stk
        (fun l => .inr (.inl l)) (machineControl M)
        (some (.inr (.inr (.inl ())))) (M.init word) := by
  have hb := BitMachineStackEmbedding.bank_eq_self (machineStack M)
    (afterParse M header word).stk (M.init word).stk (by
      intro k
      simpa only [BitMachine.Machine.init] using
        (afterParse_machine_stack M header word k).symm)
  change (⟨some (.inr (.inl M.start)), parserControl M (some true),
      (afterParse M header word).stk⟩ : Config M) =
    ⟨some (.inr (.inl M.start)), machineControl M M.initial,
      BitMachineStackEmbedding.bank (machineStack M) (afterParse M header word).stk
        (M.init word).stk⟩
  rw [hb]
  rfl

noncomputable def afterMachine (header : List Bool) (word : List Bool) (c : M.Config) :
    Config M :=
  BitMachineStackEmbedding.cfg (machineStack M) (afterParse M header word).stk
    (fun l => .inr (.inl l)) (machineControl M)
    (some (.inr (.inr (.inl ())))) c

private theorem machine_program_eq (l : Fin M.labelCount) :
    program M (.inr (.inl l)) = BitMachineStackEmbedding.stmt (machineStack M)
      (fun l => .inr (.inl l)) (machineControl M) (fun v => v.2.1)
      (some (.inr (.inr (.inl ())))) (M.program l) := rfl

theorem machine_run (header : List Bool) (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    ∃ (u : ℕ) (c : M.Config), u ≤ T ∧
      run M u (afterParse M header word) = afterMachine M header word c ∧
      c.l = none ∧ c.stk M.output = output := by
  obtain ⟨t,ht,hhalt,hout⟩ := h
  let c := M.run t (M.init word)
  have hh : (((advance M.program)^[t]) (M.init word)).l = none := hhalt
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (machineStack M)
    (afterParse M header word).stk (fun l => .inr (.inl l))
    (machineControl M) (fun v => v.2.1) (by intro v; rfl)
    (some (.inr (.inr (.inl ())))) M.program (program M)
    (machine_program_eq M) (M.init word) t hh
  refine ⟨u,c,hu.trans ht,?_,hhalt,hout⟩
  change ((advance (program M))^[u]) _ = _ at he
  exact (congrArg (run M u) (machine_initial M header word)).trans he

private theorem afterMachine_originalN (header : List Bool) (word : List Bool)
    (c : M.Config) :
    (afterMachine M header word c).stk (.inl (0 : Fin 1)) =
      header := by
  have ho : ¬ ∃ k : Fin M.stackCount,
      machineStack M k = (.inl (0 : Fin 1) : Stack M) := by
    rintro ⟨k,hk⟩
    exact Sum.inr_ne_inl hk
  change BitMachineStackEmbedding.bank (machineStack M) _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterParse_originalN M header word

private theorem afterMachine_result (header : List Bool) (word : List Bool)
    (c : M.Config) :
    (afterMachine M header word c).stk (machineStack M M.output) = c.stk M.output := by
  change BitMachineStackEmbedding.bank (machineStack M) _ _
    (machineStack M M.output) = _
  exact BitMachineStackEmbedding.bank_at _ _ _ _

private theorem afterMachine_work (header : List Bool) (word : List Bool)
    (c : M.Config) (j : Fin 3) :
    (afterMachine M header word c).stk (.inr (.inr j)) = [] := by
  have ho : ¬ ∃ k : Fin M.stackCount,
      machineStack M k = (.inr (.inr j) : Stack M) := by
    rintro ⟨k,hk⟩
    exact Sum.inl_ne_inr (Sum.inr_injective hk)
  change BitMachineStackEmbedding.bank (machineStack M) _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  exact afterParse_work M header word j

noncomputable def beginSerializer (header : List Bool) (word : List Bool)
    (c : M.Config) : Config M :=
  ⟨some (.inr (.inr (.inr (.emit 0)))), serializerControl M none,
    (afterMachine M header word c).stk⟩

theorem handoff_step (header : List Bool) (word : List Bool) (c : M.Config)
    (hc : c.l = none) :
    advance (program M) (afterMachine M header word c) =
      beginSerializer M header word c := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none =>
      simp [afterMachine, beginSerializer, BitMachineStackEmbedding.cfg,
        BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
        advance, TM2.step, TM2.stepAux, program,SourceOriginalPacketLiftCore.program]
  | some l => cases hc

def resultBank (header : List Bool) (output : List Bool) : Fin 2 → List Bool :=
  CurrentAdditive.V40LawPacket.bank header output

noncomputable def serializerInitial (header : List Bool) (output : List Bool) :
    TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool) :=
  BitMachineBankSerialize.cfg (some (.emit 0)) none
    (resultBank header output) [] [] []

private theorem serializer_initial (header : List Bool) (word output : List Bool)
    (c : M.Config) (hout : c.stk M.output = output) :
    beginSerializer M header word c =
      BitMachineStackEmbedding.cfg (serializerStack M)
        (afterMachine M header word c).stk
        (fun l => .inr (.inr (.inr l))) (serializerControl M) none
        (serializerInitial header output) := by
  have hb := BitMachineStackEmbedding.bank_eq_self (serializerStack M)
    (afterMachine M header word c).stk (serializerInitial header output).stk (by
      intro k
      cases k with
      | inl k =>
          fin_cases k
          · simp [serializerInitial, BitMachineBankSerialize.cfg,
              BitMachineBankSerialize.contents, resultBank,
              CurrentAdditive.V40LawPacket.bank, serializerStack,
              afterMachine_originalN M header word c]
          · simp [serializerInitial, BitMachineBankSerialize.cfg,
              BitMachineBankSerialize.contents, resultBank,
              CurrentAdditive.V40LawPacket.bank, serializerStack,
              ]
            exact ((afterMachine_result M header word c).trans hout).symm
      | inr k =>
          simp [serializerInitial, BitMachineBankSerialize.cfg,
            BitMachineBankSerialize.contents, serializerStack,
            afterMachine_work M header word c k])
  change (⟨some (.inr (.inr (.inr (.emit 0)))), serializerControl M none,
      (afterMachine M header word c).stk⟩ : Config M) =
    ⟨some (.inr (.inr (.inr (.emit 0)))), serializerControl M none,
      BitMachineStackEmbedding.bank (serializerStack M)
        (afterMachine M header word c).stk (serializerInitial header output).stk⟩
  rw [hb]

noncomputable def afterSerialize (header : List Bool) (word output : List Bool)
    (c : M.Config) (S' : BitMachineBankSerialize.Bank 2) : Config M :=
  BitMachineStackEmbedding.cfg (serializerStack M)
    (afterMachine M header word c).stk
    (fun l => .inr (.inr (.inr l))) (serializerControl M) none
    (BitMachineBankSerialize.cfg none none S' [] []
      (CurrentAdditive.V40LawPacket.packet header output))

private theorem serializer_program_eq (l : BitMachineBankSerialize.Label 2) :
    program M (.inr (.inr (.inr l))) =
      BitMachineStackEmbedding.stmt (serializerStack M)
        (fun l => .inr (.inr (.inr l))) (serializerControl M)
        (fun v => v.2.2) none (BitMachineBankSerialize.program 2 l) := rfl

theorem serialize_run (header : List Bool) (word output : List Bool)
    (c : M.Config) (hout : c.stk M.output = output) :
    ∃ (u : ℕ) (S' : BitMachineBankSerialize.Bank 2),
      u ≤ 2 * (CurrentAdditive.V40LawPacket.packet header output).length + 2 ∧
      run M u (beginSerializer M header word c) =
        afterSerialize M header word output c S' := by
  let S := resultBank header output
  have hpacket : BitMachineBankSerialize.encode (List.ofFn S) =
      CurrentAdditive.V40LawPacket.packet header output := by
    rw [CurrentAdditive.V40LawPacket.packet, BitMachineBankCodec.encode_eq_list]
    rfl
  obtain ⟨t,S',ht,hr⟩ := BitMachineBankSerialize.serialize S [] []
  rw [hpacket] at ht hr
  have hh : (BitMachineBankSerialize.run t (serializerInitial header output)).l = none := by
    change (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none S [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs (serializerStack M)
    (afterMachine M header word c).stk (fun l => .inr (.inr (.inr l)))
    (serializerControl M) (fun v => v.2.2) (by intro v; rfl) none
    (BitMachineBankSerialize.program 2) (program M) (serializer_program_eq M)
    (serializerInitial header output) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u,S',hu.trans ht,?_⟩
  change ((advance (program M))^[u]) _ = _ at he
  unfold BitMachineBankSerialize.run at hr
  have hr' : ((advance (BitMachineBankSerialize.program 2))^[t])
      (serializerInitial header output) =
      BitMachineBankSerialize.cfg none none S' [] []
        (CurrentAdditive.V40LawPacket.packet header output) := by
    simpa only [serializerInitial, List.append_nil] using hr
  rw [hr'] at he
  exact (congrArg (run M u) (serializer_initial M header word output c hout)).trans he

theorem final_packet (header : List Bool) (word output : List Bool)
    (c : M.Config) (S' : BitMachineBankSerialize.Bank 2) :
    (afterSerialize M header word output c S').stk (.inr (.inr (2 : Fin 3))) =
      CurrentAdditive.V40LawPacket.packet header output := by
  change BitMachineStackEmbedding.bank (serializerStack M) _ _
    (serializerStack M (.inr (2 : Fin 3))) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem run_add {c d : Config M} {t : ℕ}
    (h : run M t c = d) (u : ℕ) :
    run M (t + u) c = run M u d := by
  simp only [run] at h ⊢
  rw [show t + u = u + t by omega, Function.iterate_add_apply, h]

theorem canonical_packet_run (header : List Bool) (word output : List Bool) (T : ℕ)
    (h : M.OutputsWithin word output T) :
    ∃ u ≤ 5 * ((CurrentAdditive.V40LawPacket.packet header word).length + 1) +
      T + 1 + 2 * (CurrentAdditive.V40LawPacket.packet header output).length + 2,
      (run M u (entry M (CurrentAdditive.V40LawPacket.packet header word))).l = none ∧
      (run M u (entry M (CurrentAdditive.V40LawPacket.packet header word))).stk
        (.inr (.inr (2 : Fin 3))) =
          CurrentAdditive.V40LawPacket.packet header output := by
  obtain ⟨p,hp,hparse⟩ := parse_run M header word
  obtain ⟨q,c,hq,hmachine,hhalt,hout⟩ := machine_run M header word output T h
  obtain ⟨r,S',hr,hserialize⟩ := serialize_run M header word output c hout
  have hpart : run M (p + q)
      (entry M (CurrentAdditive.V40LawPacket.packet header word)) =
      afterMachine M header word c := (run_add M hparse q).trans hmachine
  have hbegin : run M (p + q + 1)
      (entry M (CurrentAdditive.V40LawPacket.packet header word)) =
      beginSerializer M header word c := by
    rw [run_add M hpart 1]
    exact handoff_step M header word c hhalt
  have hfull : run M (p + q + 1 + r)
      (entry M (CurrentAdditive.V40LawPacket.packet header word)) =
      afterSerialize M header word output c S' :=
    (run_add M hbegin r).trans hserialize
  refine ⟨p + q + 1 + r, by omega, ?_, ?_⟩
  · rw [hfull]
    rfl
  · rw [hfull]
    exact final_packet M header word output c S'

end CurrentAdditive.V40LawBankCore
