import CurrentAdditive.RationalSubtractDenReverse
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Physical selection of three RawRat fields from a packed 32-bank result. -/

namespace EthInapproximability.CurrentPaper.RationalSubtractSelect3

open Turing TM2.Stmt BitMachineEncoding

abbrev Stack := BitMachineBankCodec.Stack 32
abbrev Bank := BitMachineBankCodec.Bank 32
abbrev Label := BitMachineBankCodec.ParserLabel 32 ⊕
  (BitMachineBankSerialize.Label 3 ⊕ Unit)
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def serIndex : Fin 3 → Fin 32 := ![30,31,11]
def selected (S : Bank) : BitMachineBankSerialize.Bank 3 :=
  fun i => S (serIndex i)

def serSlots : BitMachineBankSerialize.Stack 3 ↪ Stack where
  toFun
    | .inl i => .inl (serIndex i)
    | .inr j => .inr j
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            fin_cases x <;> fin_cases y <;> simp_all [serIndex]
        | inr y => cases h
    | inr x =>
        cases y with
        | inl y => cases h
        | inr y => simpa using h

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl id id
      (some (.inr (.inr ()))) (BitMachineBankCodec.parser 32 l)
  | .inr (.inr ()) => branch (fun v => v.getD false)
      (load (fun _ => none) (goto (fun _ => .inr (.inl (.emit 0))))) halt
  | .inr (.inl l) => BitMachineStackEmbedding.stmt serSlots
      (fun l => .inr (.inl l)) id id none (BitMachineBankSerialize.program 3 l)

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) : Config :=
  ⟨l, v, BitMachineBankCodec.contents S source saved output⟩

def run (n : Nat) (c : Config) : Config :=
  ((advance program)^[n]) c

theorem run_add (t u : Nat) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

theorem parse_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 32 input = some S) :
    ∃ t ≤ 65*(input.length+1),
      run t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        cfg (some (.inr (.inr ()))) (some true) S [] [] [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 32 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 32 → Label)
    id id (fun _ => rfl) (some (.inr (.inr ())))
    (BitMachineBankCodec.parser 32) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem admin_step (S : Bank) :
    advance program (cfg (some (.inr (.inr ()))) (some true) S [] [] []) =
      cfg (some (.inr (.inl (.emit 0)))) none S [] [] [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem ser_start (S : Bank) :
    cfg (some (.inr (.inl (.emit 0)))) none S [] [] [] =
      BitMachineStackEmbedding.cfg serSlots
        (cfg (some (.inr (.inl (.emit 0)))) none S [] [] []).stk
        (fun l => .inr (.inl l)) id none
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (selected S) [] [] []) := by
  unfold cfg BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply (BitMachineStackEmbedding.bank_eq_self serSlots
    (cfg (some (.inr (.inl (.emit 0)))) none S [] [] []).stk
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected S) [] [] []).stk) ?_ |>.symm
  intro k
  cases k with
  | inl k =>
      fin_cases k <;> simp [serSlots, serIndex, selected, cfg,
        BitMachineBankCodec.contents, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents]
  | inr k =>
      fin_cases k <;> simp [serSlots, cfg,
        BitMachineBankCodec.contents, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents]

theorem serialize_run (S : Bank) :
    ∃ t ≤ 2*(BitMachineBankSerialize.encode (List.ofFn (selected S))).length+2,
      let c := run t (cfg (some (.inr (.inl (.emit 0)))) none S [] [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected S)) := by
  obtain ⟨t,T,ht,hs⟩ := BitMachineBankSerialize.serialize (selected S) [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs serSlots
    (cfg (some (.inr (.inl (.emit 0)))) none S [] [] []).stk
    (fun l => .inr (.inl l)) id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 3) program (fun _ => rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected S) [] [] []) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u, hu.trans ht, ?_⟩
  change _ ∧ _
  rw [← ser_start S] at hr
  change run u _ = _ at hr
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  constructor
  · exact congrArg (fun c => c.l) hr
  · have ho := congrArg (fun c => c.stk (.inr 2)) hr
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at ho
    rw [← show serSlots (.inr 2) = (.inr 2 : Stack) by rfl,
      BitMachineStackEmbedding.bank_at] at ho
    simpa [BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents] using ho

theorem output_length (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 32 input = some S) :
    (BitMachineBankSerialize.encode (List.ofFn (selected S))).length ≤
      6*input.length+3 := by
  rw [BitMachineBankSerialize.encode,
    ← BitMachineBankCodec.encode_eq_list,
    BitMachineBankCodec.encode_length]
  have h0 := BitMachineBankCodec.decoded_word_length hd (30 : Fin 32)
  have h1 := BitMachineBankCodec.decoded_word_length hd (31 : Fin 32)
  have h2 := BitMachineBankCodec.decoded_word_length hd (11 : Fin 32)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change 2*((S 30).length + ((S 31).length + (S 11).length)) + 3 ≤
    6*input.length+3
  omega

theorem valid_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 32 input = some S) :
    ∃ t ≤ 80*(input.length+1),
      let c := run t
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected S)) := by
  obtain ⟨t,ht,hp⟩ := parse_run input S hd
  obtain ⟨u,hu,hs⟩ := serialize_run S
  refine ⟨t+1+u, ?_, ?_⟩
  · have hl := output_length input S hd
    omega
  · rw [run_add (t+1) u, run_add t 1, hp]
    change (run u
      (advance program
        (cfg (some (.inr (.inr ()))) (some true) S [] [] []))).l = none ∧ _
    rw [admin_step]
    exact hs

theorem reject_run (input : List Bool)
    (hd : BitMachineBankCodec.decode 32 input = none) :
    ∃ t ≤ 65*(input.length+1)+1,
      let c := run t
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 32 input []
  rw [hd] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 32 => Bool)
      (BitMachineBankCodec.ParserLabel 32) Control :=
    BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 32 → Label)
    id id (fun _ => rfl) (some (.inr (.inr ())))
    (BitMachineBankCodec.parser 32) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hp.1
  refine ⟨u+1, by omega, ?_⟩
  have hr' : run u
      (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
      BitMachineInline.cfg Sum.inl id (some (.inr (.inr ()))) c := hr
  change _ ∧ _
  rw [run_add u 1, hr']
  simp only [run, Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, program, BitMachineInline.cfg,
    hp.1, hp.2.1, hp.2.2]

def result (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 32 input with
  | none => []
  | some S => BitMachineBankSerialize.encode (List.ofFn (selected S))

@[simp] theorem result_encode (S : Bank) :
    result (BitMachineBankCodec.encode S) =
      BitMachineBankCodec.encode (selected S) := by
  rw [result, BitMachineBankCodec.decode_encode,
    BitMachineBankCodec.encode_eq_list]
  rfl

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack) (.inr 2) (.inl (.scan 0)) none program

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label) none input =
      cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [] := by
  unfold rawInit cfg BitMachineBankCodec.contents
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => fin_cases k <;> rfl

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (80*(input.length+1)) := by
  cases hd : BitMachineBankCodec.decode 32 input with
  | none =>
      obtain ⟨t,ht,hh,ho⟩ := reject_run input hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none program input
        (result input) t _ (by omega)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some S =>
      obtain ⟨t,ht,hh,ho⟩ := valid_run input S hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none program input
        (result input) t _ ht
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 80, 1, ?_⟩
  intro input
  simpa only [pow_one] using outputs input

end EthInapproximability.CurrentPaper.RationalSubtractSelect3
