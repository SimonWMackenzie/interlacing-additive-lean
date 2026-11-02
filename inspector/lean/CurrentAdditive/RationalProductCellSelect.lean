import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
Physical extraction of two encoded RawRat words from a Gauss cell packet.
The outer twelve-field parser and two-field serializer are both literal finite
programs. This module does not yet parse the two nested RawRat words.
-/

namespace EthInapproximability.CurrentPaper.RationalProductCellSelect

open Turing TM2.Stmt BitMachineEncoding
open BitMachineBankCodec

abbrev Stack := BitMachineBankCodec.Stack 12
abbrev Bank := BitMachineBankCodec.Bank 12
abbrev Label := BitMachineBankCodec.ParserLabel 12 ⊕
  (BitMachineBankSerialize.Label 2 ⊕ Unit)
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def selected (a b : Fin 12) (S : Bank) : BitMachineBankSerialize.Bank 2 :=
  fun i => if i = 0 then S a else S b

def serSlots (a b : Fin 12) (hab : a ≠ b) :
    BitMachineBankSerialize.Stack 2 ↪ Stack where
  toFun
    | .inl i => .inl (if i = 0 then a else b)
    | .inr j => .inr j
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            fin_cases x <;> fin_cases y <;> simp [hab, Ne.symm hab] at h ⊢
        | inr y => simp at h
    | inr x =>
        cases y with
        | inl y => simp at h
        | inr y => simpa using h

def program (a b : Fin 12) (hab : a ≠ b) : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl id id
      (some (.inr (.inr ()))) (BitMachineBankCodec.parser 12 l)
  | .inr (.inr ()) => branch (fun v => v.getD false)
      (load (fun _ => none) (goto (fun _ => .inr (.inl (.emit 0))))) halt
  | .inr (.inl l) => BitMachineStackEmbedding.stmt (serSlots a b hab)
      (fun l => .inr (.inl l)) id id none (BitMachineBankSerialize.program 2 l)

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) : Config :=
  ⟨l, v, BitMachineBankCodec.contents S source saved output⟩

def run (a b : Fin 12) (hab : a ≠ b) (n : Nat) (c : Config) : Config :=
  ((advance (program a b hab))^[n]) c

theorem run_add (a b : Fin 12) (hab : a ≠ b) (t u : Nat) (c : Config) :
    run a b hab (t+u) c = run a b hab u (run a b hab t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program a b hab)) u t c

theorem parse_run (a b : Fin 12) (hab : a ≠ b)
    (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    ∃ t ≤ 25*(input.length+1),
      run a b hab t (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
        cfg (some (.inr (.inr ()))) (some true) S [] [] [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 12 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label)
    id id (fun _ => rfl) (some (.inr (.inr ())))
    (BitMachineBankCodec.parser 12) (program a b hab) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem admin_step (a b : Fin 12) (hab : a ≠ b) (S : Bank) :
    advance (program a b hab)
      (cfg (some (.inr (.inr ()))) (some true) S [] [] []) =
    cfg (some (.inr (.inl (.emit 0)))) none S [] [] [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem ser_start (a b : Fin 12) (hab : a ≠ b) (S : Bank) :
    cfg (some (.inr (.inl (.emit 0)))) none S [] [] [] =
      BitMachineStackEmbedding.cfg (serSlots a b hab)
        (cfg (some (.inr (.inl (.emit 0)))) none S [] [] []).stk
        (fun l => .inr (.inl l)) id none
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (selected a b S) [] [] []) := by
  unfold cfg BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply (BitMachineStackEmbedding.bank_eq_self (serSlots a b hab)
    (cfg (some (.inr (.inl (.emit 0)))) none S [] [] []).stk
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected a b S) [] [] []).stk) ?_ |>.symm
  intro k
  cases k with
  | inl k =>
      fin_cases k <;> simp [serSlots, selected, cfg,
        BitMachineBankCodec.contents, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents]
  | inr k =>
      fin_cases k <;> simp [serSlots, cfg,
        BitMachineBankCodec.contents, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents]

private theorem ser_program_eq (a b : Fin 12) (hab : a ≠ b)
    (l : BitMachineBankSerialize.Label 2) :
    program a b hab (.inr (.inl l)) =
      BitMachineStackEmbedding.stmt (serSlots a b hab)
        (fun l => .inr (.inl l)) id id none
        (BitMachineBankSerialize.program 2 l) := rfl

theorem serialize_run (a b : Fin 12) (hab : a ≠ b) (S : Bank) :
    ∃ t ≤ 2*(BitMachineBankSerialize.encode (List.ofFn (selected a b S))).length+2,
      let c := run a b hab t
        (cfg (some (.inr (.inl (.emit 0)))) none S [] [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected a b S)) ∧
      ∀ j : Fin 12, j ≠ a → j ≠ b → c.stk (.inl j) = S j := by
  obtain ⟨t,T,ht,hs⟩ := BitMachineBankSerialize.serialize (selected a b S) [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs
    (serSlots a b hab)
    (cfg (some (.inr (.inl (.emit 0)))) none S [] [] []).stk
    (fun l => .inr (.inl l)) id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 2) (program a b hab)
    (ser_program_eq a b hab)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected a b S) [] [] []) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u, hu.trans ht, ?_⟩
  change _ ∧ _
  rw [← ser_start a b hab S] at hr
  change run a b hab u _ = _ at hr
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  constructor
  · exact congrArg (fun c => c.l) hr
  constructor
  · have ho := congrArg (fun c => c.stk (.inr 2)) hr
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at ho
    rw [← show (serSlots a b hab) (.inr 2) = (.inr 2 : Stack) by rfl,
      BitMachineStackEmbedding.bank_at] at ho
    simpa [BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents] using ho
  · intro j hja hjb
    have hout : ¬ ∃ k : BitMachineBankSerialize.Stack 2,
        serSlots a b hab k = (.inl j : Stack) := by
      rintro ⟨k,hk⟩
      cases k with
      | inl k =>
          fin_cases k
          · exact hja (Sum.inl.inj hk).symm
          · exact hjb (Sum.inl.inj hk).symm
      | inr k => cases hk
    have hj := congrArg (fun c => c.stk (.inl j)) hr
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg] at hj
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout] at hj
    exact hj

theorem output_length (a b : Fin 12) (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    (BitMachineBankSerialize.encode (List.ofFn (selected a b S))).length ≤
      4*input.length+2 := by
  rw [BitMachineBankSerialize.encode,
    ← BitMachineBankCodec.encode_eq_list]
  rw [BitMachineBankCodec.encode_length]
  have ha := BitMachineBankCodec.decoded_word_length hd a
  have hb := BitMachineBankCodec.decoded_word_length hd b
  simp only [Fin.sum_univ_two, selected]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h10, ↓reduceIte]
  omega

theorem valid_run (a b : Fin 12) (hab : a ≠ b)
    (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 12 input = some S) :
    ∃ t ≤ 35*(input.length+1),
      let c := run a b hab t
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (selected a b S)) ∧
      ∀ j : Fin 12, j ≠ a → j ≠ b → c.stk (.inl j) = S j := by
  obtain ⟨t,ht,hp⟩ := parse_run a b hab input S hd
  obtain ⟨u,hu,hs⟩ := serialize_run a b hab S
  refine ⟨t+1+u, ?_, ?_⟩
  · have hl := output_length a b input S hd
    omega
  · rw [run_add a b hab (t+1) u, run_add a b hab t 1, hp]
    change (run a b hab u
      (advance (program a b hab)
        (cfg (some (.inr (.inr ()))) (some true) S [] [] []))).l = none ∧ _
    rw [admin_step]
    exact hs

theorem reject_run (a b : Fin 12) (hab : a ≠ b)
    (input : List Bool) (hd : BitMachineBankCodec.decode 12 input = none) :
    ∃ t ≤ 25*(input.length+1)+1,
      let c := run a b hab t
        (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct 12 input []
  rw [hd] at hp
  change (BitMachineBankCodec.parserRun t _).l = none ∧
    (BitMachineBankCodec.parserRun t _).var = some false ∧
    (BitMachineBankCodec.parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 12 => Bool)
      (BitMachineBankCodec.ParserLabel 12) Control :=
    BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 12 → Label)
    id id (fun _ => rfl) (some (.inr (.inr ())))
    (BitMachineBankCodec.parser 12) (program a b hab) (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hp.1
  refine ⟨u+1, by omega, ?_⟩
  have hr' : run a b hab u
      (cfg (some (.inl (.scan 0))) none (fun _ => []) input [] []) =
      BitMachineInline.cfg Sum.inl id (some (.inr (.inr ()))) c := hr
  change _ ∧ _
  rw [run_add a b hab u 1, hr']
  simp only [run, Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, program, BitMachineInline.cfg,
    hp.1, hp.2.1, hp.2.2]

def result (a b : Fin 12) (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 12 input with
  | none => []
  | some S => BitMachineBankSerialize.encode (List.ofFn (selected a b S))

@[simp] theorem result_encode (a b : Fin 12) (S : Bank) :
    result a b (BitMachineBankCodec.encode S) =
      BitMachineBankCodec.encode (selected a b S) := by
  rw [result, BitMachineBankCodec.decode_encode,
    BitMachineBankCodec.encode_eq_list]
  rfl

theorem selected_three_four (S : Bank) :
    selected 3 4 S = fun i => if i = 0 then S 3 else S 4 := rfl

theorem selected_two_four (S : Bank) :
    selected 2 4 S = fun i => if i = 0 then S 2 else S 4 := rfl

noncomputable def machine (a b : Fin 12) (hab : a ≠ b) : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack) (.inr 2) (.inl (.scan 0)) none (program a b hab)

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label) none input =
      cfg (some (.inl (.scan 0))) none (fun _ => []) input [] [] := by
  unfold rawInit cfg BitMachineBankCodec.contents
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => fin_cases k <;> rfl

theorem outputs (a b : Fin 12) (hab : a ≠ b) (input : List Bool) :
    (machine a b hab).OutputsWithin input (result a b input)
      (35*(input.length+1)) := by
  cases hd : BitMachineBankCodec.decode 12 input with
  | none =>
      obtain ⟨t,ht,hh,ho⟩ := reject_run a b hab input hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none (program a b hab) input
        (result a b input) t _ (by omega)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some S =>
      obtain ⟨t,ht,hh,ho,_⟩ := valid_run a b hab input S hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) none (program a b hab) input
        (result a b input) t _ ht
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho

theorem polytime (a b : Fin 12) (hab : a ≠ b) :
    BitMachine.Polytime (result a b) := by
  refine ⟨machine a b hab, 35, 1, ?_⟩
  intro input
  simpa only [pow_one] using outputs a b hab input

end EthInapproximability.CurrentPaper.RationalProductCellSelect
