import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineInline
import Mathlib.Tactic

/-! A fixed physical reader for the strict sign of a three-field RawRat bank.
It checks both the sign field and whether the numerator contains a one, so
negative zero is correctly classified as false. -/

namespace CurrentAdditive.RationalStrictNegative

set_option maxRecDepth 4096

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding BitMachineBankCodec

abbrev Bank := BitMachineBankCodec.Bank 3
abbrev Stack := BitMachineBankCodec.Stack 3

inductive Admin where
  | parsed | sign | scan | emit
  deriving DecidableEq, Fintype

abbrev Label := ParserLabel 3 ⊕ Admin

structure Control where
  parserBit : Option Bool
  negative : Bool
  seen : Bool
  deriving DecidableEq, Fintype

def embed (v : Option Bool) : Control := ⟨v, false, false⟩
def read (v : Control) : Option Bool := v.parserBit

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl embed read (some (.inr .parsed))
      (parser 3 l)
  | .inr .parsed => branch (fun v => v.parserBit.getD false)
      (goto (fun _ => .inr .sign)) halt
  | .inr .sign => pop (.inl 0)
      (fun v b => {v with parserBit := b, negative := b.getD false})
      (goto (fun _ => .inr .scan))
  | .inr .scan => pop (.inl 1)
      (fun v b => {v with parserBit := b, seen := v.seen || b.getD false})
      (branch (fun v => v.parserBit.isSome)
        (goto (fun _ => .inr .scan)) (goto (fun _ => .inr .emit)))
  | .inr .emit => branch (fun v => v.negative && v.seen)
      (push (.inr 2) (fun _ => true) halt) halt

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨l,v,contents S source saved output⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem run_add (t u : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

theorem run_succ (t : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem parse_run (input : List Bool) (S : Bank)
    (hd : decode 3 input = some S) :
    ∃ t ≤ 7*(input.length+1),
      run t (cfg (some (.inl (.scan 0))) (embed none)
        (fun _ => []) input [] []) =
      cfg (some (.inr .parsed)) (embed (some true)) S [] [] [] := by
  obtain ⟨t,ht,hp⟩ := parser_correct 3 input []
  rw [hd] at hp
  change parserRun t (parserCfg (some (.scan 0)) none
    (fun _ => []) input [] []) =
      parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : ParserLabel 3 → Label) embed read
    (by intro v; rfl) (some (.inr .parsed))
    (parser 3) program (fun _ => rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold parserRun at hp
  rw [hp] at hr
  simpa [run, cfg, BitMachineInline.cfg, embed] using hr

theorem reject_run (input : List Bool)
    (hd : decode 3 input = none) :
    ∃ t ≤ 7*(input.length+1)+1,
      let c := run t (cfg (some (.inl (.scan 0))) (embed none)
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t,ht,hp⟩ := parser_correct 3 input []
  rw [hd] at hp
  change (parserRun t _).l = none ∧
    (parserRun t _).var = some false ∧
    (parserRun t _).stk (.inr 2) = [] at hp
  let c : TM2.Cfg (fun _ : Stack => Bool) (ParserLabel 3) (Option Bool) :=
    parserRun t (parserCfg (some (.scan 0)) none
      (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u,hu,hr⟩ := BitMachineInline.outputs
    (Sum.inl : ParserLabel 3 → Label) embed read
    (by intro v; rfl) (some (.inr .parsed))
    (parser 3) program (fun _ => rfl)
    (parserCfg (some (.scan 0)) none (fun _ => []) input [] []) t hp.1
  refine ⟨u+1, by omega, ?_⟩
  have hr' : run u (cfg (some (.inl (.scan 0))) (embed none)
      (fun _ => []) input [] []) =
      BitMachineInline.cfg Sum.inl embed (some (.inr .parsed)) c := hr
  change _ ∧ _
  rw [run_add u 1, hr']
  simp only [run, Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, program, BitMachineInline.cfg,
    embed, hp.1, hp.2.1, hp.2.2]

theorem parsed_step (S : Bank) :
    advance program (cfg (some (.inr .parsed)) (embed (some true)) S [] [] []) =
    cfg (some (.inr .sign)) (embed (some true)) S [] [] [] := rfl

theorem sign_step (S : Bank) :
    advance program (cfg (some (.inr .sign)) (embed (some true)) S [] [] []) =
    cfg (some (.inr .scan))
      ⟨(S 0).head?, (S 0).headD false, false⟩
      (Function.update S 0 ((S 0).drop 1)) [] [] [] := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, embed]
  constructor
  · constructor <;> rfl
  · funext k
    cases k with
    | inl j => fin_cases j <;> rfl
    | inr j => fin_cases j <;> rfl

def numContents (S : Bank) (word : List Bool) : Bank :=
  Function.update S 1 word

theorem scan_cons (S : Bank) (v : Control) (b : Bool)
    (rest output : List Bool) :
    advance program
      (cfg (some (.inr .scan)) v (numContents S (b::rest)) [] [] output) =
    cfg (some (.inr .scan))
      ⟨some b, v.negative, v.seen || b⟩
      (numContents S rest) [] [] output := by
  have hw : contents (numContents S (b::rest)) [] [] output (.inl 1) =
      b::rest := by simp only [contents, Sum.elim_inl, numContents,
        Function.update_self]
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    hw, List.head?_cons, Option.isSome_some, Bool.cond_true,
    Option.getD_some, List.tail_cons]
  congr 1
  funext k
  cases k with
  | inl j => fin_cases j <;> rfl
  | inr j => fin_cases j <;> rfl

theorem scan_nil (S : Bank) (v : Control) (output : List Bool) :
    advance program
      (cfg (some (.inr .scan)) v (numContents S []) [] [] output) =
    cfg (some (.inr .emit))
      ⟨none, v.negative, v.seen⟩ (numContents S []) [] [] output := by
  have hw : contents (numContents S []) [] [] output (.inl 1) =
      [] := by simp only [contents, Sum.elim_inl, numContents,
        Function.update_self]
  simp only [advance, TM2.step, TM2.stepAux, program, cfg,
    hw, List.head?_nil, Option.isSome_none, Bool.cond_false,
    Option.getD_none, List.tail_nil, Bool.or_false]
  simp only [Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl j => fin_cases j <;> rfl
  | inr j => fin_cases j <;> rfl

theorem scan_run (S : Bank) (v : Control) (word output : List Bool) :
    run (word.length+1)
      (cfg (some (.inr .scan)) v (numContents S word) [] [] output) =
    cfg (some (.inr .emit))
      ⟨none, v.negative, v.seen || word.any id⟩
      (numContents S []) [] [] output := by
  induction word generalizing v with
  | nil => simpa [run] using scan_nil S v output
  | cons b rest ih =>
      rw [List.length_cons,
        show rest.length+1+1 = (rest.length+1)+1 by omega,
        run_succ, scan_cons]
      simpa [Bool.or_assoc] using
        ih ⟨some b, v.negative, v.seen || b⟩

theorem emit_step (S : Bank) (neg seen : Bool) :
    advance program
      (cfg (some (.inr .emit)) ⟨none,neg,seen⟩ S [] [] []) =
    cfg none ⟨none,neg,seen⟩ S [] []
      (if neg && seen then [true] else []) := by
  cases neg <;> cases seen <;>
    simp [advance, TM2.step, TM2.stepAux, program, cfg]
  all_goals
    funext k
    cases k with
    | inl j => fin_cases j <;> rfl
    | inr j => fin_cases j <;> rfl

def result (input : List Bool) : List Bool :=
  match decode 3 input with
  | none => []
  | some S => if (S 0).headD false && (S 1).any id then [true] else []

@[simp] theorem result_encode (S : Bank) :
    result (encode S) =
      if (S 0).headD false && (S 1).any id then [true] else [] := by
  simp [result]

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack) (.inr 2) (.inl (.scan 0)) (embed none) program

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label) (embed none) input =
      cfg (some (.inl (.scan 0))) (embed none) (fun _ => []) input [] [] := by
  unfold rawInit cfg contents
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => fin_cases k <;> rfl

theorem valid_run (input : List Bool) (S : Bank)
    (hd : decode 3 input = some S) :
    ∃ t ≤ 8*(input.length+1)+3,
      let c := run t (cfg (some (.inl (.scan 0))) (embed none)
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = result input := by
  obtain ⟨t,ht,hp⟩ := parse_run input S hd
  refine ⟨t+1+1+((S 1).length+1)+1, ?_, ?_⟩
  · have hw := decoded_word_length hd (1 : Fin 3)
    omega
  · change _ ∧ _
    rw [run_add (t+1+1+((S 1).length+1)) 1,
      run_add (t+1+1) ((S 1).length+1),
      run_add (t+1) 1, run_add t 1, hp]
    rw [show run 1 (cfg (some (.inr .parsed))
      (embed (some true)) S [] [] []) =
      advance program (cfg (some (.inr .parsed))
        (embed (some true)) S [] [] []) from rfl,
      parsed_step]
    rw [show run 1 (cfg (some (.inr .sign))
      (embed (some true)) S [] [] []) =
      advance program (cfg (some (.inr .sign))
        (embed (some true)) S [] [] []) from rfl,
      sign_step]
    have hs := scan_run (Function.update S 0 ((S 0).drop 1))
      ⟨(S 0).head?, (S 0).headD false, false⟩ (S 1) []
    have hnum : numContents (Function.update S 0 ((S 0).drop 1)) (S 1) =
        Function.update S 0 ((S 0).drop 1) := by
      funext j
      fin_cases j <;> rfl
    rw [hnum] at hs
    rw [hs]
    simp only [Bool.false_or]
    simp only [run, Function.iterate_one]
    rw [emit_step]
    simp [result, hd, cfg, contents]

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (8*(input.length+1)+3) := by
  cases hd : decode 3 input with
  | none =>
      obtain ⟨t,ht,hh,ho⟩ := reject_run input hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) (embed none) program input
        (result input) t _ (by omega)
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run, result, hd] using ho
  | some S =>
      obtain ⟨t,ht,hh,ho⟩ := valid_run input S hd
      apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
        (.inl (.scan 0)) (embed none) program input
        (result input) t _ ht
      · simpa only [initial_cfg, run] using hh
      · simpa only [initial_cfg, run] using ho

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 11, 1, ?_⟩
  intro input
  apply BitMachine.outputsWithin_mono machine (outputs input)
  simp only [pow_one]
  omega

#print axioms outputs
#print axioms polytime

end CurrentAdditive.RationalStrictNegative
