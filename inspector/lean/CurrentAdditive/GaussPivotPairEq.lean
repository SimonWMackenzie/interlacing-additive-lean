import EthInapproximability.CurrentPaper.EntryUnaryCompare
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineInline

/-! Parse a Bank2 unary pivot pair and compare its row and column lengths. -/

namespace CurrentAdditive.GaussPivotPairEq

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := BitMachineBankCodec.Stack 2
abbrev Bank := BitMachineBankCodec.Bank 2
abbrev Label := BitMachineBankCodec.ParserLabel 2 ⊕
  (Unit ⊕ EntryUnaryCompare.CL)
abbrev Control := Option Bool × EntryUnaryCompare.CV
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def A : Stack := .inl 0
def B : Stack := .inl 1
def O : Stack := .inr 2

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl
      (fun v => (v, (none, none))) Prod.fst
      (some (.inr (.inl ()))) (BitMachineBankCodec.parser 2 l)
  | .inr (.inl ()) =>
      branch (fun v => v.1.getD false)
        (load (fun _ => (none, (none, none)))
          (goto fun _ => .inr (.inr .loop))) halt
  | .inr (.inr l) => BitMachineInline.stmt
      (fun l => .inr (.inr l)) (fun v => (none, v)) Prod.snd none
      (EntryUnaryCompare.program A B O false true false l)

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) : Config :=
  ⟨l, v, BitMachineBankCodec.contents S source saved output⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add (t u : Nat) (c : Config) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

def pairPacket (r c : Nat) : List Bool :=
  BitMachineBankCodec.encode
    (![List.replicate r true, List.replicate c true] : Bank)

def result (input : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 2 input with
  | none => []
  | some S => [decide ((S 0).length = (S 1).length)]

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack) O
    (.inl (.scan 0) : Label) ((none, (none, none)) : Control) program

theorem parse_run (input : List Bool) (S : Bank)
    (hd : BitMachineBankCodec.decode 2 input = some S) :
    ∃ t ≤ 5 * (input.length + 1),
      run t (cfg (some (.inl (.scan 0))) (none, (none, none))
        (fun _ => []) input [] []) =
      cfg (some (.inr (.inl ()))) (some true, (none, none)) S [] [] [] := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct 2 input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    (Sum.inl : BitMachineBankCodec.ParserLabel 2 → Label)
    (fun v => (v, (none, none))) Prod.fst (fun _ => rfl)
    (some (.inr (.inl ())))
    (BitMachineBankCodec.parser 2) program (fun _ => rfl)
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem dispatch_step (S : Bank) :
    advance program
      (cfg (some (.inr (.inl ()))) (some true, (none, none)) S [] [] []) =
    cfg (some (.inr (.inr .loop))) (none, (none, none)) S [] [] [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem verdict_eq (r c : Nat) :
    EntryUnaryCompare.verdict false true false r c = decide (r = c) := by
  by_cases h : r = c
  · subst c
    simp [EntryUnaryCompare.verdict]
  · by_cases hlt : r < c <;> simp [EntryUnaryCompare.verdict, h, hlt]

theorem compare_run (S : Bank) (r c : Nat)
    (hr : S 0 = List.replicate r true)
    (hc : S 1 = List.replicate c true) :
    ∃ t ≤ max r c + 2,
      let outCfg := run t
        (cfg (some (.inr (.inr .loop))) (none, (none, none)) S [] [] [])
      outCfg.l = none ∧
      outCfg.stk O = [decide (r = c)] := by
  let T := BitMachineBankCodec.contents S [] [] []
  have hA : T A = List.replicate r true := by
    simp [T, A, BitMachineBankCodec.contents, hr]
  have hB : T B = List.replicate c true := by
    simp [T, B, BitMachineBankCodec.contents, hc]
  obtain ⟨t, ht, v, hr⟩ := EntryUnaryCompare.compare_run A B O
    (by decide) (by decide) (by decide)
    false true false T (none, none)
    r c hA hB
  have hh := congrArg (fun c => c.l) hr
  change _ = none at hh
  obtain ⟨u, hu, hlift⟩ := BitMachineInline.outputs
    (fun l => .inr (.inr l) : EntryUnaryCompare.CL → Label)
    (fun v => (none, v)) Prod.snd (fun _ => rfl) none
    (EntryUnaryCompare.program A B O false true false) program (fun _ => rfl)
    (⟨some .loop, (none, none), T⟩ :
      TM2.Cfg (fun _ : Stack => Bool) EntryUnaryCompare.CL EntryUnaryCompare.CV)
    t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run u (cfg (some (.inr (.inr .loop)))
    (none, (none, none)) S [] [] []) = _ at hlift
  rw [hr] at hlift
  change _ ∧ _
  rw [hlift]
  constructor
  · rfl
  · simp [BitMachineInline.cfg, T, BitMachineBankCodec.contents,
      O, verdict_eq]

theorem pair_run (r c : Nat) :
    ∃ t ≤ 5 * ((pairPacket r c).length + 1) + 1 + (max r c + 2),
      let outCfg := run t
        (cfg (some (.inl (.scan 0))) (none, (none, none))
          (fun _ => []) (pairPacket r c) [] [])
      outCfg.l = none ∧ outCfg.stk O = [decide (r = c)] := by
  let S : Bank := ![List.replicate r true, List.replicate c true]
  have hd : BitMachineBankCodec.decode 2 (pairPacket r c) = some S := by
    simp [pairPacket, S, BitMachineBankCodec.decode_encode]
  obtain ⟨a, ha, hparse⟩ := parse_run (pairPacket r c) S hd
  obtain ⟨b, hb, hcompare, hout⟩ := compare_run S r c
    (by simp [S]) (by simp [S])
  refine ⟨a + 1 + b, by omega, ?_⟩
  rw [run_add, run_add, hparse]
  change (run b (advance program
    (cfg (some (.inr (.inl ()))) (some true, (none, none)) S [] [] []))).l =
      none ∧
    (run b (advance program
      (cfg (some (.inr (.inl ()))) (some true, (none, none)) S [] [] []))).stk O =
      [decide (r = c)]
  rw [dispatch_step]
  exact ⟨hcompare, hout⟩

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (.inl (.scan 0) : Label)
      ((none, (none, none)) : Control) input =
    cfg (some (.inl (.scan 0))) (none, (none, none))
      (fun _ => []) input [] [] := by
  unfold rawInit cfg BitMachineBankCodec.contents
  congr 1
  funext i
  cases i with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

theorem result_pairPacket (r c : Nat) :
    result (pairPacket r c) = [decide (r = c)] := by
  simp [result, pairPacket, BitMachineBankCodec.decode_encode]

theorem outputs_pairPacket (r c : Nat) :
    machine.OutputsWithin (pairPacket r c) [decide (r = c)]
      (5 * ((pairPacket r c).length + 1) + 1 + (max r c + 2)) := by
  obtain ⟨t, ht, hh, ho⟩ := pair_run r c
  apply outputsWithin_of_raw_run (.inr 0 : Stack) O
    (.inl (.scan 0) : Label) ((none, (none, none)) : Control)
    program (pairPacket r c) [decide (r = c)] t _ ht
  · rw [initial_cfg]
    exact hh
  · rw [initial_cfg]
    exact ho

#print axioms outputs_pairPacket

end CurrentAdditive.GaussPivotPairEq
